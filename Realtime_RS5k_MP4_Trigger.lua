--[[
Real-time RS5K → MP4 Video Sampler (v5.2 - Native Source Flip & Zero Audio)
Author: Reaper DAW Ultimate Assistant
Version: 5.2 (Native Chunk Flipping, -144dB Audio, Perfect VJ History)
]]

--------------------------------------------------
-- 🔧 CONFIG
--------------------------------------------------
local MIDI_DEVICE_ID = 0 
local DEBUG = false 
local QUANTIZE_VIDEO_TO_GRID = true -- 動画配置位置を自動でグリッドに吸着させる
local SPAWN_VIDEO_ONLY_ON_RECORD = true -- REAPERが「録音中」の時のみ動画を配置する
local FREEZE_LAST_FRAME = true -- 最後のフレームをフリーズさせて画面に残す
local ONE_SHOT_MODE = true -- 【NEW】MIDI入力の長さに関わらず動画を最後まで流し切る（ワンショット動作）
local FREEZE_PLAYRATE = 0.005 -- フリーズ機能が発動した際のスロー再生倍率
local FREEZE_DURATION = 30 -- フリーズ（残像）が持続する最大秒数
local TOGGLE_HORIZONTAL_FLIP = true -- 【NEW】MIDI入力ごとに各トラックの映像を左右反転させる（ダイナミックVJ効果）
local VIDEO_AUDIO_VOLUME_DB = -144.0 -- 動画本来の音声ボリューム（dB単位で指定。無音は -144.0 等）
local VIDEO_AUDIO_VOLUME = 10 ^ (VIDEO_AUDIO_VOLUME_DB / 20) -- 【内部用】（リニア値への自動変換）

-- RS5K Parameter Indexes
local NOTE_START_PARAM_IDX = 3 
local NOTE_END_PARAM_IDX   = 4 
local START_OFFSET_PARAM_IDX = 13 
local LENGTH_PARAM_IDX = 14 

--------------------------------------------------
-- 🧩 Internal Caches
--------------------------------------------------
local note_to_item = {}     -- [note] = { item, start_time, path }
local note_to_tail = {}     -- [note] = tail_item
local note_to_flip_state = {} -- [note] = boolean (現在の反転状態を記憶)
local last_processed_event_seq = 0
local g_is_first_run = true

local g_all_rs5k_cache = {}
local g_last_state_hash = ""

--------------------------------------------------
-- 🧠 Utility Functions
--------------------------------------------------
local function msg(text)
  if DEBUG then reaper.ShowConsoleMsg(tostring(text).."\n") end
end

local B64 = { _ = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/", d = {} }
for i = 1, #B64._ do B64.d[B64._:sub(i, i)] = i - 1 end

local function base64_decode(str)
    str = str:gsub("[^"..B64._.."=]", "")
    local mod = #str % 4
    if mod == 2 then str = str .. "==" end
    if mod == 3 then str = str .. "=" end
    local bytes = {}
    for i = 1, #str, 4 do
        local b1 = B64.d[str:sub(i, i)]
        local b2 = B64.d[str:sub(i+1, i+1)]
        local b3 = B64.d[str:sub(i+2, i+2)]
        local b4 = B64.d[str:sub(i+3, i+3)]
        if b1 then bytes[#bytes+1] = string.char(b1*4 + math.floor(b2/16)) end
        if b2 and str:sub(i+2, i+2) ~= "=" then bytes[#bytes+1] = string.char((b2%16)*16 + math.floor(b3/4)) end
        if b3 and str:sub(i+3, i+3) ~= "=" then bytes[#bytes+1] = string.char((b3%4)*64 + b4) end
    end
    return table.concat(bytes)
end

local function get_or_create_child_track(parent_name, child_name)
  local parent_tr = nil
  local parent_idx = -1
  
  -- 1. 親トラック（RS5K_Video_Output）の探索・作成
  for i = 0, reaper.CountTracks(0)-1 do
    local tr = reaper.GetTrack(0, i)
    local _, name = reaper.GetTrackName(tr, "")
    if name == parent_name then
      parent_tr = tr
      parent_idx = i
      break
    end
  end
  
  if not parent_tr then
    reaper.InsertTrackAtIndex(reaper.CountTracks(0), true)
    parent_idx = reaper.CountTracks(0) - 1
    parent_tr = reaper.GetTrack(0, parent_idx)
    reaper.GetSetMediaTrackInfo_String(parent_tr, "P_NAME", parent_name, true)
    reaper.SetMediaTrackInfo_Value(parent_tr, "I_FOLDERDEPTH", 0) 
  end
  
  -- 2. 子トラック（音程別トラック）が既に存在するか確認
  for i = 0, reaper.CountTracks(0)-1 do
    local tr = reaper.GetTrack(0, i)
    local _, name = reaper.GetTrackName(tr, "")
    if name == child_name then 
      return tr 
    end
  end
  
  -- 3. 親トラックの直下に新しい子トラックを作成
  local insert_idx = parent_idx + 1
  reaper.InsertTrackAtIndex(insert_idx, true)
  local child_tr = reaper.GetTrack(0, insert_idx)
  reaper.GetSetMediaTrackInfo_String(child_tr, "P_NAME", child_name, true)
  reaper.SetMediaTrackInfo_Value(child_tr, "I_RECMON", 0)
  reaper.SetMediaTrackInfo_Value(child_tr, "I_RECARM", 0)
  
  -- 4. REAPERのフォルダ構造（Folder Depth）を更新
  local current_parent_depth = reaper.GetMediaTrackInfo_Value(parent_tr, "I_FOLDERDEPTH")
  
  if current_parent_depth == 0 then
    reaper.SetMediaTrackInfo_Value(parent_tr, "I_FOLDERDEPTH", 1)
    reaper.SetMediaTrackInfo_Value(child_tr, "I_FOLDERDEPTH", -1)
  else
    reaper.SetMediaTrackInfo_Value(child_tr, "I_FOLDERDEPTH", 0)
  end
  
  reaper.TrackList_AdjustWindows(false)
  return child_tr
end

-- === アイテム自体のソースプロパティ(FLIP)を直接書き換える関数 ===
local function apply_item_flip(item, is_flipped)
  if not item or not reaper.ValidatePtr2(0, item, "MediaItem*") then return end
  
  local retval, chunk = reaper.GetItemStateChunk(item, "", false)
  if retval then
      if chunk:match("<SOURCE VIDEO") or chunk:match("<SOURCE PICT") then
          -- 既存の FLIP 設定を一旦すべて削除（リセット）
          chunk = chunk:gsub("\nFLIP [%d]+ [%d]+", "")
          
          -- 左右反転にする場合は、ソースのすぐ下に FLIP 2 0 を追加
          if is_flipped then
              chunk = chunk:gsub("(<SOURCE VIDEO[^\n]*\n)", "%1FLIP 2 0\n")
              chunk = chunk:gsub("(<SOURCE PICT[^\n]*\n)", "%1FLIP 2 0\n")
          end
          
          reaper.SetItemStateChunk(item, chunk, false)
      end
  end
end

--------------------------------------------------
-- 🔍 FX Container & Note Range Scanning
--------------------------------------------------
local function get_plugin_note_range(track, fx)
  local note_start, note_end = -1, -1
  local found = false
  for p = 0, 10 do
    local ok, pname = reaper.TrackFX_GetParamName(track, fx, p, "")
    if ok and pname then
      pname = pname:lower()
      if pname:find("lowest key") or pname:find("note min") or pname:find("min note") or pname:find("key min") then
         note_start = math.floor(reaper.TrackFX_GetParam(track, fx, p) + 0.5)
         found = true
      elseif pname:find("highest key") or pname:find("note max") or pname:find("max note") or pname:find("key max") then
         note_end = math.floor(reaper.TrackFX_GetParam(track, fx, p) + 0.5)
         found = true
      elseif pname == "note" or pname:find("note in") or pname == "key" then
         local val = math.floor(reaper.TrackFX_GetParam(track, fx, p) + 0.5)
         if note_start == -1 then note_start = val end
         if note_end == -1 then note_end = val end
         found = true
      end
    end
  end
  if found then return note_start, note_end else return -1, -1 end
end

local function collect_rs5k_fx(track, current_fx, rs5k_list, current_filter_start, current_filter_end)
  local retval, name = reaper.TrackFX_GetFXName(track, current_fx, "")
  if not (retval and name) then return current_filter_start, current_filter_end end
  
  local lower_name = name:lower()

  if lower_name:find("midi") or lower_name:find("filter") or lower_name:find("map") or lower_name:find("drum") then
    local fs, fe = get_plugin_note_range(track, current_fx)
    if fs ~= -1 then current_filter_start = fs end
    if fe ~= -1 then current_filter_end = fe end
  end

  if lower_name:find("reasamplomatic5000") or lower_name:find("(rs5k)") then
    table.insert(rs5k_list, {
      fx = current_fx,
      filter_start = current_filter_start,
      filter_end = current_filter_end
    })
  end
  
  local is_container, count_str = reaper.TrackFX_GetNamedConfigParm(track, current_fx, "container_count")
  if is_container then
    local count = tonumber(count_str) or 0
    local container_fs = current_filter_start
    local container_fe = current_filter_end
    for i = 0, count - 1 do
      local ok, child_fx_str = reaper.TrackFX_GetNamedConfigParm(track, current_fx, "container_item." .. tostring(i))
      local child_fx = tonumber(child_fx_str)
      if not (ok and child_fx) then
        local track_count = reaper.TrackFX_GetCount(track)
        child_fx = 0x2000000 + ((i + 1) * (track_count + 1)) + (current_fx + 1)
      end
      container_fs, container_fe = collect_rs5k_fx(track, child_fx, rs5k_list, container_fs, container_fe)
    end
  end
  
  return current_filter_start, current_filter_end
end

--------------------------------------------------
-- 🚀 状態ハッシュ型・完全キャッシュシステム
--------------------------------------------------
local function get_all_rs5k_on_track(track)
  local rs5k_list = {}
  local count = reaper.TrackFX_GetCount(track)
  local fs, fe = -1, -1
  for fx = 0, count - 1 do
    fs, fe = collect_rs5k_fx(track, fx, rs5k_list, fs, fe)
  end
  return rs5k_list
end

local g_first_build_done = false
local g_needs_rebuild = false
local g_cache_rebuild_timer = 0

local function update_project_cache()
  local state_cnt = reaper.GetProjectStateChangeCount(0)
  local hash = tostring(state_cnt)
  
  if hash ~= g_last_state_hash then
     g_last_state_hash = hash
     
     if not g_first_build_done then
         -- 初回のみ即時キャッシュ構築
         g_all_rs5k_cache = {}
         for t = 0, reaper.CountTracks(0) - 1 do
           local track = reaper.GetTrack(0, t)
           g_all_rs5k_cache[track] = get_all_rs5k_on_track(track)
         end
         g_first_build_done = true
         msg("--- ♻️ Track FX cache initialized ---")
     else
         -- 【最重要】Nabla Looper等がアイテム操作をした直後に重いスキャンが走らないよう、1秒間の猶予（Debounce）を持たせる
         g_needs_rebuild = true
         g_cache_rebuild_timer = reaper.time_precise() + 1.0 
     end
  end
  
  -- 1秒が経過して安全なタイミングになったら裏でこっそりスキャンを行う
  if g_needs_rebuild and reaper.time_precise() > g_cache_rebuild_timer then
     g_all_rs5k_cache = {}
     for t = 0, reaper.CountTracks(0) - 1 do
       local track = reaper.GetTrack(0, t)
       g_all_rs5k_cache[track] = get_all_rs5k_on_track(track)
     end
     g_needs_rebuild = false
     msg("--- ♻️ Track FX cache rebuilt ---")
  end
end

--------------------------------------------------
-- 📂 Path & Video API
--------------------------------------------------
local function get_sample_path(track, fx)
  for _, key in ipairs({"FILE", "FILE0", "FILE1"}) do
    local ok, val = reaper.TrackFX_GetNamedConfigParm(track, fx, key)
    if ok and val and val ~= "" and val:lower():find(".mp4") then 
      return val:gsub('\0', ''):gsub('%s+$', '')
    end
  end
  local ok, chunk = reaper.GetTrackStateChunk(track, "", false)
  if ok and chunk then
    local rs5k_block, b64_path_line = chunk:match('<VST "VSTi: ReaSamplOmatic5000 (Cockos)".-\n.-[\r\n](QzpcV.-)[\r\n]') 
    if b64_path_line then
      local path = base64_decode(b64_path_line:match("^%S+")):match("(C:\\.-%.mp4)") 
      if path then return path:gsub('\0', ''):gsub('%s+$', '') end
    end
  end
  return nil
end

local function get_pcm_source(path)
  local clean_path = path:gsub("/", "\\")
  return reaper.PCM_Source_CreateFromFile(clean_path)
end

local function get_rs5k_params(track, fx)
  local _, start_str = reaper.TrackFX_GetFormattedParamValue(track, fx, START_OFFSET_PARAM_IDX, "")
  local _, length_str = reaper.TrackFX_GetFormattedParamValue(track, fx, LENGTH_PARAM_IDX, "")
  local start_offset_norm = tonumber(start_str)
  local length_norm = tonumber(length_str)

  start_offset_norm = math.max(0, math.min(1, start_offset_norm or 0))
  length_norm = math.max(0, math.min(1, length_norm or 1))

  local end_offset_norm = length_norm
  if end_offset_norm <= start_offset_norm then
      start_offset_norm = 0.0
      end_offset_norm = 1.0
  end
  return start_offset_norm, end_offset_norm
end

--------------------------------------------------
-- 🎞️ Video Spawning (Multi-Track)
--------------------------------------------------
local function spawn_video(path, start_norm, end_offset_norm, incoming_note, projPos)
  if SPAWN_VIDEO_ONLY_ON_RECORD and (reaper.GetPlayState() & 4) ~= 4 then return nil, nil end
  if not path or path == "" then return nil, nil end

  local src = get_pcm_source(path)
  if not src then return nil, nil end

  local full_src_length = reaper.GetMediaSourceLength(src)
  if not full_src_length or full_src_length <= 0 then return nil, nil end

  local start_time = start_norm * full_src_length
  local end_time   = end_offset_norm * full_src_length
  local duration   = end_time - start_time
  if duration <= 0 then duration = 0.05 end

  local playrate = 1.0

  local track_name = "RS5K_Video_Note_" .. tostring(incoming_note)
  local video_tr = get_or_create_child_track("RS5K_Video_Output", track_name)
  
  reaper.PreventUIRefresh(1)
  
  local item = reaper.AddMediaItemToTrack(video_tr)
  local take = reaper.AddTakeToMediaItem(item)
  reaper.SetMediaItemTake_Source(take, src)
  reaper.SetMediaItemTakeInfo_Value(take, "D_VOL", VIDEO_AUDIO_VOLUME)

  local play_pos = projPos or reaper.GetPlayPosition()
  if QUANTIZE_VIDEO_TO_GRID then
    play_pos = reaper.SnapToGrid(0, play_pos)
  end
  
  reaper.SetMediaItemInfo_Value(item, "D_POSITION", play_pos)
  reaper.SetMediaItemTakeInfo_Value(take, "D_STARTOFFS", start_time)
  reaper.SetMediaItemTakeInfo_Value(take, "D_PLAYRATE", playrate)
  reaper.SetMediaItemInfo_Value(item, "D_LENGTH", duration / playrate)

  reaper.PreventUIRefresh(-1)
  
  return item, play_pos, video_tr
end

-- 指定アイテムのお尻にくっつくように残像フリーズアイテムを生成する
local function spawn_freeze_tail(original_item, tail_start_time, actual_duration, note, path)
  local track = reaper.GetMediaItem_Track(original_item)
  local take = reaper.GetActiveTake(original_item)
  local start_offs = reaper.GetMediaItemTakeInfo_Value(take, "D_STARTOFFS")
  local playrate = reaper.GetMediaItemTakeInfo_Value(take, "D_PLAYRATE")
  
  -- 映像が真っ暗になるのを防ぐため、終端からほんの少し(0.05秒)前のフレームを抽出
  local freeze_media_time = start_offs + (actual_duration * playrate) - 0.05
  if freeze_media_time < start_offs then freeze_media_time = start_offs end
  
  reaper.PreventUIRefresh(1)
  local tail = reaper.AddMediaItemToTrack(track)
  local tail_take = reaper.AddTakeToMediaItem(tail)
  local new_src = get_pcm_source(path)
  
  if new_src then
    reaper.SetMediaItemTake_Source(tail_take, new_src)
    reaper.SetMediaItemInfo_Value(tail, "D_POSITION", tail_start_time)
    reaper.SetMediaItemInfo_Value(tail, "D_LENGTH", FREEZE_DURATION) -- 設定時間だけフリーズを維持
    reaper.SetMediaItemTakeInfo_Value(tail_take, "D_STARTOFFS", freeze_media_time)
    reaper.SetMediaItemTakeInfo_Value(tail_take, "D_PLAYRATE", FREEZE_PLAYRATE) -- 設定された倍率でスロー再生
    reaper.SetMediaItemTakeInfo_Value(tail_take, "D_VOL", 0)
    note_to_tail[note] = tail
  else
    reaper.DeleteTrackMediaItem(track, tail)
    tail = nil
  end
  reaper.PreventUIRefresh(-1)
  
  return tail
end

--------------------------------------------------
-- 🎹 MIDI Input Handling
--------------------------------------------------
local function handle_note_on(note, projPos)
  if note_to_item[note] and not ONE_SHOT_MODE then
     handle_note_off(note, projPos)
  end

  for track, rs5k_list in pairs(g_all_rs5k_cache) do
    for _, info in ipairs(rs5k_list) do
        local fx = info.fx
        
        local note_start = math.floor(reaper.TrackFX_GetParam(track, fx, NOTE_START_PARAM_IDX, 0, 0) * 127 + 0.5)
        local note_end = math.floor(reaper.TrackFX_GetParam(track, fx, NOTE_END_PARAM_IDX, 0, 0) * 127 + 0.5)
        
        if note_start == 0 and note_end == 127 then
            if info.filter_start ~= -1 then note_start = info.filter_start end
            if info.filter_end ~= -1 then note_end = info.filter_end end
        end
        
        if note >= note_start and note <= note_end then
          local path = get_sample_path(track, fx) 
          if path and path:lower():find(".mp4") then
            local start_norm, end_norm = get_rs5k_params(track, fx)
            local item, snapped_start, video_tr = spawn_video(path, start_norm, end_norm, note, projPos) 
            
            if item then
              -- VJフリップ（ソースチャンクの直接書き換え）処理
              if TOGGLE_HORIZONTAL_FLIP then
                 if note_to_flip_state[note] == nil then
                   note_to_flip_state[note] = false
                 else
                   note_to_flip_state[note] = not note_to_flip_state[note]
                 end
                 apply_item_flip(item, note_to_flip_state[note])
              end

              -- 前回のフリーズ残像が存在する場合はカットする
              if FREEZE_LAST_FRAME and note_to_tail[note] then
                local tail = note_to_tail[note]
                if reaper.ValidatePtr2(0, tail, "MediaItem*") then
                  local tail_pos = reaper.GetMediaItemInfo_Value(tail, "D_POSITION")
                  local new_tail_len = snapped_start - tail_pos
                  if new_tail_len > 0 then
                    reaper.SetMediaItemInfo_Value(tail, "D_LENGTH", new_tail_len)
                  else
                    reaper.DeleteTrackMediaItem(reaper.GetMediaItem_Track(tail), tail)
                  end
                end
                note_to_tail[note] = nil
              end

              if ONE_SHOT_MODE then
                 -- ワンショットモード：動画本来の長さをフルで流し切り、直後にフリーズを予約する
                 if FREEZE_LAST_FRAME then
                    if reaper.ValidatePtr2(0, item, "MediaItem*") then
                        local duration = reaper.GetMediaItemInfo_Value(item, "D_LENGTH")
                    local tail = spawn_freeze_tail(item, snapped_start + duration, duration, note, path)
                    
                    -- フリーズ残像にも反転状態を引き継ぐ
                    if tail and TOGGLE_HORIZONTAL_FLIP and note_to_flip_state[note] then
                        apply_item_flip(tail, note_to_flip_state[note])
                     end
                   end
                 end
              else
                 -- ゲートモード：離すまで流すためにアイテム情報を記録
                 note_to_item[note] = {
                   item = item,
                   start_time = snapped_start,
                   path = path
                 }
              end
            end
          end
        end 
      end 
  end 
end

local function handle_note_off(note, projPos)
  if ONE_SHOT_MODE then return end -- ワンショットモード時はノートオフを完全無視
  
  local info = note_to_item[note]
  if not info then return end
  
  if info.item and reaper.ValidatePtr2(0, info.item, "MediaItem*") then
    local end_pos = projPos or reaper.GetPlayPosition()
    
    local new_duration = end_pos - info.start_time
    local max_duration = reaper.GetMediaItemInfo_Value(info.item, "D_LENGTH")
    
    local is_trimmed = false
    if new_duration > 0 and new_duration < max_duration then
      reaper.SetMediaItemInfo_Value(info.item, "D_LENGTH", new_duration)
      is_trimmed = true
    end  
    
    if FREEZE_LAST_FRAME and info.path then
      local actual_duration = is_trimmed and new_duration or max_duration
      local tail_start_time = info.start_time + actual_duration
      local tail = spawn_freeze_tail(info.item, tail_start_time, actual_duration, note, info.path)
      
      -- フリーズ残像にも反転状態を引き継ぐ
      if tail and TOGGLE_HORIZONTAL_FLIP and note_to_flip_state[note] then
         apply_item_flip(tail, note_to_flip_state[note])
      end
    end
  end 
  
  note_to_item[note] = nil
end

--------------------------------------------------
-- ♻️ Main Deferred Loop (Hardware Polling Only)
--------------------------------------------------
local function main()
  if g_is_first_run then
    local retval = reaper.MIDI_GetRecentInputEvent(0)
    if retval > 0 then last_processed_event_seq = retval end
    msg("Script initialized. Hardware Live MIDI mode active.")
    g_is_first_run = false
    reaper.defer(main)
    return
  end
  
  update_project_cache()

  local events_to_process = {}
  local new_last_seq = 0
  local idx = 0

  while true do
    local retval, msg_str, ts, devIdx, projPos, projLoopCnt = reaper.MIDI_GetRecentInputEvent(idx)
    if retval > 0 and retval > last_processed_event_seq then
      table.insert(events_to_process, {seq = retval, msg = msg_str, projPos = projPos})
      if new_last_seq == 0 then new_last_seq = retval end
      idx = idx + 1
    else break end
  end

  if new_last_seq > 0 then last_processed_event_seq = new_last_seq end

  for i = #events_to_process, 1, -1 do
    local event = events_to_process[i]
    local msg_str = event.msg
    local projPos = event.projPos
    
    if msg_str and #msg_str >= 3 then
      local b1, b2, b3 = string.byte(msg_str, 1, 3)
      local status = b1 & 0xF0

      if status == 0x90 then 
        if b3 > 0 then handle_note_on(b2, projPos) else handle_note_off(b2, projPos) end
      elseif status == 0x80 then 
        handle_note_off(b2, projPos)
      end
    end
  end

  reaper.defer(main)
end

--------------------------------------------------
-- 🚀 Start
--------------------------------------------------
reaper.ShowConsoleMsg("RS5K Video Sampler (v5.2 Native Setup) running...\n")
main()
