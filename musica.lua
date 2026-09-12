--[[
    CC:Tweaked Tape Media Player
    Unified file with search, playlist, queue, progress bar, metadata,
    play/pause, stop=rewind, wipe, next button, and scrollbars.
    Search fix applied (zone detection + tab switching).
    Playlist tab added with controls, history removed.
]]

-----------------------------
-- CONFIG / GLOBAL STATE
-----------------------------

local api_base_url = "https://ipod-2to6magyna-uc.a.run.app/"
local version = "2.1"

local backend_url =
    "https://98yl2vq7zb9w.share.zrok.io/convert?url="

local backend_video_url =
    "https://98yl2vq7zb9w.share.zrok.io/convertVideo?url="

local player_update_url =
    "https://98yl2vq7zb9w.share.zrok.io/musica.lua"

local cache_clear_url =
    "https://98yl2vq7zb9w.share.zrok.io/clear-cache"


local width, height = term.getSize()
local tab = 1 -- 1=Search, 2=Playlist, 3=Queue

-- Search state
local waiting_for_input = false
local last_search = nil
local last_search_url = nil
local search_results = nil
local search_error = false
local search_scroll = 0
local max_scroll = 0

-- Playlist state
local playlist = {}
local playlist_scroll = 0
local playlist_max_scroll = 0

-- Queue state
local tape_queue = {}
local queue_scroll = 0
local queue_max_scroll = 0
local autoplay_next = true

-- Video state
local currentVideo = nil
local playingVideo = false
local audioPosition = 0
local restart_requested = false
local video_fps = 20
local monitor_fps = 20
local last_rendered_frame = nil
local dfpwm_bytes_per_second = 6000

-- Video synchronization
-- Start as soon as the first frame is available; the rolling producer
-- continues filling the buffer while audio and video are already playing.
local VIDEO_PREBUFFER_FRAMES = 1

-- Rolling video buffer
local VIDEO_BUFFER_SECONDS = 8
local video_streaming = false
local video_stream_handle = nil
local video_stream_coroutine = nil

-- Tape drive
local tape = peripheral.find("tape_drive")
local video_monitor = peripheral.find("monitor")

if video_monitor then
    pcall(function() video_monitor.setTextScale(0.5) end)
    video_monitor.setBackgroundColor(colors.black)
    video_monitor.clear()
end

local function getAudioTime()
    if tape then
        return tape.getPosition() / dfpwm_bytes_per_second
    end
    return audioPosition
end

term.clear()
if not tape then
    print("No Tape Drive found!")
    return
else
    pcall(function() tape.getPosition() end)
end

-----------------------------
-- HELPERS
-----------------------------

local function filterPromo(results)
    if not results then return nil end

    local cleaned = {}

    for _, item in ipairs(results) do
        local name = string.lower(item.name or "")
        local artist = string.lower(item.artist or "")

        if not name:find("patreon")
            and not artist:find("patreon") then

            table.insert(cleaned, item)
        end
    end

    return cleaned
end

local function build_download_url(result)
    local video_url = result.url or result.id or ""

    if video_url == "" then
        return nil
    end

    return backend_url .. textutils.urlEncode(video_url)
end

-- HTTP GET compatibility wrapper.
-- Uses the table form so every request has an explicit URL and binary mode.
local function safeHttpGet(url, binary)
    if type(url) ~= "string" then
        return nil, "HTTP URL is not a string"
    end

    -- Remove accidental leading/trailing whitespace before validating the URL.
    url = url:match("^%s*(.-)%s*$") or url

    if not url:match("^https?://") then
        return nil, "must specify http or https: " .. tostring(url)
    end

    local ok, response, request_error, error_response =
        pcall(
            http.get,
            {
                url = url,
                headers = {},
                binary = binary == true
            }
        )

    if not ok then
        return nil, tostring(response)
    end

    return response, request_error, error_response
end

local function fetchNFV(url)
    local h = safeHttpGet(url, false)

    if not h then
        return nil, "HTTP failed"
    end

    local data = h.readAll()
    h.close()

    return data
end

local renderCurrentVideoFrame

-----------------------------
-- ROLLING VIDEO BUFFER
-----------------------------

local function getBufferedFrame(video, frame_number)
    if not video then
        return nil
    end

    if frame_number < video.first_frame then
        return nil
    end

    if frame_number > video.last_frame then
        return nil
    end

    local index =
        ((frame_number - 1) % video.buffer_size) + 1

    return video.frames[index]
end

local function stopVideoStream()
    video_streaming = false

    if video_stream_handle then
        pcall(function()
            video_stream_handle.close()
        end)

        video_stream_handle = nil
    end

    video_stream_coroutine = nil
end

local function clearPlayedCache()
    local response = safeHttpGet(
        cache_clear_url,
        true
    )

    if response then
        response.close()
    end
end

local function streamNFV(url)
    stopVideoStream()

    local handle = safeHttpGet(url, false)

    if not handle then
        return nil, "HTTP failed"
    end

    local header = handle.readLine()

    if not header then
        handle.close()
        return nil, "Empty NFV response"
    end

    local stream_width,
          stream_height,
          stream_fps =
                header:match("(%d+)%s+(%d+)%s+([%d%.]+)")

    stream_width = tonumber(stream_width)
    stream_height = tonumber(stream_height)
    stream_fps = tonumber(stream_fps)

    if not stream_width
        or not stream_height
        or not stream_fps then

        handle.close()
        return nil, "Invalid NFV header"
    end

    local buffer_size =
        math.max(
            60,
            math.floor(
                stream_fps * VIDEO_BUFFER_SECONDS
            )
        )

    currentVideo = {
        width = stream_width,
        height = stream_height,
        fps = stream_fps,

        frames = {},

        buffer_size = buffer_size,

        first_frame = 1,
        last_frame = 0,

        received_frames = 0,

        finished = false,
        stream_error = nil
    }

    last_rendered_frame = nil

    video_stream_handle = handle
    video_streaming = true

    video_stream_coroutine = coroutine.create(function()

        local video = currentVideo

        while video
            and video_streaming
            and currentVideo == video do

            local frame = handle.readLine()

            if not frame then
                break
            end

            video.received_frames =
                video.received_frames + 1

            local frame_number =
                video.received_frames

            local index =
                ((frame_number - 1)
                % video.buffer_size) + 1

            video.frames[index] = frame

            video.last_frame = frame_number

            if video.last_frame -
               video.first_frame + 1
               > video.buffer_size then

                video.first_frame =
                    video.last_frame
                    - video.buffer_size
                    + 1
            end

            coroutine.yield()
        end

        pcall(function()
            handle.close()
        end)

        if video_stream_handle == handle then
            video_stream_handle = nil
        end

        video_streaming = false
        video.finished = true
    end)

    return currentVideo
end

local function videoStreamLoop()
    while true do

        if video_stream_coroutine then

            if coroutine.status(video_stream_coroutine) == "dead" then
                video_stream_coroutine = nil

            else
                local ok, err =
                    coroutine.resume(video_stream_coroutine)

                if not ok then

                    if currentVideo then
                        currentVideo.stream_error =
                            tostring(err)

                        currentVideo.finished = true
                    end

                    video_streaming = false

                    if video_stream_handle then
                        pcall(function()
                            video_stream_handle.close()
                        end)

                        video_stream_handle = nil
                    end

                    video_stream_coroutine = nil
                end
            end
        end

        sleep(0)
    end
end

-----------------------------
-- VIDEO PREBUFFER
-----------------------------

local function waitForVideoPrebuffer(video)
    if not video then
        return false
    end

    local start_time = os.epoch("utc")
    local timeout_ms = 5000

    while true do

        if currentVideo ~= video then
            return false
        end

        if video.received_frames >= VIDEO_PREBUFFER_FRAMES then
            return true
        end

        if video.finished then
            return video.received_frames > 0
        end

        local now = os.epoch("utc")

        if now - start_time >= timeout_ms then
            return video.received_frames > 0
        end

        sleep(0.01)
    end
end

-----------------------------
-- PLAYER UPDATE
-----------------------------

local function clearBackendCache()
    local cache_response, cache_error =
        safeHttpGet(
            cache_clear_url,
            true
        )

    if not cache_response then
        return false,
            cache_error or "Cache deletion request failed"
    end

    local cache_message = cache_response.readAll() or ""
    cache_response.close()

    if not cache_message:match("^Cache deleted:") then
        return false,
            cache_message ~= ""
            and cache_message
            or "Cache deletion failed"
    end

    return true, cache_message
end

local function downloadLatestPlayer()
    local update_url =
        player_update_url
        .. "?t="
        .. os.epoch("utc")

    local response, request_error =
        safeHttpGet(
            update_url,
            true
        )

    if not response then
        return false,
            request_error or "HTTP request failed"
    end

    local code = response.readAll()
    response.close()

    if type(code) ~= "string"
        or code == "" then

        return false, "Empty response"
    end

    local file =
        fs.open("musica.lua.new", "w")

    if not file then
        return false,
            "Cannot open musica.lua.new"
    end

    file.write(code)
    file.close()

    local cache_cleared, cache_message =
        clearBackendCache()

    if not cache_cleared then
        fs.delete("musica.lua.new")
        return false, cache_message
    end

    return true, cache_message
end

local function replacePlayerFile()
    if fs.exists("musica.lua") then
        fs.delete("musica.lua")
    end

    fs.move(
        "musica.lua.new",
        "musica.lua"
    )
end

local function parseNFV(raw)
    local lines = {}

    for line in raw:gmatch("[^\r\n]+") do
        table.insert(lines, line)
    end

    local header = lines[1]

    if not header then
        return nil
    end

    local w, h, fps =
        header:match("(%d+)%s+(%d+)%s+(%d+)")

    w = tonumber(w)
    h = tonumber(h)
    fps = tonumber(fps)

    if not w
        or not h
        or not fps
        or #lines < 2 then

        return nil
    end

    local frames = {}

    for i = 2, #lines do
        frames[i - 1] = lines[i]
    end

    return {
        width = w,
        height = h,
        fps = fps,
        frames = frames
    }
end

local function drawNFVFrame(
    target,
    frame,
    previous_frame,
    w,
    h,
    x,
    y
)
    local text =
        string.rep(" ", w)

    local foreground =
        string.rep("0", w)

    for row = 1, h do

        local background =
            frame[row]

        local previous_background =
            previous_frame
            and previous_frame[row]

        if background ~= previous_background then

            target.setCursorPos(
                x,
                y + row - 1
            )

            target.blit(
                text,
                foreground,
                background
            )
        end
    end
end

renderCurrentVideoFrame = function()

    if not video_monitor
        or not currentVideo then

        return false
    end

    local video = currentVideo

    local audio_time =
        getAudioTime()

    local target_frame =
        math.floor(
            audio_time * video.fps
        ) + 1

    if target_frame < 1 then
        target_frame = 1
    end

    if video.last_frame <
       video.first_frame then

        return false
    end

    if target_frame >
       video.last_frame then

        target_frame =
            video.last_frame
    end

    if target_frame <
       video.first_frame then

        target_frame =
            video.first_frame
    end

    local frame =
        getBufferedFrame(
            video,
            target_frame
        )

    if not frame then
        return false
    end

    if frame ==
       last_rendered_frame then

        return true
    end

    local rows = {}

    for row = 1, video.height do

        local row_start =
            (row - 1)
            * video.width
            + 1

        rows[row] =
            frame:sub(
                row_start,
                row_start
                + video.width
                - 1
            )
    end

    local monitor_width,
          monitor_height =
        video_monitor.getSize()

    local x =
        math.max(
            1,
            math.floor(
                (monitor_width
                - video.width) / 2
            ) + 1
        )

    local y =
        math.max(
            1,
            math.floor(
                (monitor_height
                - video.height) / 2
            ) + 1
        )

    drawNFVFrame(
        video_monitor,
        rows,
        nil,
        video.width,
        video.height,
        x,
        y
    )

    last_rendered_frame =
        frame

    return true
end

-----------------------------
-- SCROLLBARS / PROGRESS / METADATA
-----------------------------

local function drawScrollbarSearch()

    if not search_results then
        return
    end

    local list_height =
        #search_results * 2

    local view_height =
        height - 8

    if list_height <= view_height then
        return
    end

    local bar_x = width - 1
    local bar_y_top = 8
    local bar_y_bottom = height

    local track_height =
        bar_y_bottom
        - bar_y_top
        + 1

    local thumb_height =
        math.max(
            1,
            math.floor(
                track_height
                * (view_height / list_height)
            )
        )

    local max_thumb_offset =
        track_height - thumb_height

    local thumb_offset =
        math.floor(
            (search_scroll / max_scroll)
            * max_thumb_offset
        )

    for y = bar_y_top, bar_y_bottom do

        term.setCursorPos(
            bar_x,
            y
        )

        term.setBackgroundColor(
            colors.gray
        )

        term.write(" ")
    end

    for y =
        bar_y_top + thumb_offset,
        bar_y_top + thumb_offset
        + thumb_height - 1 do

        term.setCursorPos(
            bar_x,
            y
        )

        term.setBackgroundColor(
            colors.white
        )

        term.write(" ")
    end

    term.setBackgroundColor(
        colors.black
    )
end

local function drawScrollbarPlaylist()

    if #playlist == 0 then
        return
    end

    local list_height =
        #playlist * 2

    local view_height =
        height - 4

    if list_height <= view_height then
        return
    end

    local bar_x = width - 1
    local bar_y_top = 4
    local bar_y_bottom = height

    local track_height =
        bar_y_bottom
        - bar_y_top
        + 1

    local thumb_height =
        math.max(
            1,
            math.floor(
                track_height
                * (view_height / list_height)
            )
        )

    local max_thumb_offset =
        track_height - thumb_height

    local thumb_offset =
        math.floor(
            (playlist_scroll
            / playlist_max_scroll)
            * max_thumb_offset
        )

    for y = bar_y_top, bar_y_bottom do

        term.setCursorPos(
            bar_x,
            y
        )

        term.setBackgroundColor(
            colors.gray
        )

        term.write(" ")
    end

    for y =
        bar_y_top + thumb_offset,
        bar_y_top + thumb_offset
        + thumb_height - 1 do

        term.setCursorPos(
            bar_x,
            y
        )

        term.setBackgroundColor(
            colors.white
        )

        term.write(" ")
    end

    term.setBackgroundColor(
        colors.black
    )
end

local function drawScrollbarQueue()

    if #tape_queue == 0 then
        return
    end

    local list_height =
        #tape_queue * 2

    local view_height =
        height - 4

    if list_height <= view_height then
        return
    end

    local bar_x = width - 1
    local bar_y_top = 4
    local bar_y_bottom = height

    local track_height =
        bar_y_bottom
        - bar_y_top
        + 1

    local thumb_height =
        math.max(
            1,
            math.floor(
                track_height
                * (view_height / list_height)
            )
        )

    local max_thumb_offset =
        track_height - thumb_height

    local thumb_offset =
        math.floor(
            (queue_scroll
            / queue_max_scroll)
            * max_thumb_offset
        )

    for y = bar_y_top, bar_y_bottom do

        term.setCursorPos(
            bar_x,
            y
        )

        term.setBackgroundColor(
            colors.gray
        )

        term.write(" ")
    end

    for y =
        bar_y_top + thumb_offset,
        bar_y_top + thumb_offset
        + thumb_height - 1 do

        term.setCursorPos(
            bar_x,
            y
        )

        term.setBackgroundColor(
            colors.white
        )

        term.write(" ")
    end

    term.setBackgroundColor(
        colors.black
    )
end

local function drawTapeProgress()

    if not tape then
        return
    end

    local size =
        tape.getSize()

    if size <= 0 then
        return
    end

    local pos =
        tape.getPosition()

    if pos < 0 then
        pos = 0
    end

    if pos > size then
        pos = size
    end

    local bar_x = 2
    local bar_y = 6
    local bar_w = width - 3

    local pct =
        pos / size

    local filled =
        math.floor(
            bar_w * pct
        )

    term.setCursorPos(
        bar_x,
        bar_y
    )

    term.setBackgroundColor(
        colors.gray
    )

    term.write(
        string.rep(
            " ",
            bar_w
        )
    )

    term.setCursorPos(
        bar_x,
        bar_y
    )

    term.setBackgroundColor(
        colors.green
    )

    term.write(
        string.rep(
            " ",
            filled
        )
    )

    term.setBackgroundColor(
        colors.black
    )
end

local function drawMetadataPanel()

    if not tape then
        return
    end

    local label =
        tape.getLabel()
        or "No Label"

    local pos =
        tape.getPosition()

    local size =
        tape.getSize()

    term.setCursorPos(
        2,
        7
    )

    term.setBackgroundColor(
        colors.black
    )

    term.setTextColor(
        colors.lightGray
    )

    term.clearLine()

    local pct = 0

    if size > 0 then
        pct =
            math.floor(
                (pos / size)
                * 100
            )
    end

    term.write(
        label
        .. "  |  "
        .. pct
        .. "%"
    )
end

-----------------------------
-- DRAW SCREENS
-----------------------------

local function drawSearch()

    paintutils.drawFilledBox(
        2,
        3,
        width - 1,
        5,
        colors.lightGray
    )

    term.setBackgroundColor(
        colors.lightGray
    )

    term.setCursorPos(
        3,
        4
    )

    term.setTextColor(
        colors.black
    )

    term.write(
        last_search
        or "Search..."
    )

    drawTapeProgress()
    drawMetadataPanel()

    if search_results then

        term.setBackgroundColor(
            colors.black
        )

        max_scroll =
            math.max(
                0,
                (#search_results * 2)
                - (height - 8)
            )

        for i = 1, #search_results do

            local y_name =
                8
                + (i - 1) * 2
                - search_scroll

            local y_artist =
                9
                + (i - 1) * 2
                - search_scroll

            if y_name >= 8
                and y_name <= height then

                term.setTextColor(
                    colors.white
                )

                term.setCursorPos(
                    2,
                    y_name
                )

                local name =
                    search_results[i].name
                    or "Unknown"

                local max_name_width =
                    width - 4

                if #name >
                   max_name_width then

                    name =
                        name:sub(
                            1,
                            max_name_width
                        )
                end

                term.write(name)

                term.setCursorPos(
                    width - 2,
                    y_name
                )

                term.setTextColor(
                    colors.green
                )

                term.write("+")
            end

            if y_artist >= 8
                and y_artist <= height then

                term.setTextColor(
                    colors.lightGray
                )

                term.setCursorPos(
                    2,
                    y_artist
                )

                local artist =
                    search_results[i].artist
                    or ""

                local max_artist_width =
                    width - 4

                if #artist >
                   max_artist_width then

                    artist =
                        artist:sub(
                            1,
                            max_artist_width
                        )
                end

                term.write(artist)
            end
        end

        drawScrollbarSearch()

    else

        term.setBackgroundColor(
            colors.black
        )

        term.setCursorPos(
            2,
            8
        )

        if search_error then

            term.setTextColor(
                colors.red
            )

            term.write(
                "Network error"
            )

        elseif last_search_url then

            term.setTextColor(
                colors.lightGray
            )

            term.write(
                "Searching..."
            )

        else

            term.setCursorPos(
                1,
                8
            )

            term.setTextColor(
                colors.lightGray
            )

            print(
                "Tip: Paste YouTube links."
            )
        end
    end
end

local function drawPlaylist()

    term.setBackgroundColor(
        colors.black
    )

    term.setTextColor(
        colors.white
    )

    term.setCursorPos(
        2,
        3
    )

    term.write(
        "Playlist (? ? ?)"
    )

    if #playlist == 0 then

        term.setCursorPos(
            2,
            5
        )

        term.setTextColor(
            colors.lightGray
        )

        term.write(
            "No tracks in playlist."
        )

        return
    end

    playlist_max_scroll =
        math.max(
            0,
            (#playlist * 2)
            - (height - 4)
        )

    for i = 1, #playlist do

        local y_name =
            4
            + (i - 1) * 2
            - playlist_scroll

        local y_controls =
            5
            + (i - 1) * 2
            - playlist_scroll

        if y_name >= 4
            and y_name <= height then

            term.setCursorPos(
                2,
                y_name
            )

            term.setTextColor(
                colors.white
            )

            term.write(
                playlist[i].name
                or "Unknown"
            )
        end

        if y_controls >= 4
            and y_controls <= height then

            term.setCursorPos(
                2,
                y_controls
            )

            term.setTextColor(
                colors.green
            )

            term.write("? ")

            term.setTextColor(
                colors.cyan
            )

            term.write("? ")

            term.setTextColor(
                colors.red
            )

            term.write("?")
        end
    end

    drawScrollbarPlaylist()
end

local function drawQueue()

    term.setBackgroundColor(
        colors.black
    )

    term.setTextColor(
        colors.white
    )

    term.setCursorPos(
        2,
        3
    )

    term.write(
        "Queue (? ? ?)  Autoplay: "
        .. (autoplay_next
            and "ON"
            or "OFF")
    )

    if #tape_queue == 0 then

        term.setCursorPos(
            2,
            5
        )

        term.setTextColor(
            colors.lightGray
        )

        term.write(
            "No tracks queued."
        )

        return
    end

    queue_max_scroll =
        math.max(
            0,
            (#tape_queue * 2)
            - (height - 4)
        )

    for i = 1, #tape_queue do

        local y_name =
            4
            + (i - 1) * 2
            - queue_scroll

        local y_controls =
            5
            + (i - 1) * 2
            - queue_scroll

        if y_name >= 4
            and y_name <= height then

            term.setCursorPos(
                2,
                y_name
            )

            term.setTextColor(
                colors.white
            )

            term.write(
                tape_queue[i].name
                or "Unknown"
            )
        end

        if y_controls >= 4
            and y_controls <= height then

            term.setCursorPos(
                2,
                y_controls
            )

            term.setTextColor(
                colors.green
            )

            term.write("? ")

            term.setTextColor(
                colors.cyan
            )

            term.write("? ")

            term.setTextColor(
                colors.red
            )

            term.write("?")
        end
    end

    drawScrollbarQueue()
end

-----------------------------
-- TAPE OPERATIONS
-----------------------------

local function write_url_to_tape(url)

    term.setBackgroundColor(
        colors.black
    )

    term.setTextColor(
        colors.white
    )

    term.setCursorPos(
        2,
        10
    )

    term.clearLine()

    term.write(
        "Downloading DFPWM..."
    )

    local response =
        safeHttpGet(
            url,
            true
        )

    if not response then

        term.setCursorPos(
            2,
            11
        )

        term.setTextColor(
            colors.red
        )

        term.write(
            "Download failed."
        )

        sleep(1)

        return
    end

    tape.seek(
        -999999999999
    )

    tape.write(
        response.readAll()
    )

    response.close()

    tape.seek(
        -999999999999
    )

    term.setCursorPos(
        2,
        12
    )

    term.setTextColor(
        colors.white
    )

    term.write(
        "Tape name:"
    )

    term.setCursorPos(
        2,
        13
    )

    term.setTextColor(
        colors.lightGray
    )

    term.write(
        "Name: "
    )

    local name =
        read()

    tape.setLabel(
        name
    )

    term.setCursorPos(
        2,
        15
    )

    term.setTextColor(
        colors.green
    )

    term.write(
        "Done!"
    )

    sleep(1.5)
end

local function autoplayNextTrack()

    if not autoplay_next then
        return
    end

    if not tape_queue[1] then
        return
    end

    local result =
        tape_queue[1]

    table.remove(
        tape_queue,
        1
    )

    if result.type == "playlist"
        and result.playlist_items
        and result.playlist_items[1] then

        result =
            result.playlist_items[1]
    end

    local url =
        build_download_url(
            result
        )

    if not url or not tape then
        return
    end

    local response =
        safeHttpGet(
            url,
            true
        )

    if not response then
        return
    end

    tape.seek(
        -9999999999
    )

    tape.write(
        response.readAll()
    )

    response.close()

    tape.seek(
        -9999999999
    )

    tape.setLabel(
        result.name
        or "Unknown"
    )

    tape.play()
end

-----------------------------
-- MAIN REDRAW
-----------------------------

local function redrawScreen()

    if waiting_for_input then
        return
    end

    term.setCursorBlink(
        false
    )
                                                    -- Keep audio stopped when
                                                    -- video cannot start.

    term.setCursorPos(
        width,
        1
    )

    term.setTextColor(
        colors.white
    )

    write("X")

    term.setCursorPos(
        1,
        1
    )

    term.setBackgroundColor(
        colors.gray
    )

    term.clearLine()

    local playLabel =
        " play "

    if tape
        and tape.isPlaying
        and tape.isPlaying() then

        playLabel =
            " pause "
    end

    local tabs = {
        " Search ",
        " Playlist ",
        " Queue ",
        playLabel,
        " stop ",
        " next ",
        " wipe "
    }

    for i = 1, #tabs do

        local bg =
            colors.gray

        local fg =
            colors.white

        if i == 4 then

            if tape
                and tape.isPlaying
                and tape.isPlaying() then

                bg = colors.red
                fg = colors.white

            else

                bg = colors.green
                fg = colors.black
            end

        elseif i == 5 then

            bg = colors.orange
            fg = colors.black

        elseif i == 6 then

            bg = colors.purple
            fg = colors.white

        elseif i == 7 then

            bg = colors.red
            fg = colors.white
        end

        if (i == 1
            or i == 2
            or i == 3)
            and tab == i then

            bg = colors.white
            fg = colors.black
        end

        term.setBackgroundColor(
            bg
        )

        term.setTextColor(
            fg
        )

        local pos =
            (
                math.floor(
                    (width / #tabs)
                    * (i - 0.5)
                )
            )
            - math.ceil(
                #tabs[i] / 2
            )
            + 1

        term.setCursorPos(
            pos,
            1
        )

        term.write(
            tabs[i]
        )
    end

    term.setBackgroundColor(
        colors.black
    )

    term.setTextColor(
        colors.white
    )

    if tab == 1 then

        drawSearch()

    elseif tab == 2 then

        drawPlaylist()

    elseif tab == 3 then

        drawQueue()
    end
end

-----------------------------
-- UI LOOP
-----------------------------

local function uiLoop()

    redrawScreen()

    while true do

        if restart_requested then
            return
        end

        if waiting_for_input then

            parallel.waitForAny(

                function()

                    term.setCursorPos(
                        3,
                        4
                    )

                    term.setBackgroundColor(
                        colors.white
                    )

                    term.setTextColor(
                        colors.black
                    )

                    local input =
                        read()

                    if #input > 0 then

                        last_search =
                            input

                        last_search_url =
                            api_base_url
                            .. "?v="
                            .. version
                            .. "&search="
                            .. textutils.urlEncode(
                                input
                            )

                        http.request(
                            last_search_url
                        )

                        search_results =
                            nil

                        search_error =
                            false

                        search_scroll =
                            0

                    else

                        last_search =
                            nil

                        last_search_url =
                            nil

                        search_results =
                            nil

                        search_error =
                            false
                    end

                    waiting_for_input =
                        false

                    os.queueEvent(
                        "redraw_screen"
                    )
                end,

                function()

                    while waiting_for_input do

                        local event,
                              button,
                              x,
                              y =
                            os.pullEvent(
                                "mouse_click"
                            )

                        if y < 3
                            or y > 5
                            or x < 2
                            or x > width - 1 then

                            waiting_for_input =
                                false

                            os.queueEvent(
                                "redraw_screen"
                            )

                            break
                        end
                    end
                end
            )

        else

            parallel.waitForAny(

                function()

                    local event,
                          p1,
                          x,
                          y =
                        os.pullEvent()

                    local update_key =
                        event == "key"
                        and p1 == keys.u

                    local update_char =
                        event == "char"
                        and string.lower(
                            p1 or ""
                        ) == "u"

                    if update_key
                        or update_char then

                        local updated,
                            update_message =
                            downloadLatestPlayer()

                        term.setCursorPos(
                            2,
                            2
                        )

                        term.setTextColor(
                            updated
                            and colors.green
                            or colors.red
                        )

                        term.write(
                            updated
                            and update_message
                            or "Update failed: "
                            .. update_message
                        )

                        sleep(1.5)

                        if updated then

                            if tape then
                                tape.stop()
                            end

                            stopVideoStream()

                            playingVideo =
                                false

                            currentVideo =
                                nil

                            audioPosition =
                                0

                            replacePlayerFile()

                            restart_requested =
                                true

                            return
                        end

                        redrawScreen()
                        return
                    end

                    if tape
                        and tape.isPlaying
                        and tape.isPlaying() then

                        local size =
                            tape.getSize()

                        local pos =
                            tape.getPosition()

                        if pos >= size - 1 then

                            tape.stop()

                            stopVideoStream()

                            clearPlayedCache()

                            playingVideo =
                                false

                            currentVideo =
                                nil

                            audioPosition =
                                0

                            autoplayNextTrack()
                        end

                        redrawScreen()
                    end

                    -- SCROLL HANDLING

                    if event == "mouse_scroll" then

                        if tab == 1
                            and search_results then

                            search_scroll =
                                search_scroll
                                + (p1 * 2)

                            if search_scroll < 0 then
                                search_scroll = 0
                            end

                            if search_scroll >
                               max_scroll then

                                search_scroll =
                                    max_scroll
                            end

                            redrawScreen()

                        elseif tab == 2
                            and #playlist > 0 then

                            playlist_scroll =
                                playlist_scroll
                                + (p1 * 2)

                            if playlist_scroll < 0 then
                                playlist_scroll = 0
                            end

                            if playlist_scroll >
                               playlist_max_scroll then

                                playlist_scroll =
                                    playlist_max_scroll
                            end

                            redrawScreen()

                        elseif tab == 3
                            and #tape_queue > 0 then

                            queue_scroll =
                                queue_scroll
                                + (p1 * 2)

                            if queue_scroll < 0 then
                                queue_scroll = 0
                            end

                            if queue_scroll >
                               queue_max_scroll then

                                queue_scroll =
                                    queue_max_scroll
                            end

                            redrawScreen()
                        end
                    end

                    -- CLICK HANDLING

                    if event == "mouse_click" then

                        local button = p1

                        -- TAB BAR CLICK

                        if y == 1 then

                            local zone =
                                math.ceil(
                                    (x / width) * 7
                                )

                            if zone == 1
                                or zone == 2
                                or zone == 3 then

                                tab = zone

                                redrawScreen()

                                return
                            end

                            -- PLAY / PAUSE

                            if zone == 4
                                and tape then

                                if tape.isPlaying
                                    and tape.isPlaying() then

                                    tape.stop()

                                else

                                    tape.play()
                                end

                                redrawScreen()

                                return
                            end

                            -- STOP = REWIND

                            if zone == 5
                                and tape then

                                tape.stop()

                                stopVideoStream()

                                tape.seek(
                                    -99999999999
                                )

                                playingVideo =
                                    false

                                currentVideo =
                                    nil

                                audioPosition =
                                    0

                                redrawScreen()

                                return
                            end

                            -- NEXT BUTTON

                            if zone == 6 then

                                if tape_queue[1] then

                                    local result =
                                        tape_queue[1]

                                    table.remove(
                                        tape_queue,
                                        1
                                    )

                                    if result.type ==
                                        "playlist"
                                        and result.playlist_items
                                        and result.playlist_items[1] then

                                        result =
                                            result.playlist_items[1]
                                    end

                                    local url =
                                        build_download_url(
                                            result
                                        )

                                    if url and tape then

                                        stopVideoStream()

                                        playingVideo =
                                            false

                                        currentVideo =
                                            nil

                                        last_rendered_frame =
                                            nil

                                        audioPosition =
                                            0

                                        tape.seek(
                                            -999999999999
                                        )

                                        local response =
                                            safeHttpGet(
                                                url,
                                                true
                                            )

                                        if response then

                                            tape.write(
                                                response.readAll()
                                            )

                                            response.close()
                                        end

                                        tape.setLabel(
                                            result.name
                                            or "Unknown"
                                        )

                                        tape.seek(
                                            -999999999999
                                        )

                                        tape.play()
                                    end
                                end

                                redrawScreen()

                                return
                            end

                            -- WIPE

                            if zone == 7
                                and tape then

                                stopVideoStream()

                                local cache_cleared,
                                      cache_message =
                                    clearBackendCache()

                                term.setCursorPos(
                                    2,
                                    2
                                )

                                term.setTextColor(
                                    cache_cleared
                                    and colors.green
                                    or colors.red
                                )

                                term.write(
                                    cache_cleared
                                    and cache_message
                                    or "Cache clear failed: "
                                    .. cache_message
                                )

                                if not cache_cleared then
                                    sleep(1.5)
                                    redrawScreen()
                                    return
                                end

                                tape.seek(
                                    -99999999999
                                )

                                tape.write(
                                    string.rep(
                                        "\0",
                                        tape.getSize()
                                    )
                                )

                                tape.seek(
                                    -99999999999
                                )

                                if video_monitor then
                                    video_monitor.setBackgroundColor(
                                        colors.black
                                    )
                                    video_monitor.clear()
                                end

                                redrawScreen()

                                return
                            end
                        end

                        -- PROGRESS BAR SEEK

                        if tab == 1
                            and y == 6
                            and tape then

                            local bar_x = 2
                            local bar_w =
                                width - 3

                            if x >= bar_x
                                and x <= bar_x + bar_w then

                                local pct =
                                    (x - bar_x)
                                    / bar_w

                                pct =
                                    math.max(
                                        0,
                                        math.min(
                                            1,
                                            pct
                                        )
                                    )

                                local size =
                                    tape.getSize()

                                local target =
                                    math.floor(
                                        size * pct
                                    )

                                local current =
                                    tape.getPosition()

                                tape.seek(
                                    target
                                    - current
                                )

                                redrawScreen()

                                return
                            end
                        end

                        -- SEARCH BAR CLICK

                        if tab == 1
                            and y >= 3
                            and y <= 5 then

                            paintutils.drawFilledBox(
                                2,
                                3,
                                width - 1,
                                5,
                                colors.white
                            )

                            term.setBackgroundColor(
                                colors.white
                            )

                            waiting_for_input =
                                true

                            return
                        end

                        -- SEARCH RESULTS CLICK

                        if tab == 1
                            and search_results then

                            for i = 1,
                                #search_results do

                                local y_name =
                                    8
                                    + (i - 1) * 2
                                    - search_scroll

                                local y_artist =
                                    9
                                    + (i - 1) * 2
                                    - search_scroll

                                if y == y_name
                                    or y == y_artist then

                                    local result =
                                        search_results[i]

                                    if result.type ==
                                        "playlist" then

                                        result =
                                            result.playlist_items[1]
                                    end

                                    -- + BUTTON

                                    if y == y_name
                                        and x == width - 2 then

                                        table.insert(
                                            playlist,
                                            result
                                        )

                                        redrawScreen()

                                        return
                                    end

                                    -- RIGHT CLICK = QUEUE

                                    if button == 2 then

                                        table.insert(
                                            tape_queue,
                                            result
                                        )

                                        redrawScreen()

                                        return
                                    end

                                    -- LEFT CLICK = PLAY

                                    if button == 1 then

                                        stopVideoStream()

                                        playingVideo =
                                            false

                                        currentVideo =
                                            nil

                                        audioPosition =
                                            0

                                        last_rendered_frame =
                                            nil

                                        local url =
                                            build_download_url(
                                                result
                                            )

                                        if url and tape then

                                            -- Download audio first.
                                            -- Audio remains stopped while
                                            -- video is being prepared.

                                            tape.seek(
                                                -999999999999999
                                            )

                                            local response =
                                                safeHttpGet(
                                                    url,
                                                    true
                                                )

                                            if response then

                                                tape.write(
                                                    response.readAll()
                                                )

                                                response.close()

                                            end

                                            tape.setLabel(
                                                result.name
                                                or "Unknown"
                                            )

                                            tape.seek(
                                                -999999999999999
                                            )

                                            local video_source =
                                                result.url
                                                or result.id

                                            if video_source
                                                and video_monitor then

                                                local video_width,
                                                      video_height =
                                                    video_monitor.getSize()

                                                video_width =
                                                    math.min(
                                                        video_width,
                                                        128
                                                    )

                                                video_height =
                                                    math.min(
                                                        video_height,
                                                        72
                                                    )

                                                local video_url =
                                                    backend_video_url
                                                    .. textutils.urlEncode(
                                                        tostring(
                                                            video_source
                                                        )
                                                    )
                                                    .. "&resolution="
                                                    .. video_width
                                                    .. "x"
                                                    .. video_height
                                                    .. "&fps="
                                                    .. video_fps

                                                -- IMPORTANT:
                                                -- Start video stream BEFORE
                                                -- starting the tape.

                                                local streamedVideo =
                                                    streamNFV(
                                                        video_url
                                                    )

                                                if streamedVideo then

                                                    currentVideo =
                                                        streamedVideo

                                                    -- Wait for the first
                                                    -- frames to arrive while
                                                    -- the tape is still stopped.

                                                    waitForVideoPrebuffer(
                                                        currentVideo
                                                    )

                                                    tape.seek(
                                                        -999999999999999
                                                    )

                                                    audioPosition =
                                                        0

                                                    last_rendered_frame =
                                                        nil

                                                    playingVideo =
                                                        true

                                                    local video_started =
                                                        renderCurrentVideoFrame()

                                                    if video_started then
                                                        tape.play()
                                                    else
                                                        playingVideo = false
                                                    end

                                                else

                                                    -- Keep audio stopped when
                                                    -- video cannot start.
                                                end

                                            elseif not video_monitor then

                                                term.setCursorPos(
                                                    2,
                                                    2
                                                )

                                                term.setTextColor(
                                                    colors.red
                                                )

                                                term.write(
                                                    "No monitor found"
                                                )

                                                sleep(1.5)

                                            else

                                            end
                                        end

                                        redrawScreen()

                                        return
                                    end
                                end
                            end
                        end

                        -- PLAYLIST TAB CLICK

                        if tab == 2 then

                            if #playlist > 0
                                and y >= 4 then

                                for i = 1,
                                    #playlist do

                                    local y_controls =
                                        5
                                        + (i - 1) * 2
                                        - playlist_scroll

                                    if y ==
                                        y_controls then

                                        -- MOVE UP

                                        if x == 2
                                            or x == 3 then

                                            if i > 1 then

                                                playlist[i],
                                                playlist[i - 1] =
                                                    playlist[i - 1],
                                                    playlist[i]
                                            end
                                        end

                                        -- MOVE DOWN

                                        if x == 4
                                            or x == 5 then

                                            if i <
                                                #playlist then

                                                playlist[i],
                                                playlist[i + 1] =
                                                    playlist[i + 1],
                                                    playlist[i]
                                            end
                                        end

                                        -- REMOVE

                                        if x == 6
                                            or x == 7 then

                                            table.remove(
                                                playlist,
                                                i
                                            )
                                        end

                                        redrawScreen()

                                        return
                                    end
                                end
                            end
                        end

                        -- QUEUE TAB CLICK

                        if tab == 3 then

                            if y == 3 then

                                autoplay_next =
                                    not autoplay_next

                                redrawScreen()

                                return
                            end

                            if #tape_queue > 0
                                and y >= 4 then

                                for i = 1,
                                    #tape_queue do

                                    local y_controls =
                                        5
                                        + (i - 1) * 2
                                        - queue_scroll

                                    if y ==
                                        y_controls then

                                        -- MOVE UP

                                        if x == 2
                                            or x == 3 then

                                            if i > 1 then

                                                tape_queue[i],
                                                tape_queue[i - 1] =
                                                    tape_queue[i - 1],
                                                    tape_queue[i]
                                            end
                                        end

                                        -- MOVE DOWN

                                        if x == 4
                                            or x == 5 then

                                            if i <
                                                #tape_queue then

                                                tape_queue[i],
                                                tape_queue[i + 1] =
                                                    tape_queue[i + 1],
                                                    tape_queue[i]
                                            end
                                        end

                                        -- REMOVE

                                        if x == 6
                                            or x == 7 then

                                            table.remove(
                                                tape_queue,
                                                i
                                            )
                                        end

                                        redrawScreen()

                                        return
                                    end
                                end
                            end
                        end
                    end
                end,

                function()

                    local event =
                        os.pullEvent(
                            "redraw_screen"
                        )

                    redrawScreen()
                end
            )
        end
    end
end

-----------------------------
-- HTTP LOOP
-----------------------------

local function httpLoop()

    while true do

        parallel.waitForAny(

            function()

                local event,
                      url,
                      handle =
                    os.pullEvent(
                        "http_success"
                    )

                if url ==
                    last_search_url then

                    local body =
                        handle.readAll()

                    handle.close()

                    local raw =
                        textutils.unserialiseJSON(
                            body
                        )

                    search_results =
                        filterPromo(
                            raw
                        )

                    os.queueEvent(
                        "redraw_screen"
                    )

                    redrawScreen()
                end
            end,

            function()

                local event,
                      url =
                    os.pullEvent(
                        "http_failure"
                    )

                if url ==
                    last_search_url then

                    search_error =
                        true

                    os.queueEvent(
                        "redraw_screen"
                    )
                end
            end
        )
    end
end

-----------------------------
-- VIDEO LOOP
-----------------------------

local function videoLoop()

    local frame_period_ms =
        1000 / monitor_fps

    local next_frame_time =
        os.epoch("utc")

    while true do

        if playingVideo
            and currentVideo
            and tape then

            -- Tape position is the master clock.

            audioPosition =
                getAudioTime()

            local rendered,
                  render_error =
                pcall(
                    renderCurrentVideoFrame
                )

            if not rendered then

                print(
                    "Video render error: "
                    .. tostring(
                        render_error
                    )
                )

                playingVideo =
                    false
            end

            next_frame_time =
                next_frame_time
                + frame_period_ms

            local now =
                os.epoch("utc")

            local wait_time =
                next_frame_time
                - now

            if wait_time > 0 then

                -- Do not wake up for every
                -- incoming video frame.
                --
                -- The video producer continues
                -- independently through videoStreamLoop.

                sleep(
                    wait_time / 1000
                )

            else

                next_frame_time =
                    now
            end

        else

            next_frame_time =
                os.epoch("utc")

            sleep(
                0.05
            )
        end
    end
end

-----------------------------
-- START
-----------------------------

parallel.waitForAny(
    uiLoop,
    httpLoop,
    videoLoop,
    videoStreamLoop
)

term.setBackgroundColor(
    colors.black
)

term.setTextColor(
    colors.white
)

term.clear()

term.setCursorPos(
    1,
    1
)
