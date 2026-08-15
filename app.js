(() => {
  "use strict";

  const REC_BUFFER_SIZE = 2048;
  const HOLD_MS = 800; // press-and-hold threshold, shared by every button
  const RIPPLE_MS = 1500; // covers the last ripple's delay + duration
  const SCRUB_RATES = [2, 8, 25, 60]; // seconds of tape per second, per stage
  const METER_SEGMENTS = 14;
  const METER_WARN_FROM = 10; // segments from here up are yellow
  const METER_CLIP_FROM = 12; // ...and from here up, red
  const METER_FLOOR_DB = -48; // bottom of the meter's range
  const METER_PEAK_HOLD_MS = 900;
  const OFFSET_STEP = 0.005; // 5ms per press
  const OFFSET_LIMIT = 1.0; // clamp track 2 shifting to +/- 1 second
  const COUNT_START_STEP = 0.005; // 5ms per press
  const COUNT_START_LIMIT = 5.0; // count can begin up to 5s either side of the head
  const BPM_MIN = 40;
  const BPM_MAX = 300;
  const BEATS_MIN = 1;
  const BEATS_MAX = 16;
  const BEEP_HZ = 1000;
  const BEEP_PEAK = 0.5; // amplitude at 100% count volume
  const COUNT_VOL_STEP = 0.05;
  const PREVIEW_SECONDS = 5; // how long a preview runs from the count start
  const PREVIEW_MIN_AFTER_HEAD = 3; // ...but always this far past the head
  const BEEP_LEN = 0.09;

  const el = {
    app: document.getElementById("app"),
    trackLabel: document.getElementById("trackLabel"),
    loadBtn: document.getElementById("loadBtn"),
    fileInput: document.getElementById("fileInput"),
    timeDisplay: document.getElementById("timeDisplay"),
    meter: document.getElementById("meter"),
    meterLabel: document.getElementById("meterLabel"),
    markerADisplay: document.getElementById("markerADisplay"),
    markerBDisplay: document.getElementById("markerBDisplay"),
    rewindBtn: document.getElementById("rewindBtn"),
    playBtn: document.getElementById("playBtn"),
    playIcon: document.getElementById("playIcon"),
    ffBtn: document.getElementById("ffBtn"),
    recBtn: document.getElementById("recBtn"),
    recWrap: document.getElementById("recWrap"),
    markerABtn: document.getElementById("markerABtn"),
    markerBBtn: document.getElementById("markerBBtn"),
    recMark: document.getElementById("recMark"),
    dotA: document.getElementById("dotA"),
    dotB: document.getElementById("dotB"),
    markerALabel: document.getElementById("markerALabel"),
    markerBLabel: document.getElementById("markerBLabel"),
    loopABBtn: document.getElementById("loopABBtn"),
    countInBtn: document.getElementById("countInBtn"),
    countInState: document.getElementById("countInState"),
    dotCountIn: document.getElementById("dotCountIn"),
    countInModal: document.getElementById("countInModal"),
    bpmInput: document.getElementById("bpmInput"),
    bpmMinusBtn: document.getElementById("bpmMinusBtn"),
    bpmPlusBtn: document.getElementById("bpmPlusBtn"),
    beatsValue: document.getElementById("beatsValue"),
    countVolValue: document.getElementById("countVolValue"),
    countVolMinusBtn: document.getElementById("countVolMinusBtn"),
    countVolPlusBtn: document.getElementById("countVolPlusBtn"),
    beatsMinusBtn: document.getElementById("beatsMinusBtn"),
    beatsPlusBtn: document.getElementById("beatsPlusBtn"),
    countStartInput: document.getElementById("countStartInput"),
    countStartMinusBtn: document.getElementById("countStartMinusBtn"),
    countStartPlusBtn: document.getElementById("countStartPlusBtn"),
    countInSummary: document.getElementById("countInSummary"),
    countInPreviewBtn: document.getElementById("countInPreviewBtn"),
    countInCloseBtn: document.getElementById("countInCloseBtn"),
    track2MuteBtn: document.getElementById("track2MuteBtn"),
    track2State: document.getElementById("track2State"),
    dotTrack2: document.getElementById("dotTrack2"),
    monitorBtn: document.getElementById("monitorBtn"),
    monitorState: document.getElementById("monitorState"),
    dotMonitor: document.getElementById("dotMonitor"),
    offsetMinusBtn: document.getElementById("offsetMinusBtn"),
    offsetPlusBtn: document.getElementById("offsetPlusBtn"),
    offsetReadout: document.getElementById("offsetReadout"),
    balanceSlider: document.getElementById("balanceSlider"),
    panSlider: document.getElementById("panSlider"),
    statusMsg: document.getElementById("statusMsg"),
  };

  const ICON_PLAY = '<path d="M7 5L19 12L7 19V5Z" fill="currentColor"/>';
  const ICON_PAUSE =
    '<rect x="6" y="5" width="4" height="14" rx="1" fill="currentColor"/><rect x="14" y="5" width="4" height="14" rx="1" fill="currentColor"/>';

  class TapeRecorder {
    constructor() {
      this.audioCtx = null;

      this.track1Buffer = null; // decoded stereo music AudioBuffer
      this.track2Buffer = null; // mono recorded AudioBuffer (live-writable)
      this.track2Data = null; // Float32Array view into track2Buffer channel 0
      this.track2HasData = false; // drives the paw mark on the LCD
      this.duration = 0;

      this.isPlaying = false;
      this.isRecording = false;
      this.isArmed = false; // REC pressed while stopped, waiting on PLAY
      this.track2Offset = 0; // seconds the recorded track is shifted by
      this.scrubDirection = 0; // -1 rewind, +1 fast-forward, 0 idle
      this.scrubStage = 0; // 1..4, drives speed and colour
      this.scrubRaf = null;
      this.playhead = 0; // seconds, valid while stopped
      this.contextStartTime = 0; // audioCtx.currentTime at last (re)start
      this.startOffset = 0; // playhead value at that (re)start

      this.markerA = null;
      this.markerB = null;
      this.loopAB = false;

      this.track1Source = null;
      this.track2Source = null;

      this.micStream = null;
      this.micSourceNode = null;
      this.recProcessor = null;
      this.recSilentGain = null;
      this.monitorGain = null;
      this.monitorMuted = true; // input monitoring is off until asked for
      this.track2Gain = null;
      this.track2Muted = false; // the recorded track plays back by default

      this.countInEnabled = false;
      this.countInBpm = 120;
      this.countInBeats = 4;
      this.countInStart = -2.0; // timeline position of the first beep, seconds
      this.countInVolume = 0.7;
      this.countInVoices = []; // scheduled beeps, so they can be cancelled
      this.previewTimer = null;
      this.previewResumeAt = 0;
      this.previewWasArmed = false;

      this.musicGain = null;
      this.guitarGain = null;
      this.guitarPanner = null;

      this.balance = 0;
      this.pan = 0;

      this.rafId = null;
      this.scrubTimer = null;

      this.analyser = null;
      this.analyserData = null;
      this.meterSegments = [];
      this.meterRaf = null;
      this.meterLevel = 0;
      this.meterPeak = 0;
      this.meterPeakAt = 0;

      this.buildMeter();
      this.bindUI();
      this.updateTransportEnabled();
      this.render();
    }

    // ---------- setup ----------

    ensureAudioCtx() {
      if (!this.audioCtx) {
        this.audioCtx = new (window.AudioContext || window.webkitAudioContext)();
        this.musicGain = this.audioCtx.createGain();
        this.guitarGain = this.audioCtx.createGain();
        this.guitarPanner = this.audioCtx.createStereoPanner();

        this.musicGain.connect(this.audioCtx.destination);
        // Recorded playback gets its own gain so muting it leaves the input
        // monitor, which shares guitarGain, still audible.
        this.track2Gain = this.audioCtx.createGain();
        this.track2Gain.gain.value = this.track2Muted ? 0 : 1;
        this.track2Gain.connect(this.guitarGain);

        this.guitarGain.connect(this.guitarPanner);
        this.guitarPanner.connect(this.audioCtx.destination);

        this.applyBalance();
        this.applyPan();
      }
      if (this.audioCtx.state === "suspended") {
        this.audioCtx.resume();
      }
      return this.audioCtx;
    }

    bindUI() {
      // Backstop for the iOS long-press callout on anything not covered by CSS,
      // except text fields, where the menu is how you paste.
      document.addEventListener("contextmenu", (e) => {
        if (!e.target.closest("input")) e.preventDefault();
      });

      el.loadBtn.addEventListener("click", () => el.fileInput.click());
      el.fileInput.addEventListener("change", (e) => this.onFileSelected(e));

      el.playBtn.addEventListener("click", () => this.togglePlayWithCountIn());

      this.bindTapHold(el.countInBtn, {
        onTap: () => this.toggleCountIn(),
        onHold: () => this.openCountInModal(),
      });

      this.bindRepeat(el.bpmMinusBtn, () => this.nudgeBpm(-1));
      this.bindRepeat(el.bpmPlusBtn, () => this.nudgeBpm(1));
      this.bindRepeat(el.beatsMinusBtn, () => this.nudgeBeats(-1));
      this.bindRepeat(el.beatsPlusBtn, () => this.nudgeBeats(1));
      this.bindRepeat(el.countStartMinusBtn, () => this.nudgeCountStart(-1));
      this.bindRepeat(el.countStartPlusBtn, () => this.nudgeCountStart(1));
      this.bindRepeat(el.countVolMinusBtn, () => this.nudgeCountVolume(-1));
      this.bindRepeat(el.countVolPlusBtn, () => this.nudgeCountVolume(1));
      this.bindNumberInput(el.bpmInput, () => this.commitBpm());
      this.bindNumberInput(el.countStartInput, () => this.commitCountStart());

      el.countInPreviewBtn.addEventListener("click", () => this.previewCountIn());
      el.countInCloseBtn.addEventListener("click", () => this.closeCountInModal());
      el.countInModal.addEventListener("pointerdown", (e) => {
        if (e.target === el.countInModal) this.closeCountInModal();
      });

      this.bindTapHold(el.recBtn, {
        onTap: () => this.toggleRecord(),
        onHold: () => this.eraseTrack2(),
        holdClass: "holding",
      });

      // Tap steps the scrub speed; hold jumps to the very start / end.
      this.bindTapHold(el.rewindBtn, {
        onTap: () => this.stepScrub(-1),
        onHold: () => this.jumpTo(0),
      });
      this.bindTapHold(el.ffBtn, {
        onTap: () => this.stepScrub(1),
        onHold: () => this.jumpTo(this.duration),
      });

      this.bindTapHold(el.markerABtn, {
        onTap: () => this.markerTap("A"),
        onHold: () => this.clearMarker("A"),
      });
      this.bindTapHold(el.markerBBtn, {
        onTap: () => this.markerTap("B"),
        onHold: () => this.clearMarker("B"),
      });

      el.monitorBtn.addEventListener("click", () => this.toggleMonitor());
      el.track2MuteBtn.addEventListener("click", () => this.toggleTrack2Mute());

      this.bindRepeat(el.offsetMinusBtn, () => this.nudgeTrack2(-1));
      this.bindRepeat(el.offsetPlusBtn, () => this.nudgeTrack2(1));
      el.loopABBtn.addEventListener("click", () => this.toggleLoopAB());

      el.balanceSlider.addEventListener("input", () => {
        this.balance = parseFloat(el.balanceSlider.value);
        this.applyBalance();
      });
      el.panSlider.addEventListener("input", () => {
        this.pan = parseFloat(el.panSlider.value);
        this.applyPan();
      });
    }

    /**
     * Wires a button so a quick press runs onTap and a press held past
     * HOLD_MS runs onHold instead. The hold suppresses the release, so the
     * two actions never both fire from one press.
     */
    bindTapHold(button, { onTap, onHold, holdClass }) {
      let timer = null;
      let held = false;

      const down = (e) => {
        if (button.disabled) return;
        e.preventDefault();
        held = false;
        if (holdClass) button.classList.add(holdClass);
        clearTimeout(timer);
        timer = setTimeout(() => {
          held = true;
          if (holdClass) button.classList.remove(holdClass);
          onHold();
        }, HOLD_MS);
      };

      const up = () => {
        clearTimeout(timer);
        if (holdClass) button.classList.remove(holdClass);
        if (!held) onTap();
        held = false;
      };

      const cancel = () => {
        clearTimeout(timer);
        if (holdClass) button.classList.remove(holdClass);
        held = false;
      };

      button.addEventListener("pointerdown", down);
      button.addEventListener("pointerup", up);
      button.addEventListener("pointerleave", cancel);
      button.addEventListener("pointercancel", cancel);
      button.addEventListener("contextmenu", (e) => e.preventDefault());
    }

    /** Commits a typed value on blur or Enter, and keeps keys off the transport. */
    bindNumberInput(input, commit) {
      input.addEventListener("change", commit);
      input.addEventListener("keydown", (e) => {
        e.stopPropagation();
        if (e.key === "Enter") input.blur();
      });
    }

    /** Fires action on press, then repeatedly while the button stays held. */
    bindRepeat(button, action) {
      let timer = null;
      let interval = null;

      const stop = () => {
        clearTimeout(timer);
        clearInterval(interval);
      };

      button.addEventListener("pointerdown", (e) => {
        if (button.disabled) return;
        e.preventDefault();
        action();
        stop();
        timer = setTimeout(() => {
          interval = setInterval(action, 80);
        }, 400);
      });
      button.addEventListener("pointerup", stop);
      button.addEventListener("pointerleave", stop);
      button.addEventListener("pointercancel", stop);
      button.addEventListener("contextmenu", (e) => e.preventDefault());
    }

    // ---------- file loading ----------

    async onFileSelected(e) {
      const file = e.target.files[0];
      if (!file) return;
      try {
        this.setStatus("読み込み中...");
        const ctx = this.ensureAudioCtx();
        const decoded = await this.decodeMediaFile(file);

        this.stopAll();
        this.track1Buffer = decoded;
        this.duration = decoded.duration;

        this.track2Buffer = ctx.createBuffer(1, decoded.length, ctx.sampleRate);
        this.track2Data = this.track2Buffer.getChannelData(0);
        this.track2HasData = false;

        this.playhead = 0;
        this.markerA = null;
        this.markerB = null;
        this.loopAB = false;
        this.track2Offset = 0;

        el.trackLabel.textContent = file.name;
        this.updateTransportEnabled();
        this.render();
        this.setStatus("");
      } catch (err) {
        console.error(err);
        this.setStatus(err && err.userMessage ? err.userMessage : "読み込みに失敗しました");
      } finally {
        el.fileInput.value = "";
      }
    }

    /**
     * Decodes audio from an audio OR video file. decodeAudioData handles both
     * (it pulls just the audio track out of a video container) and is near
     * instant, so it is tried first. Containers it rejects but the media
     * pipeline can still play — varies by browser — fall back to capturing the
     * audio through a media element, which runs in real time.
     */
    async decodeMediaFile(file) {
      const ctx = this.ensureAudioCtx();
      try {
        const arrayBuffer = await file.arrayBuffer();
        return await ctx.decodeAudioData(arrayBuffer);
      } catch (err) {
        return await this.extractAudioViaPlayback(file);
      }
    }

    async extractAudioViaPlayback(file) {
      const ctx = this.ensureAudioCtx();
      const url = URL.createObjectURL(file);
      const media = document.createElement("video");
      media.src = url;
      media.playsInline = true;
      media.preload = "auto";

      let src = null;
      let processor = null;
      let silentGain = null;

      try {
        await new Promise((resolve, reject) => {
          media.addEventListener("loadedmetadata", resolve, { once: true });
          media.addEventListener("error", () => reject(this.unsupportedError()), { once: true });
        });

        const duration = media.duration;
        if (!isFinite(duration) || duration <= 0) throw this.unsupportedError();

        const sampleRate = ctx.sampleRate;
        const capacity = Math.ceil((duration + 1) * sampleRate);
        const left = new Float32Array(capacity);
        const right = new Float32Array(capacity);
        let written = 0;
        let peak = 0;

        src = ctx.createMediaElementSource(media);
        processor = ctx.createScriptProcessor(REC_BUFFER_SIZE, 2, 2);
        silentGain = ctx.createGain();
        silentGain.gain.value = 0; // extraction should be inaudible

        processor.onaudioprocess = (e) => {
          const input = e.inputBuffer;
          const inL = input.getChannelData(0);
          const inR = input.numberOfChannels > 1 ? input.getChannelData(1) : inL;
          const n = Math.min(inL.length, capacity - written);
          for (let i = 0; i < n; i++) {
            left[written + i] = inL[i];
            right[written + i] = inR[i];
            const a = Math.abs(inL[i]);
            if (a > peak) peak = a;
          }
          written += n;
        };

        src.connect(processor);
        processor.connect(silentGain);
        silentGain.connect(ctx.destination);

        const onProgress = () => {
          const pct = Math.min(100, Math.round((media.currentTime / duration) * 100));
          this.setStatus(`動画から音声を抽出中... ${pct}%（実時間かかります）`);
        };
        media.addEventListener("timeupdate", onProgress);
        onProgress();

        try {
          await media.play();
        } catch (err) {
          throw this.userError("自動再生がブロックされました。もう一度ファイルを選び直してください");
        }

        await new Promise((resolve, reject) => {
          media.addEventListener("ended", resolve, { once: true });
          media.addEventListener("error", () => reject(this.unsupportedError()), { once: true });
        });
        media.removeEventListener("timeupdate", onProgress);

        if (written === 0 || peak === 0) {
          throw this.userError("このファイルに音声トラックが見つかりませんでした");
        }

        const out = ctx.createBuffer(2, written, sampleRate);
        out.copyToChannel(left.subarray(0, written), 0);
        out.copyToChannel(right.subarray(0, written), 1);
        return out;
      } finally {
        if (processor) processor.onaudioprocess = null;
        [src, processor, silentGain].forEach((node) => {
          if (node) { try { node.disconnect(); } catch (e) {} }
        });
        media.pause();
        media.removeAttribute("src");
        media.load();
        URL.revokeObjectURL(url);
      }
    }

    userError(message) {
      const err = new Error(message);
      err.userMessage = message;
      return err;
    }

    unsupportedError() {
      return this.userError("この形式は再生できません。mp3/wav/m4a/mp4 などに変換してください");
    }

    updateTransportEnabled() {
      const ready = !!this.track1Buffer;
      [el.playBtn, el.recBtn, el.rewindBtn, el.ffBtn, el.markerABtn, el.markerBBtn, el.loopABBtn].forEach(
        (b) => (b.disabled = !ready)
      );
    }

    // ---------- transport clock ----------

    getPlayhead() {
      if (this.isPlaying) {
        return this.startOffset + (this.audioCtx.currentTime - this.contextStartTime);
      }
      return this.playhead;
    }

    playheadAtContextTime(t) {
      return this.startOffset + (t - this.contextStartTime);
    }

    startClock() {
      const tick = () => {
        const t = this.getPlayhead();

        if (this.loopAB && this.markerA != null && this.markerB != null && t >= this.markerB) {
          this.seekTo(this.markerA, true);
          this.rafId = requestAnimationFrame(tick);
          return;
        }

        if (t >= this.duration) {
          this.pause();
          this.playhead = this.duration;
          this.render();
          return;
        }

        this.render();
        this.rafId = requestAnimationFrame(tick);
      };
      cancelAnimationFrame(this.rafId);
      this.rafId = requestAnimationFrame(tick);
    }

    stopClock() {
      cancelAnimationFrame(this.rafId);
      this.rafId = null;
    }

    // ---------- playback sources ----------

    startTrack1Source(offset) {
      const ctx = this.audioCtx;
      const src = ctx.createBufferSource();
      src.buffer = this.track1Buffer;
      src.connect(this.musicGain);
      if (!this.startSourceAt(src, offset)) return;
      this.track1Source = src;
    }

    /**
     * Cues a source to a timeline position. A position before zero — which the
     * count-in uses — waits that long and then rolls from the top rather than
     * reading behind the start of the buffer.
     */
    startSourceAt(src, position) {
      const ctx = this.audioCtx;
      if (position >= 0) {
        if (position >= src.buffer.duration) return false; // nothing left to play
        src.start(0, position);
      } else {
        src.start(ctx.currentTime + -position, 0);
      }
      return true;
    }

    /**
     * Starts the recorded track shifted by track2Offset: a positive offset
     * plays it later, a negative one earlier, which is what compensates for
     * recording latency. Reading before the start of the take means waiting
     * that long before rolling it instead.
     */
    startTrack2Source(offset) {
      const ctx = this.audioCtx;
      const src = ctx.createBufferSource();
      src.buffer = this.track2Buffer;
      src.connect(this.track2Gain);

      if (!this.startSourceAt(src, offset - this.track2Offset)) return;
      this.track2Source = src;
    }

    nudgeTrack2(direction) {
      if (!this.track2Buffer) return;
      const next = this.track2Offset + direction * OFFSET_STEP;
      this.track2Offset = Math.max(-OFFSET_LIMIT, Math.min(OFFSET_LIMIT, next));

      // Re-cue so the new alignment is audible straight away.
      if (this.isPlaying && !this.isRecording) {
        this.stopTrack2Playback();
        this.startTrack2Source(this.getPlayhead());
      }
      this.render();
    }

    stopSources() {
      if (this.track1Source) {
        try { this.track1Source.stop(); } catch (e) {}
        this.track1Source.disconnect();
        this.track1Source = null;
      }
      if (this.track2Source) {
        try { this.track2Source.stop(); } catch (e) {}
        this.track2Source.disconnect();
        this.track2Source = null;
      }
    }

    // ---------- transport controls ----------

    play(fromSeconds = null) {
      if (!this.track1Buffer) return;
      const ctx = this.ensureAudioCtx();
      this.stopPreview(); // any transport move ends a running preview
      this.stopScrub();
      this.stopSources();

      // PLAY is what actually rolls tape on an armed recording.
      if (this.isArmed) {
        this.isArmed = false;
        this.isRecording = true;
      }

      const startAt = fromSeconds !== null ? fromSeconds : this.playhead;
      // The floor is the count-in position, not 0, so the tape can roll from
      // before the head while the beeps play.
      const floor = Math.min(0, this.countInStart);
      this.startOffset = Math.max(floor, Math.min(startAt, this.duration));
      this.contextStartTime = ctx.currentTime;
      this.isPlaying = true;

      this.startTrack1Source(this.startOffset);
      // While recording, track 2 stays silent — it is being overwritten.
      if (!this.isRecording) {
        this.startTrack2Source(this.startOffset);
      }

      this.startClock();
      this.updatePlayIcon();
    }

    /** PLAY leads in with the count when it is switched on. */
    togglePlayWithCountIn() {
      if (this.isPlaying) {
        this.pause();
        return;
      }
      if (!this.track1Buffer || !this.countInEnabled) {
        this.play();
        return;
      }

      const ctx = this.ensureAudioCtx();
      this.cancelCountIn();
      this.play(this.countInStart);
      this.scheduleCountIn(this.contextStartTime, this.startOffset);
    }

    pause() {
      if (!this.isPlaying) return;
      this.stopPreview();
      this.cancelCountIn();
      this.playhead = Math.max(0, this.getPlayhead());
      if (this.isRecording) this.disengageRecording();
      this.isArmed = false;
      this.stopSources();
      this.isPlaying = false;
      this.stopClock();
      this.updatePlayIcon();
      this.render();
    }

    seekTo(seconds, keepPlaying) {
      const clamped = Math.max(0, Math.min(seconds, this.duration));
      this.disengageRecording();

      if (this.isPlaying && (keepPlaying !== false)) {
        this.play(clamped);
      } else {
        this.stopSources();
        this.isPlaying = false;
        this.stopClock();
        this.playhead = clamped;
        this.updatePlayIcon();
        this.render();
      }
    }

    /**
     * Each tap advances the scrub speed one stage (wrapping after the 4th) and
     * runs a silent shuttle in that direction. Tapping the opposite button
     * flips direction and restarts at stage 1. PLAY stops it.
     */
    stepScrub(direction) {
      if (!this.track1Buffer) return;

      if (this.scrubDirection === direction) {
        this.scrubStage = (this.scrubStage % SCRUB_RATES.length) + 1;
      } else {
        this.scrubDirection = direction;
        this.scrubStage = 1;
      }

      if (this.isPlaying) this.pause(); // shuttling is silent, like a tape search
      this.runScrub();
      this.render();
    }

    runScrub() {
      cancelAnimationFrame(this.scrubRaf);
      let last = performance.now();

      const step = (now) => {
        const dt = (now - last) / 1000;
        last = now;

        const rate = SCRUB_RATES[this.scrubStage - 1];
        let t = this.playhead + this.scrubDirection * rate * dt;

        if (t <= 0) {
          this.playhead = 0;
          this.stopScrub();
          return;
        }
        if (t >= this.duration) {
          this.playhead = this.duration;
          this.stopScrub();
          return;
        }

        this.playhead = t;
        this.render();
        this.scrubRaf = requestAnimationFrame(step);
      };

      this.scrubRaf = requestAnimationFrame(step);
    }

    stopScrub() {
      cancelAnimationFrame(this.scrubRaf);
      this.scrubRaf = null;
      this.scrubDirection = 0;
      this.scrubStage = 0;
      this.render();
    }

    /** Hold target for rewind / fast-forward: straight to the start or end. */
    jumpTo(seconds) {
      if (!this.track1Buffer) return;
      this.stopScrub();
      this.seekTo(seconds, this.isPlaying);
    }

    playFromMarker(which) {
      const target = which === "A" ? this.markerA : this.markerB;
      if (target == null) return;
      this.seekTo(target, true);
      if (!this.isPlaying) this.play(target);
    }

    stopAll() {
      this.stopClock();
      this.stopScrub();
      this.stopSources();
      this.disengageRecording();
      this.isArmed = false;
      this.isPlaying = false;
      this.playhead = 0;
      this.updatePlayIcon();
    }

    // ---------- markers ----------

    /**
     * One button per marker: sets it while empty, plays from it once set, and
     * clears it on a hold. Setting never overwrites, so the mark you punched
     * in at stays put until you deliberately drop it.
     */
    markerTap(which) {
      const existing = which === "A" ? this.markerA : this.markerB;
      if (existing == null) this.setMarker(which);
      else this.playFromMarker(which);
    }

    /** Refuses to overwrite: an existing marker has to be cleared by holding first. */
    setMarker(which) {
      const existing = which === "A" ? this.markerA : this.markerB;
      if (existing != null) {
        this.setStatus(`マーカー${which}は設定済みです - 長押しで解除`, 1800);
        return;
      }

      const t = this.getPlayhead();
      if (which === "A") this.markerA = t;
      else this.markerB = t;
      this.render();
    }

    /** Hold target for the marker buttons. */
    clearMarker(which) {
      if (which === "A") this.markerA = null;
      else this.markerB = null;
      if (this.markerA == null || this.markerB == null) this.loopAB = false;
      this.setStatus(`マーカー${which}を解除しました`, 1800);
      this.render();
    }

    toggleLoopAB() {
      if (this.markerA == null || this.markerB == null) return;
      this.loopAB = !this.loopAB;
      this.render();
    }

    // ---------- recording (punch in/out) ----------

    /**
     * Stopped: REC arms the track and PLAY rolls it. Already rolling: REC
     * punches straight in or out, so partial takes still work mid-playback.
     */
    async toggleRecord() {
      if (!this.track1Buffer) return;

      if (this.isRecording) {
        this.disengageRecording();
        this.render();
        return;
      }

      if (this.isArmed) {
        this.isArmed = false;
        this.setStatus("録音待機を解除しました", 1800);
        this.render();
        return;
      }

      try {
        await this.ensureMic();
      } catch (err) {
        console.error(err);
        this.setStatus("マイクにアクセスできませんでした");
        return;
      }

      if (this.isPlaying) {
        this.isRecording = true;
        this.stopTrack2Playback();
      } else {
        this.isArmed = true;
        this.setStatus("録音待機中 - 再生ボタンでスタート");
      }
      this.render();
    }

    async ensureMic() {
      if (this.micStream) return;
      const ctx = this.ensureAudioCtx();
      this.micStream = await navigator.mediaDevices.getUserMedia({
        audio: { echoCancellation: false, noiseSuppression: false, autoGainControl: false },
      });
      this.micSourceNode = ctx.createMediaStreamSource(this.micStream);

      this.analyser = ctx.createAnalyser();
      this.analyser.fftSize = 1024;
      this.analyserData = new Float32Array(this.analyser.fftSize);
      this.micSourceNode.connect(this.analyser); // silent tap, never reaches output
      this.startMeter();

      this.recProcessor = ctx.createScriptProcessor(REC_BUFFER_SIZE, 1, 1);
      this.recSilentGain = ctx.createGain();
      this.recSilentGain.gain.value = 0;
      this.recProcessor.connect(this.recSilentGain);
      this.recSilentGain.connect(ctx.destination);

      this.recProcessor.onaudioprocess = (e) => this.handleRecordProcess(e);

      // Both taps stay connected for the life of the mic; the record handler
      // ignores blocks while stopped, and monitorGain holds the output at zero
      // until monitoring is unmuted.
      this.monitorGain = ctx.createGain();
      this.monitorGain.gain.value = this.monitorMuted ? 0 : 1;
      this.monitorGain.connect(this.guitarGain);
      this.micSourceNode.connect(this.monitorGain);
      this.micSourceNode.connect(this.recProcessor);
    }

    handleRecordProcess(e) {
      if (!this.isRecording || !this.track2Data) return;
      const input = e.inputBuffer.getChannelData(0);
      const blockStartPlayhead = this.playheadAtContextTime(e.playbackTime);
      const startSample = Math.round(blockStartPlayhead * this.audioCtx.sampleRate);
      const len = this.track2Data.length;

      let audible = false;
      for (let i = 0; i < input.length; i++) {
        const idx = startSample + i;
        if (idx >= 0 && idx < len) {
          const sample = input[i];
          this.track2Data[idx] = sample;
          if (sample !== 0) audible = true;
        }
      }

      // The render loop is already running while recording, so flag it and let
      // the next frame light the paw rather than touching the DOM from here.
      if (audible) this.track2HasData = true;
    }

    /**
     * Monitoring is independent of recording: the mic feeds the output through
     * monitorGain, which the mute button opens and closes. Muting never
     * touches the recording tap or the meter, so a muted take still records
     * and still reads on the meter.
     */
    async toggleMonitor() {
      const nextMuted = !this.monitorMuted;

      if (!nextMuted) {
        try {
          await this.ensureMic(); // unmuting is a reason to open the mic
        } catch (err) {
          console.error(err);
          this.setStatus("マイクにアクセスできませんでした");
          return;
        }
      }

      this.monitorMuted = nextMuted;
      this.applyMonitor();
      this.setStatus(
        nextMuted ? "入力モニターをミュートしました" : "入力モニターON - ハウリングに注意",
        2200
      );
      this.render();
    }

    applyMonitor() {
      if (!this.monitorGain) return;
      // Ramp rather than jump, so toggling does not click.
      this.monitorGain.gain.setTargetAtTime(
        this.monitorMuted ? 0 : 1,
        this.audioCtx.currentTime,
        0.01
      );
    }

    /** Silences playback of the recorded track without affecting the monitor. */
    toggleTrack2Mute() {
      this.track2Muted = !this.track2Muted;
      this.applyTrack2Mute();
      this.setStatus(
        this.track2Muted ? "録音トラックをミュートしました" : "録音トラックのミュートを解除しました",
        2000
      );
      this.render();
    }

    applyTrack2Mute() {
      if (!this.track2Gain) return;
      this.track2Gain.gain.setTargetAtTime(
        this.track2Muted ? 0 : 1,
        this.audioCtx.currentTime,
        0.01
      );
    }

    stopTrack2Playback() {
      if (this.track2Source) {
        try { this.track2Source.stop(); } catch (e) {}
        this.track2Source.disconnect();
        this.track2Source = null;
      }
    }

    /** Clears the whole mono recording track, keeping the loaded music intact. */
    eraseTrack2() {
      if (!this.track2Data) return;

      this.disengageRecording();
      this.track2Data.fill(0);
      this.track2HasData = false;

      // The playing source still references the pre-erase audio, so restart it.
      if (this.isPlaying) {
        this.stopTrack2Playback();
        this.startTrack2Source(this.getPlayhead());
      }

      this.playRipple();
      this.setStatus("録音トラックを消去しました", 2200);
      this.render();
    }

    playRipple() {
      el.recWrap.classList.remove("erasing");
      void el.recWrap.offsetWidth; // reflow, so a repeated erase replays the animation
      el.recWrap.classList.add("erasing");
      clearTimeout(this.rippleTimer);
      this.rippleTimer = setTimeout(() => el.recWrap.classList.remove("erasing"), RIPPLE_MS);
    }

    disengageRecording() {
      if (!this.isRecording) return;
      this.isRecording = false;
      if (this.isPlaying) {
        this.startTrack2Source(this.getPlayhead());
      }
    }

    // ---------- count in ----------

    toggleCountIn() {
      this.countInEnabled = !this.countInEnabled;
      this.setStatus(
        this.countInEnabled ? "カウントインON - 長押しで設定" : "カウントインOFF",
        1800
      );
      this.render();
    }

    /**
     * Beeps sit at fixed timeline positions starting at countInStart, which can
     * be negative so the count lands before a song that plays from its first
     * sample. contextStart/timelineStart map that timeline onto the clock the
     * transport just started against.
     */
    scheduleCountIn(contextStart, timelineStart) {
      const ctx = this.audioCtx;
      const interval = 60 / this.countInBpm;

      for (let i = 0; i < this.countInBeats; i++) {
        const at = contextStart + (this.countInStart + i * interval - timelineStart);
        if (at < ctx.currentTime) continue; // that beat is already behind us
        this.playBeep(at);
      }
    }

    playBeep(at) {
      const peak = BEEP_PEAK * this.countInVolume;
      if (peak <= 0.0001) return; // silent, and an exponential ramp needs > 0

      const ctx = this.audioCtx;
      const osc = ctx.createOscillator();
      const gain = ctx.createGain();

      osc.type = "sine";
      osc.frequency.value = BEEP_HZ;

      // Short envelope, so it clicks like a metronome rather than blipping.
      gain.gain.setValueAtTime(0, at);
      gain.gain.linearRampToValueAtTime(peak, at + 0.004);
      gain.gain.exponentialRampToValueAtTime(0.0008, at + BEEP_LEN);

      osc.connect(gain);
      gain.connect(ctx.destination);
      osc.start(at);
      osc.stop(at + BEEP_LEN + 0.02);

      this.countInVoices.push(osc);
      osc.onended = () => {
        gain.disconnect();
        this.countInVoices = this.countInVoices.filter((v) => v !== osc);
      };
    }

    cancelCountIn() {
      this.countInVoices.forEach((osc) => {
        try { osc.stop(); } catch (e) {}
      });
      this.countInVoices = [];
    }

    /**
     * Rolls the count and the music together, from the count start until a few
     * seconds past the head, so the beeps can be lined up against where the
     * song actually comes in. Never records, and puts the playhead back after.
     */
    previewCountIn() {
      if (this.previewTimer) {
        this.stopPreview();
        this.pause();
        this.restoreAfterPreview();
        return;
      }

      const ctx = this.ensureAudioCtx();
      this.cancelCountIn();

      if (!this.track1Buffer) {
        this.scheduleCountIn(ctx.currentTime + 0.08, this.countInStart); // beeps alone
        return;
      }

      this.previewResumeAt = this.playhead;
      this.previewWasArmed = this.isArmed;
      this.isArmed = false; // a preview must never punch in

      this.play(this.countInStart);
      this.scheduleCountIn(this.contextStartTime, this.startOffset);

      const end = Math.max(this.countInStart + PREVIEW_SECONDS, PREVIEW_MIN_AFTER_HEAD);
      this.previewTimer = setTimeout(() => {
        this.previewTimer = null;
        this.pause();
        this.restoreAfterPreview();
      }, (end - this.startOffset) * 1000);

      this.render();
    }

    restoreAfterPreview() {
      this.playhead = this.previewResumeAt || 0;
      this.isArmed = this.previewWasArmed || false;
      this.previewWasArmed = false;
      this.render();
    }

    stopPreview() {
      clearTimeout(this.previewTimer);
      this.previewTimer = null;
    }

    // ---------- count in settings ----------

    openCountInModal() {
      el.countInModal.hidden = false;
      this.renderCountInModal();
    }

    closeCountInModal() {
      el.countInModal.hidden = true;
      if (this.previewTimer) {
        this.stopPreview();
        this.pause();
        this.restoreAfterPreview();
      }
      this.cancelCountIn();
    }

    /** Commits whatever is half-typed before a +/- press moves the value. */
    commitPendingInput() {
      const active = document.activeElement;
      if (active === el.bpmInput || active === el.countStartInput) active.blur();
    }

    commitBpm() {
      const typed = parseInt(el.bpmInput.value, 10);
      if (Number.isFinite(typed)) this.countInBpm = clamp(typed, BPM_MIN, BPM_MAX);
      el.bpmInput.value = String(this.countInBpm); // show the clamped value back
      this.renderCountInModal();
    }

    commitCountStart() {
      const typed = parseFloat(el.countStartInput.value);
      if (Number.isFinite(typed)) {
        this.countInStart = toMs(clamp(typed, -COUNT_START_LIMIT, COUNT_START_LIMIT));
      }
      el.countStartInput.value = this.countInStart.toFixed(3);
      this.renderCountInModal();
    }

    nudgeCountVolume(direction) {
      this.commitPendingInput();
      this.countInVolume = clamp(this.countInVolume + direction * COUNT_VOL_STEP, 0, 1);
      this.renderCountInModal();
    }

    nudgeBpm(direction) {
      this.commitPendingInput();
      this.countInBpm = clamp(this.countInBpm + direction, BPM_MIN, BPM_MAX);
      this.renderCountInModal();
    }

    nudgeBeats(direction) {
      this.countInBeats = clamp(this.countInBeats + direction, BEATS_MIN, BEATS_MAX);
      this.renderCountInModal();
    }

    nudgeCountStart(direction) {
      this.commitPendingInput();
      const next = this.countInStart + direction * COUNT_START_STEP;
      this.countInStart = toMs(clamp(next, -COUNT_START_LIMIT, COUNT_START_LIMIT));
      this.renderCountInModal();
    }

    renderCountInModal() {
      // Leave a field alone while it is being typed into.
      if (document.activeElement !== el.bpmInput) el.bpmInput.value = String(this.countInBpm);
      if (document.activeElement !== el.countStartInput) {
        el.countStartInput.value = this.countInStart.toFixed(3);
      }
      el.beatsValue.textContent = String(this.countInBeats);
      el.countVolValue.textContent = Math.round(this.countInVolume * 100) + " %";

      const last = this.countInStart + (this.countInBeats - 1) * (60 / this.countInBpm);
      el.countInSummary.textContent =
        `先頭を基準にした位置。${this.countInStart.toFixed(3)} 秒から ${this.countInBeats} 拍、` +
        `最後の拍は ${last >= 0 ? "+" : ""}${last.toFixed(3)} 秒。`;
    }

    // ---------- input level meter ----------

    buildMeter() {
      for (let i = 0; i < METER_SEGMENTS; i++) {
        const seg = document.createElement("span");
        seg.className = "meter-seg";
        if (i >= METER_CLIP_FROM) seg.classList.add("clip");
        else if (i >= METER_WARN_FROM) seg.classList.add("warn");
        el.meter.appendChild(seg);
        this.meterSegments.push(seg);
      }
    }

    /**
     * Taps the mic ahead of the monitoring path, so the meter reads the input
     * whenever the mic is open — including while armed, before tape rolls.
     */
    startMeter() {
      if (this.meterRaf) return;
      el.meterLabel.classList.add("live");

      const tick = () => {
        this.analyser.getFloatTimeDomainData(this.analyserData);

        let peak = 0;
        for (let i = 0; i < this.analyserData.length; i++) {
          const v = Math.abs(this.analyserData[i]);
          if (v > peak) peak = v;
        }

        this.updateMeter(peak);
        this.meterRaf = requestAnimationFrame(tick);
      };
      this.meterRaf = requestAnimationFrame(tick);
    }

    updateMeter(instant) {
      // Jump straight to a louder reading, ease back down from a quieter one.
      this.meterLevel = instant > this.meterLevel ? instant : this.meterLevel * 0.88;

      const now = performance.now();
      if (instant >= this.meterPeak) {
        this.meterPeak = instant;
        this.meterPeakAt = now;
      } else if (now - this.meterPeakAt > METER_PEAK_HOLD_MS) {
        this.meterPeak = Math.max(this.meterLevel, this.meterPeak - 0.015);
      }

      const lit = Math.round(ampToNorm(this.meterLevel) * METER_SEGMENTS);
      const peakIndex = Math.ceil(ampToNorm(this.meterPeak) * METER_SEGMENTS) - 1;

      for (let i = 0; i < METER_SEGMENTS; i++) {
        const seg = this.meterSegments[i];
        seg.classList.toggle("on", i < lit);
        seg.classList.toggle("peak", i === peakIndex && peakIndex >= 0);
      }
    }

    // ---------- mix controls ----------

    applyBalance() {
      if (!this.musicGain) return;
      const t = (this.balance + 1) / 2; // 0..1
      const musicVol = Math.cos((t * Math.PI) / 2);
      const guitarVol = Math.sin((t * Math.PI) / 2);
      this.musicGain.gain.value = musicVol;
      this.guitarGain.gain.value = guitarVol;
    }

    applyPan() {
      if (!this.guitarPanner) return;
      this.guitarPanner.pan.value = this.pan;
    }

    // ---------- rendering ----------

    updatePlayIcon() {
      el.playIcon.innerHTML = this.isPlaying ? ICON_PAUSE : ICON_PLAY;
    }

    render() {
      el.timeDisplay.textContent = formatTime(this.getPlayhead());
      el.markerADisplay.textContent = "A " + (this.markerA != null ? formatTime(this.markerA) : "--:--.-");
      el.markerBDisplay.textContent = "B " + (this.markerB != null ? formatTime(this.markerB) : "--:--.-");

      el.dotA.classList.toggle("set", this.markerA != null);
      el.dotB.classList.toggle("set", this.markerB != null);

      el.recMark.classList.toggle("has-data", this.track2HasData);

      el.countInPreviewBtn.textContent = this.previewTimer ? "STOP" : "PREVIEW";

      el.countInBtn.classList.toggle("on", this.countInEnabled);
      el.dotCountIn.classList.toggle("set", this.countInEnabled);
      el.countInState.textContent = this.countInEnabled ? "ON" : "OFF";

      // A set marker turns into its own play-from button.
      el.markerALabel.textContent = this.markerA != null ? "▶A" : "A";
      el.markerBLabel.textContent = this.markerB != null ? "▶B" : "B";

      el.loopABBtn.classList.toggle("active", this.loopAB);
      el.loopABBtn.disabled = !this.track1Buffer || this.markerA == null || this.markerB == null;

      el.recBtn.classList.toggle("recording", this.isRecording);
      el.recBtn.classList.toggle("armed", this.isArmed);

      this.renderScrubStage(el.rewindBtn, -1);
      this.renderScrubStage(el.ffBtn, 1);

      el.track2MuteBtn.classList.toggle("on", !this.track2Muted);
      el.dotTrack2.classList.toggle("set", !this.track2Muted);
      el.track2State.textContent = this.track2Muted ? "MUTED" : "ON";

      el.monitorBtn.classList.toggle("on", !this.monitorMuted);
      el.dotMonitor.classList.toggle("set", !this.monitorMuted);
      el.monitorState.textContent = this.monitorMuted ? "MUTED" : "ON";

      const ms = Math.round(this.track2Offset * 1000);
      el.offsetReadout.textContent = (ms > 0 ? "+" : "") + ms + " ms";
      el.offsetReadout.classList.toggle("zero", ms === 0);
      el.offsetMinusBtn.disabled = !this.track2Buffer;
      el.offsetPlusBtn.disabled = !this.track2Buffer;
    }

    renderScrubStage(button, direction) {
      const active = this.scrubDirection === direction ? this.scrubStage : 0;
      for (let i = 1; i <= SCRUB_RATES.length; i++) {
        button.classList.toggle("scrub-" + i, active === i);
      }
    }

    setStatus(msg, clearAfterMs) {
      el.statusMsg.textContent = msg;
      clearTimeout(this.statusTimer);
      if (clearAfterMs) {
        this.statusTimer = setTimeout(() => {
          if (el.statusMsg.textContent === msg) el.statusMsg.textContent = "";
        }, clearAfterMs);
      }
    }
  }

  function clamp(value, min, max) {
    return Math.max(min, Math.min(max, value));
  }

  /** Snaps to whole milliseconds, keeping repeated nudges free of float drift. */
  function toMs(seconds) {
    return Math.round(seconds * 1000) / 1000;
  }

  function formatTime(seconds) {
    if (!isFinite(seconds)) seconds = 0;
    const sign = seconds < 0 ? "-" : ""; // the count-in runs before the head
    const abs = Math.abs(seconds);
    const mm = Math.floor(abs / 60);
    const ss = Math.floor(abs % 60);
    const t = Math.floor((abs * 10) % 10);
    return `${sign}${pad2(mm)}:${pad2(ss)}.${t}`;
  }

  /** Maps a 0..1 amplitude onto the meter's dB scale. */
  function ampToNorm(amp) {
    if (amp <= 0) return 0;
    const db = 20 * Math.log10(amp);
    if (db <= METER_FLOOR_DB) return 0;
    return Math.min(1, (db - METER_FLOOR_DB) / -METER_FLOOR_DB);
  }

  function pad2(n) {
    return n < 10 ? "0" + n : String(n);
  }

  window.tapeRecorderApp = new TapeRecorder();
})();
