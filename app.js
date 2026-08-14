(() => {
  "use strict";

  const SEEK_STEP = 5; // seconds jumped per rewind/ff click
  const SCRUB_INTERVAL_MS = 150; // press-and-hold scrub tick
  const REC_BUFFER_SIZE = 2048;
  const ERASE_HOLD_MS = 800; // hold REC this long to erase the recorded track
  const RIPPLE_MS = 1500; // covers the last ripple's delay + duration

  const el = {
    app: document.getElementById("app"),
    trackLabel: document.getElementById("trackLabel"),
    loadBtn: document.getElementById("loadBtn"),
    fileInput: document.getElementById("fileInput"),
    timeDisplay: document.getElementById("timeDisplay"),
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
    dotA: document.getElementById("dotA"),
    dotB: document.getElementById("dotB"),
    loopABBtn: document.getElementById("loopABBtn"),
    playABtn: document.getElementById("playABtn"),
    playBBtn: document.getElementById("playBBtn"),
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
      this.duration = 0;

      this.isPlaying = false;
      this.isRecording = false;
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
      this.monitorConnected = false;

      this.musicGain = null;
      this.guitarGain = null;
      this.guitarPanner = null;

      this.balance = 0;
      this.pan = 0;

      this.rafId = null;
      this.scrubTimer = null;

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
      el.loadBtn.addEventListener("click", () => el.fileInput.click());
      el.fileInput.addEventListener("change", (e) => this.onFileSelected(e));

      el.playBtn.addEventListener("click", () => this.togglePlay());
      this.bindRecButton();

      this.bindScrub(el.rewindBtn, -1);
      this.bindScrub(el.ffBtn, 1);

      el.markerABtn.addEventListener("click", () => this.setMarker("A"));
      el.markerBBtn.addEventListener("click", () => this.setMarker("B"));
      el.loopABBtn.addEventListener("click", () => this.toggleLoopAB());
      el.playABtn.addEventListener("click", () => this.playFromMarker("A"));
      el.playBBtn.addEventListener("click", () => this.playFromMarker("B"));

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
     * Short press punches recording in/out; holding erases the recorded track.
     * The erase suppresses the release so a long press never toggles recording.
     */
    bindRecButton() {
      let timer = null;
      let erased = false;

      const down = (e) => {
        if (el.recBtn.disabled) return;
        e.preventDefault();
        erased = false;
        el.recBtn.classList.add("holding");
        clearTimeout(timer);
        timer = setTimeout(() => {
          erased = true;
          el.recBtn.classList.remove("holding");
          this.eraseTrack2();
        }, ERASE_HOLD_MS);
      };

      const up = () => {
        clearTimeout(timer);
        el.recBtn.classList.remove("holding");
        if (!erased) this.toggleRecord();
        erased = false;
      };

      const cancel = () => {
        clearTimeout(timer);
        el.recBtn.classList.remove("holding");
        erased = false;
      };

      el.recBtn.addEventListener("pointerdown", down);
      el.recBtn.addEventListener("pointerup", up);
      el.recBtn.addEventListener("pointerleave", cancel);
      el.recBtn.addEventListener("pointercancel", cancel);
      el.recBtn.addEventListener("contextmenu", (e) => e.preventDefault());
    }

    bindScrub(button, direction) {
      const step = () => this.seekBy(direction * SEEK_STEP);
      const start = (e) => {
        e.preventDefault();
        step();
        clearInterval(this.scrubTimer);
        this.scrubTimer = setInterval(step, SCRUB_INTERVAL_MS);
      };
      const stop = () => clearInterval(this.scrubTimer);
      button.addEventListener("pointerdown", start);
      button.addEventListener("pointerup", stop);
      button.addEventListener("pointerleave", stop);
      button.addEventListener("pointercancel", stop);
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

        this.playhead = 0;
        this.markerA = null;
        this.markerB = null;
        this.loopAB = false;

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
      [el.playBtn, el.recBtn, el.rewindBtn, el.ffBtn, el.markerABtn, el.markerBBtn, el.loopABBtn, el.playABtn, el.playBBtn].forEach(
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
      src.start(0, Math.max(0, offset));
      this.track1Source = src;
    }

    startTrack2Source(offset) {
      const ctx = this.audioCtx;
      const src = ctx.createBufferSource();
      src.buffer = this.track2Buffer;
      src.connect(this.guitarGain);
      src.start(0, Math.max(0, offset));
      this.track2Source = src;
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
      this.stopSources();

      const startAt = fromSeconds !== null ? fromSeconds : this.playhead;
      this.startOffset = Math.max(0, Math.min(startAt, this.duration));
      this.contextStartTime = ctx.currentTime;
      this.isPlaying = true;

      this.startTrack1Source(this.startOffset);
      if (this.isRecording) {
        this.connectMonitoring();
      } else {
        this.startTrack2Source(this.startOffset);
      }

      this.startClock();
      this.updatePlayIcon();
    }

    pause() {
      if (!this.isPlaying) return;
      this.playhead = this.getPlayhead();
      if (this.isRecording) this.disengageRecording();
      this.stopSources();
      this.isPlaying = false;
      this.stopClock();
      this.updatePlayIcon();
      this.render();
    }

    togglePlay() {
      if (this.isPlaying) this.pause();
      else this.play();
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

    seekBy(delta) {
      if (!this.track1Buffer) return;
      this.seekTo(this.getPlayhead() + delta, this.isPlaying);
    }

    playFromMarker(which) {
      const target = which === "A" ? this.markerA : this.markerB;
      if (target == null) return;
      this.seekTo(target, true);
      if (!this.isPlaying) this.play(target);
    }

    stopAll() {
      this.stopClock();
      this.stopSources();
      this.disengageRecording();
      this.isPlaying = false;
      this.playhead = 0;
      this.updatePlayIcon();
    }

    // ---------- markers ----------

    setMarker(which) {
      const t = this.getPlayhead();
      if (which === "A") this.markerA = t;
      else this.markerB = t;
      this.render();
    }

    toggleLoopAB() {
      if (this.markerA == null || this.markerB == null) return;
      this.loopAB = !this.loopAB;
      this.render();
    }

    // ---------- recording (punch in/out) ----------

    async toggleRecord() {
      if (!this.track1Buffer) return;

      if (this.isRecording) {
        this.disengageRecording();
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

      if (!this.isPlaying) {
        this.isRecording = true;
        this.play();
      } else {
        this.isRecording = true;
        this.stopTrack2Playback();
        this.connectMonitoring();
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

      this.recProcessor = ctx.createScriptProcessor(REC_BUFFER_SIZE, 1, 1);
      this.recSilentGain = ctx.createGain();
      this.recSilentGain.gain.value = 0;
      this.recProcessor.connect(this.recSilentGain);
      this.recSilentGain.connect(ctx.destination);

      this.recProcessor.onaudioprocess = (e) => this.handleRecordProcess(e);
    }

    handleRecordProcess(e) {
      if (!this.isRecording || !this.track2Data) return;
      const input = e.inputBuffer.getChannelData(0);
      const blockStartPlayhead = this.playheadAtContextTime(e.playbackTime);
      const startSample = Math.round(blockStartPlayhead * this.audioCtx.sampleRate);
      const len = this.track2Data.length;

      for (let i = 0; i < input.length; i++) {
        const idx = startSample + i;
        if (idx >= 0 && idx < len) {
          this.track2Data[idx] = input[i];
        }
      }
    }

    connectMonitoring() {
      if (this.monitorConnected) return;
      this.micSourceNode.connect(this.guitarGain);
      this.micSourceNode.connect(this.recProcessor);
      this.monitorConnected = true;
    }

    disconnectMonitoring() {
      if (!this.monitorConnected) return;
      try { this.micSourceNode.disconnect(this.guitarGain); } catch (e) {}
      try { this.micSourceNode.disconnect(this.recProcessor); } catch (e) {}
      this.monitorConnected = false;
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
      this.disconnectMonitoring();
      if (this.isPlaying) {
        this.startTrack2Source(this.getPlayhead());
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

      el.loopABBtn.classList.toggle("active", this.loopAB);
      el.loopABBtn.disabled = !this.track1Buffer || this.markerA == null || this.markerB == null;
      el.playABtn.disabled = !this.track1Buffer || this.markerA == null;
      el.playBBtn.disabled = !this.track1Buffer || this.markerB == null;

      el.recBtn.classList.toggle("recording", this.isRecording);
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

  function formatTime(seconds) {
    if (!isFinite(seconds) || seconds < 0) seconds = 0;
    const mm = Math.floor(seconds / 60);
    const ss = Math.floor(seconds % 60);
    const t = Math.floor((seconds * 10) % 10);
    return `${pad2(mm)}:${pad2(ss)}.${t}`;
  }

  function pad2(n) {
    return n < 10 ? "0" + n : String(n);
  }

  window.tapeRecorderApp = new TapeRecorder();
})();
