(() => {
  "use strict";

  const FPS = 24;
  const SPIN_SPEED = 0.6;
  const TILT = 0.30;
  const CAM_DIST = 4.0;
  const PIVOT_Y = 0.2;
  const MESSAGE = "HAPPY 16TH BIRTHDAY, LEYLEY! i hope you like it.";
  const NUM_HEARTS = 18;

  const BLUE = [17, 18, 19, 20, 21, 25, 26, 27, 32, 33, 38, 39];
  const BLUE_CENTER = [17, 18, 19, 20, 21, 27, 33];
  const GREENS = [22, 28, 28, 34, 35, 71, 77, 114];
  const PAPER = [101, 144, 187, 223, 230, 231];
  const RIBBON = [88, 125, 161, 197, 204, 211];
  const HEART_COLORS = [161, 197, 204, 205, 211, 218];
  const MSG_COLORS = [161, 168, 205, 211, 218, 225, 218, 211, 205, 168];
  const SHADE = ".:-=+*%@";
  const PETAL_SHADE = "+*#%";
  const DISC_TYPES = [
    [BLUE, BLUE_CENTER, 13],
    [BLUE, BLUE_CENTER, 8],
    [BLUE, BLUE_CENTER, 6],
    [BLUE, BLUE_CENTER, 7],
    [BLUE, BLUE_CENTER, 12],
    [BLUE, BLUE_CENTER, 9],
  ];

  const canvas = document.getElementById("bouquet");
  const ctx = canvas.getContext("2d", { alpha: false });
  const message = document.getElementById("birthday-message");
  const motionStatus = document.getElementById("motion-status");
  const reducedMotion = window.matchMedia("(prefers-reduced-motion: reduce)");
  const light = norm([-0.45, 0.6, 0.66]);
  const xtermCache = new Map();

  let layout = null;
  let scene = null;
  let hearts = [];
  let startedAt = 0;
  let elapsedOffset = 0;
  let lastFrame = 0;
  let lastMessageShift = -1;
  let playing = !reducedMotion.matches;
  let frameHandle = 0;

  function norm(v) {
    const length = Math.sqrt(v[0] ** 2 + v[1] ** 2 + v[2] ** 2) || 1;
    return [v[0] / length, v[1] / length, v[2] / length];
  }

  function cross(a, b) {
    return [
      a[1] * b[2] - a[2] * b[1],
      a[2] * b[0] - a[0] * b[2],
      a[0] * b[1] - a[1] * b[0],
    ];
  }

  function add(p, d, k) {
    return [p[0] + d[0] * k, p[1] + d[1] * k, p[2] + d[2] * k];
  }

  function seededRandom(seed) {
    const size = 624;
    const state = new Uint32Array(size);
    state[0] = 19650218;
    for (let i = 1; i < size; i += 1) {
      const previous = state[i - 1] ^ (state[i - 1] >>> 30);
      state[i] = (Math.imul(previous, 1812433253) + i) >>> 0;
    }

    const key = [seed >>> 0];
    let i = 1;
    let j = 0;
    for (let k = Math.max(size, key.length); k > 0; k -= 1) {
      if (i >= size) {
        state[0] = state[size - 1];
        i = 1;
      }
      const previous = state[i - 1] ^ (state[i - 1] >>> 30);
      state[i] = (state[i] ^ Math.imul(previous, 1664525)) + key[j] + j;
      state[i] >>>= 0;
      i += 1;
      j += 1;
      if (j >= key.length) j = 0;
    }

    for (let k = size - 1; k > 0; k -= 1) {
      if (i >= size) {
        state[0] = state[size - 1];
        i = 1;
      }
      const previous = state[i - 1] ^ (state[i - 1] >>> 30);
      state[i] = (state[i] ^ Math.imul(previous, 1566083941)) - i;
      state[i] >>>= 0;
      i += 1;
    }
    state[0] = 0x80000000;
    let index = size;

    function nextUint32() {
      if (index >= size) {
        for (let k = 0; k < size - 397; k += 1) {
          const y = (state[k] & 0x80000000) | (state[k + 1] & 0x7fffffff);
          state[k] = state[k + 397] ^ (y >>> 1) ^ ((y & 1) ? 0x9908b0df : 0);
        }
        for (let k = size - 397; k < size - 1; k += 1) {
          const y = (state[k] & 0x80000000) | (state[k + 1] & 0x7fffffff);
          state[k] = state[k + (397 - size)] ^ (y >>> 1) ^ ((y & 1) ? 0x9908b0df : 0);
        }
        const y = (state[size - 1] & 0x80000000) | (state[0] & 0x7fffffff);
        state[size - 1] = state[396] ^ (y >>> 1) ^ ((y & 1) ? 0x9908b0df : 0);
        index = 0;
      }

      let value = state[index];
      index += 1;
      value ^= value >>> 11;
      value ^= (value << 7) & 0x9d2c5680;
      value ^= (value << 15) & 0xefc60000;
      value ^= value >>> 18;
      return value >>> 0;
    }

    return () => {
      const high = nextUint32() >>> 5;
      const low = nextUint32() >>> 6;
      return (high * 67108864 + low) / 9007199254740992;
    };
  }

  function uniform(random, low, high) {
    return low + random() * (high - low);
  }

  function choose(random, values) {
    return values[Math.floor(random() * values.length)];
  }

  function buildScene() {
    const random = seededRandom(21);
    const points = [];
    const flowers = [];
    const babies = [];
    const sparkles = [];
    const neck = [0.0, -0.12, 0.0];
    const center = [0.0, 0.12, 0.0];
    const golden = Math.PI * (3 - Math.sqrt(5));
    const heads = [];

    for (let i = 0; i < 10; i += 1) {
      const elevation = (88 - 60 * Math.sqrt(i / 9)) * Math.PI / 180;
      const azimuth = i * golden;
      const direction = [
        Math.cos(elevation) * Math.cos(azimuth),
        Math.sin(elevation),
        Math.cos(elevation) * Math.sin(azimuth),
      ];
      const position = add(center, direction, 0.64 * uniform(random, 0.92, 1.05));
      heads.push([position, norm(direction)]);
    }

    const tulipSlots = new Set([3, 8]);
    let discIndex = 0;
    for (let index = 0; index < heads.length; index += 1) {
      const [position, axis] = heads[index];
      const base = add(position, axis, -0.03);
      for (let j = 0; j < 70; j += 1) {
        const t = j / 69;
        const p = [
          base[0] + (neck[0] - base[0]) * t,
          base[1] + (neck[1] - base[1]) * t,
          base[2] + (neck[2] - base[2]) * t,
        ];
        points.push([p[0], p[1], p[2], axis[0], 0, axis[2], GREENS, -0.15, true, null]);
      }

      if (tulipSlots.has(index)) {
        flowers.push([position, "tulip", BLUE, null, 0, 0.11, uniform(random, 0, 6.28)]);
      } else {
        const [petals, centerPalette, petalCount] = DISC_TYPES[discIndex % DISC_TYPES.length];
        discIndex += 1;
        flowers.push([
          position,
          "disc",
          petals,
          centerPalette,
          petalCount,
          uniform(random, 0.12, 0.14),
          uniform(random, 0, 6.28),
        ]);
      }
    }

    for (let i = 0; i < 8; i += 1) {
      const angle = (i + 0.4) / 8 * 2 * Math.PI;
      const c = Math.cos(angle);
      const s = Math.sin(angle);
      const base = [0.26 * c, 0.30, 0.26 * s];
      const direction = norm([c, 0.15, s]);
      const side = [-s, 0, c];
      const normal = norm(cross(side, direction));
      const length = 0.30;
      const width = 0.07;
      for (let ti = 0; ti < 32; ti += 1) {
        const t = ti / 31;
        for (let wi = -5; wi <= 5; wi += 1) {
          const w = wi / 5;
          const curl = 0.025 * w * w;
          const p = [
            base[0] + direction[0] * length * t + side[0] * width * Math.sin(Math.PI * t) * w + normal[0] * curl,
            base[1] + direction[1] * length * t - 0.10 * t * t + normal[1] * curl,
            base[2] + direction[2] * length * t + side[2] * width * Math.sin(Math.PI * t) * w + normal[2] * curl,
          ];
          points.push([p[0], p[1], p[2], normal[0], normal[1], normal[2], GREENS, wi === 0 ? -0.25 : 0, true, null]);
        }
      }
    }

    const y0 = -0.20;
    const y1 = 0.30;
    const r0 = 0.06;
    const r1 = 0.36;
    const slope = (r1 - r0) / (y1 - y0);
    for (let i = 0; i < 50; i += 1) {
      const t = i / 49;
      const radius = r0 + (r1 - r0) * t;
      const count = Math.max(8, Math.floor(170 * radius));
      for (let j = 0; j < count; j += 1) {
        const phase = (j + random()) / count * 2 * Math.PI;
        const c = Math.cos(phase);
        const s = Math.sin(phase);
        let y = y0 + (y1 - y0) * t;
        if (t > 0.9) y += 0.03 * Math.sin(9 * phase);
        const fold = 0.3 * (Math.abs(Math.sin(5 * phase)) - 0.6);
        const normal = norm([c, -slope, s]);
        points.push([radius * c, y, radius * s, normal[0], normal[1], normal[2], PAPER, fold, false, null]);
      }
    }

    for (let i = 0; i < 7; i += 1) {
      const angle = i / 7 * 2 * Math.PI;
      const sx = 0.025 * Math.cos(angle);
      const sz = 0.025 * Math.sin(angle);
      for (let j = 0; j < 40; j += 1) {
        const t = j / 39;
        points.push([
          sx * (1 + 1.2 * t), -0.20 - 0.30 * t, sz * (1 + 1.2 * t),
          Math.cos(angle), 0, Math.sin(angle), GREENS, -0.1, true, null,
        ]);
      }
    }

    const by = -0.12;
    const ribbonRadius = r0 + slope * (by - y0) + 0.01;
    for (let j = 0; j < 90; j += 1) {
      const phase = j / 90 * 2 * Math.PI;
      for (const dy of [-0.012, 0, 0.012]) {
        points.push([
          ribbonRadius * Math.cos(phase), by + dy, ribbonRadius * Math.sin(phase),
          Math.cos(phase), 0, Math.sin(phase), RIBBON, 0, false, null,
        ]);
      }
    }

    const knot = [0, by, ribbonRadius + 0.01];
    for (const side of [-1, 1]) {
      for (let j = 0; j < 70; j += 1) {
        const angle = j / 70 * 2 * Math.PI;
        const lx = side * (0.07 + 0.07 * Math.cos(angle));
        const ly = 0.04 * Math.sin(angle) + 0.02 * (0.07 + 0.07 * Math.cos(angle)) / 0.14;
        for (const fill of [1.0, 0.7]) {
          points.push([
            knot[0] + lx * fill, knot[1] + ly * fill, knot[2] + 0.01,
            side * 0.3, 0.2, 0.93, RIBBON, 0.1, true, null,
          ]);
        }
      }
      for (let j = 0; j < 30; j += 1) {
        const t = j / 29;
        points.push([
          knot[0] + side * 0.06 * t, knot[1] - 0.15 * t, knot[2] + 0.015,
          side * 0.2, 0, 0.98, RIBBON, -0.05 + 0.05 * Math.sin(t * 9), true, null,
        ]);
      }
    }
    for (const dx of [-0.01, 0, 0.01]) {
      points.push([dx, by, knot[2] + 0.02, 0, 0, 1, RIBBON, 0.2, true, "@"]);
    }

    for (let i = 0; i < 90; i += 1) {
      const angle = random() * 2 * Math.PI;
      const elevation = uniform(random, 0.3, 1.4);
      const radius = uniform(random, 0.40, 0.58);
      babies.push([
        radius * Math.cos(angle) * Math.cos(elevation),
        center[1] + radius * Math.sin(elevation),
        radius * Math.sin(angle) * Math.cos(elevation),
        uniform(random, 0, 6.28),
      ]);
    }

    for (let i = 0; i < 30; i += 1) {
      const angle = random() * 2 * Math.PI;
      const radius = uniform(random, 0.75, 0.95);
      sparkles.push([
        radius * Math.cos(angle), uniform(random, -0.3, 1.0), radius * Math.sin(angle),
        uniform(random, 0, 6.28), uniform(random, 1.5, 4.0),
      ]);
    }

    return { points, flowers, babies, sparkles };
  }

  function xtermColor(index) {
    if (xtermCache.has(index)) return xtermCache.get(index);
    const base16 = [
      "#000000", "#800000", "#008000", "#808000", "#000080", "#800080", "#008080", "#c0c0c0",
      "#808080", "#ff0000", "#00ff00", "#ffff00", "#0000ff", "#ff00ff", "#00ffff", "#ffffff",
    ];
    let color;
    if (index < 16) {
      color = base16[index];
    } else if (index < 232) {
      const levels = [0, 95, 135, 175, 215, 255];
      const n = index - 16;
      color = `rgb(${levels[Math.floor(n / 36)]},${levels[Math.floor(n / 6) % 6]},${levels[n % 6]})`;
    } else {
      const gray = 8 + (index - 232) * 10;
      color = `rgb(${gray},${gray},${gray})`;
    }
    xtermCache.set(index, color);
    return color;
  }

  function updateHearts(dt) {
    while (hearts.length < NUM_HEARTS) {
      hearts.push([
        Math.random(), 1 + Math.random(), uniform(Math.random, 0.03, 0.08),
        uniform(Math.random, 0, 6.28), choose(Math.random, HEART_COLORS),
      ]);
    }
    for (const heart of hearts) {
      heart[1] -= heart[2] * dt;
      if (heart[1] < 0) {
        heart[0] = Math.random();
        heart[1] = 1;
        heart[4] = choose(Math.random, HEART_COLORS);
      }
    }
  }

  function makeProjection(time) {
    const { cols, viewRows, scale } = layout;
    const sxScale = scale * 2;
    const cx = cols / 2;
    const cy = 1 + 0.78 * scale;
    const angle = time * SPIN_SPEED;
    const ca = Math.cos(angle);
    const sa = Math.sin(angle);
    const ct = Math.cos(TILT);
    const st = Math.sin(TILT);

    function rotate(x, y, z) {
      const xr = x * ca - z * sa;
      const zr = x * sa + z * ca;
      const yp = y - PIVOT_Y;
      const yt = yp * ct - zr * st;
      const zt = yp * st + zr * ct;
      const factor = CAM_DIST / (CAM_DIST - zt);
      return [xr, yt, zt, factor];
    }

    return {
      angle, ca, sa, ct, st, cx, cy, scale, sxScale, viewRows,
      point(x, y, z) {
        const [xr, yt, zt, factor] = rotate(x, y, z);
        return [Math.trunc(cx + xr * factor * sxScale), Math.trunc(cy - yt * factor * scale), zt];
      },
      flower(x, y, z) {
        const [xr, yt, zt, factor] = rotate(x, y, z);
        return [cx + xr * factor * sxScale, cy - yt * factor * scale, zt, factor];
      },
    };
  }

  function render(time, dt) {
    if (!layout || !scene) return;
    const { cols, viewRows, cellWidth, cellHeight } = layout;
    updateHearts(dt);
    ctx.fillStyle = "#050914";
    ctx.fillRect(0, 0, canvas.clientWidth, canvas.clientHeight);

    const chars = Array.from({ length: viewRows }, () => new Array(cols).fill(" "));
    const colors = Array.from({ length: viewRows }, () => new Array(cols).fill(0));
    const zBuffer = Array.from({ length: viewRows }, () => new Float32Array(cols).fill(-1e9));
    const projection = makeProjection(time);
    const { ca, sa, ct, st } = projection;

    function plot(col, row, z, character, color) {
      if (row >= 0 && row < viewRows && col >= 0 && col < cols && z > zBuffer[row][col]) {
        zBuffer[row][col] = z;
        chars[row][col] = character;
        colors[row][col] = color;
      }
    }

    for (const heart of hearts) {
      const rawColumn = Math.trunc((heart[0] + 0.015 * Math.sin(time * 1.2 + heart[3])) * cols);
      const col = ((rawColumn % cols) + cols) % cols;
      plot(col, Math.trunc(heart[1] * viewRows), -50, "♥", heart[4]);
    }

    for (const point of scene.points) {
      const [x, y, z, nx, ny, nz, palette, tone, twoSided, override] = point;
      const [col, row, zt] = projection.point(x, y, z);
      const nxr = nx * ca - nz * sa;
      const nzr = nx * sa + nz * ca;
      const nyt = ny * ct - nzr * st;
      const nzt = ny * st + nzr * ct;
      let dot = nxr * light[0] + nyt * light[1] + nzt * light[2];
      if (twoSided && dot < 0) dot = -dot * 0.55;
      const brightness = Math.min(0.999, Math.max(0, 0.25 + 0.75 * Math.max(0, dot) + tone));
      const character = override === "P"
        ? PETAL_SHADE[Math.floor(brightness * PETAL_SHADE.length)]
        : (override || SHADE[Math.floor(brightness * SHADE.length)]);
      plot(col, row, zt, character, palette[Math.floor(brightness * palette.length)]);
    }

    for (const flower of scene.flowers) {
      const [position, kind, palette, centerPalette, petalCount, radius, seed] = flower;
      const [fx, fy, zt, factor] = projection.flower(position[0], position[1], position[2]);
      const rx = radius * factor * projection.sxScale;
      const ry = radius * factor * projection.scale;
      const dim = -0.4 * (1 - Math.min(1, Math.max(0, (zt + 0.6) / 1.2)));
      const rotation = seed + projection.angle * 0.7;
      for (let row = Math.floor(fy - ry) - 1; row < Math.floor(fy + ry) + 2; row += 1) {
        const dy = (row + 0.5 - fy) / ry;
        for (let col = Math.floor(fx - rx) - 1; col < Math.floor(fx + rx) + 2; col += 1) {
          const dx = (col + 0.5 - fx) / rx;
          if (kind === "disc") {
            const distance = Math.sqrt(dx * dx + dy * dy);
            if (distance > 1) continue;
            if (distance < 0.3) {
              const brightness = Math.min(0.999, Math.max(0, 0.55 - 0.35 * dx - 0.35 * dy + dim));
              plot(col, row, zt + 0.06, distance < 0.17 ? "@" : "o", centerPalette[Math.floor(brightness * centerPalette.length)]);
              continue;
            }
            const phase = Math.atan2(dy, dx);
            const reach = 0.32 + 0.68 * Math.abs(Math.cos(petalCount * (phase + rotation) / 2)) ** 0.7;
            if (distance > reach) continue;
            const edge = distance > reach - 0.14 ? -0.22 : 0;
            const brightness = Math.min(0.999, Math.max(0, 0.62 - 0.22 * dx - 0.28 * dy + 0.12 * distance + edge + dim));
            plot(col, row, zt + 0.04 * (1 - distance), PETAL_SHADE[Math.floor(brightness * PETAL_SHADE.length)], palette[Math.floor(brightness * palette.length)]);
          } else {
            const v = (1 - dy) / 2;
            if (v < 0 || v > 1) continue;
            const halfWidth = 0.62 * Math.sin(Math.PI * 0.5 * Math.min(1, v * 1.5 + 0.05));
            if (halfWidth <= 0 || Math.abs(dx) > halfWidth) continue;
            const xn = dx / halfWidth;
            if (v > 0.72 + 0.28 * Math.cos(1.5 * Math.PI * xn) ** 2) continue;
            const seam = Math.abs(Math.abs(xn) - 0.33) < 0.12 && v > 0.3 ? -0.25 : 0;
            const brightness = Math.min(0.999, Math.max(0, 0.55 - 0.3 * xn + 0.1 * v + seam + dim));
            plot(col, row, zt + 0.03, PETAL_SHADE[Math.floor(brightness * PETAL_SHADE.length)], palette[Math.floor(brightness * palette.length)]);
          }
        }
      }
    }

    for (const [x, y, z, phase] of scene.babies) {
      const [col, row, zt] = projection.point(x, y, z);
      const star = Math.sin(time * 2 + phase) > 0.6;
      plot(col, row, zt + 0.02, star ? "*" : "·", star ? 231 : 255);
    }

    for (const [x, y, z, phase, speed] of scene.sparkles) {
      const [col, row, zt] = projection.point(x, y, z);
      const twinkle = Math.sin(time * speed + phase);
      if (twinkle > 0.85) plot(col, row, zt, "*", 231);
      else if (twinkle > 0.4) plot(col, row, zt, "+", 225);
      else if (twinkle > 0) plot(col, row, zt, "·", 218);
    }

    const pixelFont = Math.max(8, cellHeight * 0.8);
    ctx.font = `bold ${pixelFont}px "Courier New", monospace`;
    ctx.textBaseline = "alphabetic";
    for (let row = 0; row < viewRows; row += 1) {
      let previousColor = -1;
      for (let col = 0; col < cols; col += 1) {
        const character = chars[row][col];
        if (character === " ") continue;
        const color = colors[row][col];
        if (color !== previousColor) {
          ctx.fillStyle = xtermColor(color);
          previousColor = color;
        }
        ctx.fillText(character, col * cellWidth, row * cellHeight + cellHeight * 0.83);
      }
    }

  }

  function updateMessageColors(shift) {
    if (shift === lastMessageShift) return;
    lastMessageShift = shift;
    const fragment = document.createDocumentFragment();
    for (let i = 0; i < MESSAGE.length; i += 1) {
      const letter = document.createElement("span");
      letter.textContent = MESSAGE[i];
      letter.style.color = xtermColor(MSG_COLORS[(i + shift) % MSG_COLORS.length]);
      fragment.appendChild(letter);
    }
    message.replaceChildren(fragment);
  }

  function resize() {
    const rect = canvas.getBoundingClientRect();
    const dpr = Math.min(window.devicePixelRatio || 1, 2);
    const width = Math.max(1, rect.width);
    const height = Math.max(1, rect.height);
    canvas.width = Math.round(width * dpr);
    canvas.height = Math.round(height * dpr);
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);

    const cellHeight = Math.max(11, Math.min(18, width / 38));
    const cellWidth = cellHeight / 2;
    const cols = Math.max(20, Math.floor(width / cellWidth));
    const rows = Math.max(12, Math.floor(height / cellHeight) + 2);
    const viewRows = rows - 2;
    const scale = Math.max(1, Math.min((viewRows - 2) / 1.45, (cols - 2) / 2.7));
    layout = { cols, viewRows, cellWidth, cellHeight, scale };
    const now = performance.now() / 1000;
    render(playing ? elapsedOffset + Math.max(0, now - startedAt) : elapsedOffset, 0);
  }

  function animate(now) {
    frameHandle = 0;
    if (!playing) return;
    if (now - lastFrame >= 1000 / FPS - 1) {
      const time = elapsedOffset + Math.max(0, now / 1000 - startedAt);
      const dt = lastFrame ? (now - lastFrame) / 1000 : 1 / FPS;
      lastFrame = now;
      render(time, dt);
      updateMessageColors(Math.floor(time * 6));
    }
    frameHandle = window.requestAnimationFrame(animate);
  }

  function setPlaying(nextPlaying, announce = true) {
    if (playing === nextPlaying) return;
    playing = nextPlaying;
    if (playing) {
      startedAt = performance.now() / 1000;
      lastFrame = 0;
      if (announce) motionStatus.textContent = "Animation resumed.";
      frameHandle = window.requestAnimationFrame(animate);
    } else {
      elapsedOffset += Math.max(0, performance.now() / 1000 - startedAt);
      if (frameHandle) window.cancelAnimationFrame(frameHandle);
      frameHandle = 0;
      if (announce) motionStatus.textContent = "Animation paused.";
    }
  }

  scene = buildScene();
  updateHearts(0);
  updateMessageColors(0);
  if (playing) startedAt = performance.now() / 1000;
  resize();
  if (playing) {
    frameHandle = window.requestAnimationFrame(animate);
  } else {
    motionStatus.textContent = "Animation paused because reduced motion is enabled. Press P or Space to resume.";
  }

  window.addEventListener("resize", resize, { passive: true });
  reducedMotion.addEventListener?.("change", (event) => {
    if (event.matches) setPlaying(false, false);
  });

  window.addEventListener("keydown", (event) => {
    if (event.repeat || event.altKey || event.ctrlKey || event.metaKey) return;
    if (event.key.toLowerCase() === "p" || event.code === "Space") {
      event.preventDefault();
      setPlaying(!playing);
    }
  });
})();
