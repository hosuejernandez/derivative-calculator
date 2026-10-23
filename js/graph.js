// Canvas grapher: f colored by where it increases / decreases, f' overlay, critical points,
// a tangent line that follows the pointer, and implicit curves F(x, y) = 0.

const COLORS = {
  inc: '#15803d', dec: '#dc2626', flat: '#64748b', deriv: '#7c3aed', curve: '#2563eb',
  grid: '#e5e7eb', axis: '#475569', text: '#334155', tangent: '#f59e0b', point: '#0f172a',
};

function niceStep(span) {
  const raw = span / 8;
  const p = Math.pow(10, Math.floor(Math.log10(raw)));
  const m = raw / p;
  return (m < 1.5 ? 1 : m < 3.5 ? 2 : m < 7.5 ? 5 : 10) * p;
}

const fmtTick = v => {
  const r = Math.round(v * 1e6) / 1e6;
  return Math.abs(r) >= 1e5 || (Math.abs(r) < 1e-3 && r !== 0) ? r.toExponential(1) : `${r}`;
};
const fmtNum = v => (isFinite(v) ? `${Math.round(v * 1000) / 1000}` : 'undefined');

export class Graph {
  constructor(canvas, readout) {
    this.canvas = canvas;
    this.ctx = canvas.getContext('2d');
    this.readout = readout;
    this.view = { x0: -10, x1: 10, y0: -10, y1: 10 };
    this.home = { ...this.view };
    this.data = null;
    this.hover = null;
    this.showDeriv = false;
    this.showTangent = true;
    this.names = { x: 'x', y: 'y' };
    this.bindEvents();
    new ResizeObserver(() => this.draw()).observe(canvas);
  }

  // ----- data -----

  setExplicit({ f, fp, points = [], window = null, xName = 'x', fName = 'f' }) {
    this.data = { kind: 'explicit', f, fp, points };
    this.names = { x: xName, f: fName };
    this.home = this.autoView(window);
    this.view = { ...this.home };
    this.hover = null;
    this.draw();
  }

  setImplicit({ F, slope, xName, yName }) {
    this.data = { kind: 'implicit', F, slope };
    this.names = { x: xName, y: yName };
    this.home = { x0: -7, x1: 7, y0: -7, y1: 7 };
    this.fitSquare(this.home);
    this.view = { ...this.home };
    this.hover = null;
    this.draw();
  }

  clear() { this.data = null; this.draw(); }

  autoView(window) {
    const { f, points } = this.data;
    let x0 = -10, x1 = 10;
    // the y-range is chosen from the "interesting" part of the graph, near the critical points
    let c0 = -5, c1 = 5;
    const px = points.map(p => p.x).filter(isFinite);
    if (window) { x0 = window[0]; x1 = window[1]; const pad = (x1 - x0) * 0.05; x0 -= pad; x1 += pad; c0 = x0; c1 = x1; }
    else if (px.length) {
      const lo = Math.min(...px), hi = Math.max(...px);
      const pad = Math.max(2, (hi - lo) * 0.6);
      x0 = Math.min(lo - pad, -1); x1 = Math.max(hi + pad, 1);
      const core = Math.max(1, (hi - lo) * 0.4);
      c0 = lo - core; c1 = hi + core;
    }
    const ys = [];
    for (let i = 0; i <= 400; i++) { const y = f(c0 + (c1 - c0) * i / 400); if (isFinite(y)) ys.push(y); }
    ys.sort((a, b) => a - b);
    let y0 = -10, y1 = 10;
    if (ys.length > 10) {
      y0 = ys[Math.floor(ys.length * 0.04)]; y1 = ys[Math.ceil(ys.length * 0.96) - 1];
      for (const p of points) if (isFinite(p.y)) { y0 = Math.min(y0, p.y); y1 = Math.max(y1, p.y); }
      y0 = Math.min(y0, 0); y1 = Math.max(y1, 0);
      const pad = Math.max((y1 - y0) * 0.15, 0.5);
      y0 -= pad; y1 += pad;
    }
    return { x0, x1, y0, y1 };
  }

  fitSquare(v) {
    const r = this.canvas.getBoundingClientRect();
    if (!r.width || !r.height) return;
    const cx = (v.x0 + v.x1) / 2, half = (v.y1 - v.y0) / 2 * r.width / r.height;
    v.x0 = cx - half; v.x1 = cx + half;
  }

  reset() { this.view = { ...this.home }; this.draw(); }

  zoom(factor, cx, cy) {
    const v = this.view;
    if (cx === undefined) { cx = (v.x0 + v.x1) / 2; cy = (v.y0 + v.y1) / 2; }
    this.view = { x0: cx + (v.x0 - cx) * factor, x1: cx + (v.x1 - cx) * factor, y0: cy + (v.y0 - cy) * factor, y1: cy + (v.y1 - cy) * factor };
    this.draw();
  }

  // ----- coordinates -----

  sx(x) { return (x - this.view.x0) / (this.view.x1 - this.view.x0) * this.W; }
  sy(y) { return this.H - (y - this.view.y0) / (this.view.y1 - this.view.y0) * this.H; }
  wx(px) { return this.view.x0 + px / this.W * (this.view.x1 - this.view.x0); }
  wy(py) { return this.view.y0 + (this.H - py) / this.H * (this.view.y1 - this.view.y0); }

  // ----- events -----

  bindEvents() {
    const c = this.canvas;
    let drag = null;
    const pos = e => { const r = c.getBoundingClientRect(); return [e.clientX - r.left, e.clientY - r.top]; };
    c.addEventListener('pointerdown', e => {
      const [px, py] = pos(e);
      drag = { px, py, view: { ...this.view }, moved: false };
      c.setPointerCapture(e.pointerId);
    });
    c.addEventListener('pointermove', e => {
      const [px, py] = pos(e);
      if (drag) {
        const dx = (px - drag.px) / this.W * (drag.view.x1 - drag.view.x0);
        const dy = (py - drag.py) / this.H * (drag.view.y1 - drag.view.y0);
        if (Math.abs(px - drag.px) + Math.abs(py - drag.py) > 3) drag.moved = true;
        if (drag.moved && e.pointerType === 'mouse') {
          this.view = { x0: drag.view.x0 - dx, x1: drag.view.x1 - dx, y0: drag.view.y0 + dy, y1: drag.view.y1 + dy };
        }
      }
      this.hover = { px, py };
      this.draw();
    });
    c.addEventListener('pointerup', () => { drag = null; });
    c.addEventListener('pointerleave', e => { if (e.pointerType === 'mouse') { this.hover = null; this.draw(); } });
    c.addEventListener('wheel', e => {
      e.preventDefault();
      const [px, py] = pos(e);
      this.zoom(e.deltaY > 0 ? 1.15 : 1 / 1.15, this.wx(px), this.wy(py));
    }, { passive: false });
  }

  // ----- drawing -----

  draw() {
    const c = this.canvas, dpr = window.devicePixelRatio || 1;
    const r = c.getBoundingClientRect();
    this.W = r.width; this.H = r.height;
    if (!this.W || !this.H) return;
    if (c.width !== Math.round(this.W * dpr) || c.height !== Math.round(this.H * dpr)) {
      c.width = Math.round(this.W * dpr); c.height = Math.round(this.H * dpr);
    }
    const ctx = this.ctx;
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.clearRect(0, 0, this.W, this.H);
    ctx.fillStyle = '#ffffff';
    ctx.fillRect(0, 0, this.W, this.H);
    this.drawGrid();
    if (!this.data) { this.setReadout(''); return; }
    if (this.data.kind === 'explicit') this.drawExplicit();
    else this.drawImplicit();
  }

  drawGrid() {
    const ctx = this.ctx, v = this.view;
    const sx = niceStep(v.x1 - v.x0), sy = niceStep(v.y1 - v.y0);
    ctx.lineWidth = 1;
    ctx.strokeStyle = COLORS.grid;
    ctx.beginPath();
    for (let x = Math.ceil(v.x0 / sx) * sx; x <= v.x1; x += sx) { const p = Math.round(this.sx(x)) + 0.5; ctx.moveTo(p, 0); ctx.lineTo(p, this.H); }
    for (let y = Math.ceil(v.y0 / sy) * sy; y <= v.y1; y += sy) { const p = Math.round(this.sy(y)) + 0.5; ctx.moveTo(0, p); ctx.lineTo(this.W, p); }
    ctx.stroke();
    // axes
    const ax = Math.min(Math.max(this.sy(0), 0), this.H), ay = Math.min(Math.max(this.sx(0), 0), this.W);
    ctx.strokeStyle = COLORS.axis;
    ctx.lineWidth = 1.5;
    ctx.beginPath();
    ctx.moveTo(0, ax); ctx.lineTo(this.W, ax);
    ctx.moveTo(ay, 0); ctx.lineTo(ay, this.H);
    ctx.stroke();
    ctx.fillStyle = COLORS.text;
    ctx.font = '11px system-ui, sans-serif';
    ctx.textAlign = 'center'; ctx.textBaseline = 'top';
    const ly = ax > this.H - 16 ? this.H - 14 : ax + 3;
    for (let x = Math.ceil(v.x0 / sx) * sx; x <= v.x1; x += sx) {
      if (Math.abs(x) < sx / 2) continue;
      ctx.fillText(fmtTick(x), this.sx(x), ly);
    }
    ctx.textAlign = ay > this.W - 40 ? 'right' : 'left'; ctx.textBaseline = 'middle';
    const lx = ay > this.W - 40 ? this.W - 4 : ay + 4;
    for (let y = Math.ceil(v.y0 / sy) * sy; y <= v.y1; y += sy) {
      if (Math.abs(y) < sy / 2) continue;
      ctx.fillText(fmtTick(y), lx, this.sy(y));
    }
  }

  // Polyline of a function of x, split at discontinuities; color(xa, xb) picks each piece's color.
  plot(g, color, width, dash = []) {
    const ctx = this.ctx, n = Math.ceil(this.W * 1.5);
    ctx.lineWidth = width; ctx.setLineDash(dash); ctx.lineJoin = 'round'; ctx.lineCap = 'round';
    let prev = null, cur = null;
    const limit = this.H * 4;
    for (let i = 0; i <= n; i++) {
      const x = this.wx(i / n * this.W), y = g(x);
      const pt = isFinite(y) ? [this.sx(x), this.sy(y)] : null;
      if (pt && prev && Math.abs(pt[1] - prev[1]) < limit && Math.abs(pt[1]) < limit * 2 && Math.abs(prev[1]) < limit * 2) {
        const col = color(prev.x, x);
        if (col !== cur) {
          if (cur) ctx.stroke();
          ctx.strokeStyle = col; cur = col;
          ctx.beginPath(); ctx.moveTo(prev[0], prev[1]);
        }
        ctx.lineTo(pt[0], pt[1]);
      } else if (cur) { ctx.stroke(); cur = null; }
      if (pt) pt.x = x;
      prev = pt;
    }
    if (cur) ctx.stroke();
    ctx.setLineDash([]);
  }

  drawExplicit() {
    const { f, fp, points } = this.data;
    const ctx = this.ctx;
    if (this.showDeriv) this.plot(fp, () => COLORS.deriv, 2, [6, 5]);
    this.plot(f, (a, b) => { const s = fp((a + b) / 2); return s > 1e-12 ? COLORS.inc : s < -1e-12 ? COLORS.dec : COLORS.flat; }, 3);
    // critical points
    ctx.font = '600 12px system-ui, sans-serif';
    const placed = [];
    for (const p of points) {
      if (!isFinite(p.y)) continue;
      const X = this.sx(p.x), Y = this.sy(p.y);
      ctx.fillStyle = COLORS.point;
      ctx.beginPath(); ctx.arc(X, Y, 5, 0, 2 * Math.PI); ctx.fill();
      ctx.strokeStyle = '#fff'; ctx.lineWidth = 2; ctx.stroke();
      const label = `${p.type === 'max' ? 'local max' : p.type === 'min' ? 'local min' : 'critical pt'} (${fmtNum(p.x)}, ${fmtNum(p.y)})`;
      const above = p.type !== 'min';
      // crowded points keep their dots but skip labels that would overlap
      const LY = above ? Y - 12 : Y + 20, w = ctx.measureText(label).width + 10;
      const LX = Math.min(Math.max(X, w / 2 + 2), this.W - w / 2 - 2);
      if (placed.some(q => Math.abs(q.x - LX) < (q.w + w) / 2 + 4 && Math.abs(q.y - LY) < 20)) continue;
      placed.push({ x: LX, y: LY, w });
      this.label(label, LX, LY);
    }
    // tangent line under the pointer
    if (this.hover && this.showTangent) {
      const x = this.wx(this.hover.px), y = f(x), m = fp(x);
      if (isFinite(y)) {
        if (isFinite(m)) {
          ctx.strokeStyle = COLORS.tangent; ctx.lineWidth = 2;
          ctx.beginPath();
          const xa = this.view.x0, xb = this.view.x1;
          ctx.moveTo(this.sx(xa), this.sy(y + m * (xa - x)));
          ctx.lineTo(this.sx(xb), this.sy(y + m * (xb - x)));
          ctx.stroke();
        }
        ctx.fillStyle = COLORS.tangent;
        ctx.beginPath(); ctx.arc(this.sx(x), this.sy(y), 5, 0, 2 * Math.PI); ctx.fill();
        const trend = !isFinite(m) ? 'slope undefined' : m > 1e-9 ? 'increasing ↗' : m < -1e-9 ? 'decreasing ↘' : 'flat (slope 0)';
        const { x: xn, f: fn } = this.names;
        this.setReadout(`${xn} = ${fmtNum(x)}   ${fn}(${xn}) = ${fmtNum(y)}   slope ${fn}′(${xn}) = ${fmtNum(m)}   → ${trend}`);
        return;
      }
    }
    this.setReadout('Move over the graph to see the tangent line and slope at any point. Drag to pan, scroll to zoom.');
  }

  label(text, x, y) {
    const ctx = this.ctx;
    const w = ctx.measureText(text).width + 10;
    x = Math.min(Math.max(x, w / 2 + 2), this.W - w / 2 - 2);
    ctx.fillStyle = 'rgba(255,255,255,0.9)';
    ctx.fillRect(x - w / 2, y - 14, w, 18);
    ctx.fillStyle = COLORS.point;
    ctx.textAlign = 'center'; ctx.textBaseline = 'alphabetic';
    ctx.fillText(text, x, y);
  }

  drawImplicit() {
    const { F } = this.data;
    const ctx = this.ctx, v = this.view;
    const nx = 180, ny = Math.max(60, Math.round(180 * this.H / this.W));
    const hx = (v.x1 - v.x0) / nx, hy = (v.y1 - v.y0) / ny;
    const val = [];
    for (let j = 0; j <= ny; j++) {
      const row = [];
      for (let i = 0; i <= nx; i++) row.push(F(v.x0 + i * hx, v.y0 + j * hy));
      val.push(row);
    }
    const segs = [];
    const lerp = (a, b, fa, fb) => a + (b - a) * fa / (fa - fb);
    for (let j = 0; j < ny; j++) for (let i = 0; i < nx; i++) {
      const x0 = v.x0 + i * hx, y0 = v.y0 + j * hy, x1 = x0 + hx, y1 = y0 + hy;
      const a = val[j][i], b = val[j][i + 1], c = val[j + 1][i + 1], d = val[j + 1][i];
      if (![a, b, c, d].every(isFinite)) continue;
      const pts = [];
      if ((a > 0) !== (b > 0)) pts.push([lerp(x0, x1, a, b), y0]);
      if ((b > 0) !== (c > 0)) pts.push([x1, lerp(y0, y1, b, c)]);
      if ((c > 0) !== (d > 0)) pts.push([lerp(x1, x0, c, d), y1]);
      if ((d > 0) !== (a > 0)) pts.push([x0, lerp(y1, y0, d, a)]);
      const big = Math.max(Math.abs(a), Math.abs(b), Math.abs(c), Math.abs(d));
      for (let k = 0; k + 1 < pts.length; k += 2) {
        const m = F((pts[k][0] + pts[k + 1][0]) / 2, (pts[k][1] + pts[k + 1][1]) / 2);
        if (Math.abs(m) < 0.5 * big) segs.push([pts[k], pts[k + 1]]);
      }
    }
    ctx.strokeStyle = COLORS.curve; ctx.lineWidth = 3; ctx.lineCap = 'round';
    ctx.beginPath();
    for (const [p, q] of segs) { ctx.moveTo(this.sx(p[0]), this.sy(p[1])); ctx.lineTo(this.sx(q[0]), this.sy(q[1])); }
    ctx.stroke();

    // horizontal (Fx = 0) and vertical (Fy = 0) tangents
    const e = 1e-6 * Math.max(1, v.x1 - v.x0);
    const Fx = (x, y) => (F(x + e, y) - F(x - e, y)) / (2 * e);
    const Fy = (x, y) => (F(x, y + e) - F(x, y - e)) / (2 * e);
    const marks = [];
    for (const [p, q] of segs) {
      for (const [G, kind] of [[Fx, 'h'], [Fy, 'v']]) {
        const gp = G(p[0], p[1]), gq = G(q[0], q[1]);
        if (gp * gq < 0) {
          const t = gp / (gp - gq);
          const X = this.sx(p[0] + (q[0] - p[0]) * t), Y = this.sy(p[1] + (q[1] - p[1]) * t);
          if (!marks.some(m => m.kind === kind && Math.hypot(m.X - X, m.Y - Y) < 8)) marks.push({ X, Y, kind });
        }
      }
    }
    for (const m of marks) {
      ctx.strokeStyle = m.kind === 'h' ? COLORS.inc : COLORS.dec; ctx.lineWidth = 2.5;
      ctx.beginPath();
      if (m.kind === 'h') { ctx.moveTo(m.X - 14, m.Y); ctx.lineTo(m.X + 14, m.Y); }
      else { ctx.moveTo(m.X, m.Y - 14); ctx.lineTo(m.X, m.Y + 14); }
      ctx.stroke();
      ctx.fillStyle = COLORS.point;
      ctx.beginPath(); ctx.arc(m.X, m.Y, 4, 0, 2 * Math.PI); ctx.fill();
    }

    const { x: xn, y: yn } = this.names;
    if (this.hover && this.showTangent && segs.length) {
      let best = null, bd = 30;
      for (const [p] of segs) {
        const d = Math.hypot(this.sx(p[0]) - this.hover.px, this.sy(p[1]) - this.hover.py);
        if (d < bd) { bd = d; best = p; }
      }
      if (best) {
        const [x, y] = best;
        const m = this.data.slope ? this.data.slope(x, y) : -Fx(x, y) / Fy(x, y);
        ctx.strokeStyle = COLORS.tangent; ctx.lineWidth = 2;
        ctx.beginPath();
        if (isFinite(m) && Math.abs(m) < 1e6) {
          ctx.moveTo(this.sx(v.x0), this.sy(y + m * (v.x0 - x)));
          ctx.lineTo(this.sx(v.x1), this.sy(y + m * (v.x1 - x)));
        } else { ctx.moveTo(this.sx(x), 0); ctx.lineTo(this.sx(x), this.H); }
        ctx.stroke();
        ctx.fillStyle = COLORS.tangent;
        ctx.beginPath(); ctx.arc(this.sx(x), this.sy(y), 5, 0, 2 * Math.PI); ctx.fill();
        this.setReadout(`(${xn}, ${yn}) = (${fmtNum(x)}, ${fmtNum(y)})   slope d${yn}/d${xn} = ${isFinite(m) && Math.abs(m) < 1e6 ? fmtNum(m) : 'undefined (vertical tangent)'}`);
        return;
      }
    }
    this.setReadout(segs.length
      ? 'Green bars: horizontal tangents. Red bars: vertical tangents. Move along the curve to see the tangent line.'
      : 'Nothing to draw in this window. Try zooming out.');
  }

  setReadout(t) { if (this.readout) this.readout.textContent = t; }
}
