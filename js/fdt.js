// First Derivative Test: domain, critical points, sign chart, increasing/decreasing, extrema.
import { num, sym, mul, pow, compile, contains, freeSyms, substitute, toTex, size, children } from './expr.js';
import { simplify, factorCommon } from './simplify.js';
import { toRational, realRoots, recognize, approxRoot, fmt, factorPolynomial } from './solve.js';

const TRIG = new Set(['sin', 'cos', 'tan', 'sec', 'csc', 'cot']);
const positiveConst = b => (b.type === 'sym' && (b.name === 'e' || b.name === 'pi')) || (b.type === 'num' && b.n > 0);
const uniqPts = pts => {
  const out = [];
  for (const p of pts.sort((a, b) => a.x - b.x)) if (!out.some(q => Math.abs(q.x - p.x) < 1e-9 * (1 + Math.abs(p.x)))) out.push(p);
  return out;
};
const INF = { x: Infinity, tex: '\\infty', closed: false };
const NINF = { x: -Infinity, tex: '-\\infty', closed: false };

// Where is f undefined? complete = true only if we know every such point exactly.
function exactDomain(f, v) {
  const poles = [];
  let complete = true;
  const has = n => freeSyms(n).has(v);
  (function walk(n) {
    if (!complete || !has(n)) return;
    switch (n.type) {
      case 'add': case 'mul': children(n).forEach(walk); return;
      case 'pow': {
        const { base, exp } = n;
        if (exp.type === 'num') {
          if (exp.d % 2 === 0) { complete = false; return; }
          if (exp.n < 0) {
            const r = toRational(base, v);
            if (!r) { complete = false; return; }
            poles.push(...realRoots(r.N));
          }
          walk(base);
          return;
        }
        if (!has(base) && positiveConst(base)) { walk(exp); return; }
        complete = false; return;
      }
      case 'fn':
        if (['sin', 'cos', 'atan', 'abs'].includes(n.name)) { walk(n.arg); return; }
        complete = false; return;
    }
  })(f);
  return { complete, poles: uniqPts(poles) };
}

// Zeros of f' and points where f' is undefined, found exactly from a factored form.
function exactCritical(fp, v) {
  let factored = factorCommon(fp);
  // split polynomial factors into linear pieces where possible: 3(x^2 - 1) -> 3(x - 1)(x + 1)
  const split = F => {
    const base = F.type === 'pow' && F.exp.type === 'num' && F.exp.d === 1 ? F.base : F;
    const r = freeSyms(base).has(v) && toRational(base, v);
    const fac = r && r.D.length === 1 && factorPolynomial(r.N, v);
    if (!fac) return F;
    return base === F ? fac : simplify(pow(fac, F.exp));
  };
  if (factored.type === 'mul') factored = simplify(mul(factored.factors.map(split)));
  else factored = split(factored);
  const factors = factored.type === 'mul' ? factored.factors : [factored];
  const zeros = [], undef = [];
  const fail = { complete: false, factored };
  for (const F of factors) {
    if (!freeSyms(F).has(v)) continue;
    const r = toRational(F, v);
    if (r) { zeros.push(...realRoots(r.N)); undef.push(...realRoots(r.D)); continue; }
    if (F.type !== 'pow') return fail;
    const { base, exp } = F;
    if (exp.type === 'num') {
      const rb = toRational(base, v);
      if (!rb) return fail;
      if (exp.n > 0) zeros.push(...realRoots(rb.N)); else undef.push(...realRoots(rb.N));
      undef.push(...realRoots(rb.D));
      continue;
    }
    if (!freeSyms(base).has(v) && positiveConst(base)) {
      const ru = toRational(exp, v);
      if (!ru) return fail;
      undef.push(...realRoots(ru.D));
      continue;
    }
    return fail;
  }
  return { complete: true, zeros: uniqPts(zeros), undef: uniqPts(undef), factored };
}

const snap = x => {
  const r = recognize(x);
  return r && Math.abs(r.x - x) < 1e-6 * (1 + Math.abs(x)) ? r : approxRoot(x);
};

// Numeric search on [a, b] for domain pieces and critical points.
function scan(f, fp, a, b, edges) {
  const N = 4000, h = (b - a) / N;
  const xs = [], ok = [];
  const raw = [];
  for (let i = 0; i <= N; i++) { const x = a + i * h; xs.push(x); raw.push(f(x)); ok.push(isFinite(raw[i])); }
  // long runs of +-Infinity are overflow (e^(x^2) at x = 30), not gaps in the domain
  for (let i = 0; i <= N;) {
    if (isFinite(raw[i]) || Number.isNaN(raw[i])) { i++; continue; }
    let j = i;
    while (j < N && !isFinite(raw[j + 1]) && !Number.isNaN(raw[j + 1])) j++;
    if (j - i >= 3) for (let k = i; k <= j; k++) ok[k] = true;
    i = j + 1;
  }
  const pieces = [], cands = [];
  const boundary = (bad, good) => {
    for (let k = 0; k < 60; k++) { const m = (bad + good) / 2; if (isFinite(f(m))) good = m; else bad = m; }
    const r = snap(good);
    const closed = isFinite(f(r.x)) && Math.abs(r.x - good) < 1e-6;
    return { x: r.x, tex: r.tex, closed, node: r.node };
  };
  let i = 0;
  while (i <= N) {
    if (!ok[i]) { i++; continue; }
    let j = i;
    while (j < N && ok[j + 1]) j++;
    if (j - i >= 2) {
      const l = i === 0 ? edges[0] : boundary(xs[i - 1], xs[i]);
      const r = j === N ? edges[1] : boundary(xs[j + 1], xs[j]);
      pieces.push({ l, r, i0: i, i1: j });
    }
    i = j + 1;
  }
  const out = [];
  for (const piece of pieces) {
    const poles = [];
    const pv = [];
    for (let k = piece.i0; k <= piece.i1; k++) pv.push(fp(xs[k]));
    const X = k => xs[piece.i0 + k];
    const events = [];
    for (let k = 0; k < pv.length; k++) {
      const p = pv[k];
      if (!isFinite(p)) {
        const iso = (k === 0 || isFinite(pv[k - 1])) && (k + 1 === pv.length || isFinite(pv[k + 1]));
        if (iso && isFinite(raw[piece.i0 + k])) events.push({ x: X(k), singular: true });
        continue;
      }
      if (k + 1 < pv.length && isFinite(pv[k + 1]) && p * pv[k + 1] < 0) {
        let lo = X(k), hi = X(k + 1);
        const sLo = Math.sign(p);
        for (let it = 0; it < 80; it++) { const m = (lo + hi) / 2; const s = Math.sign(fp(m)); if (s === sLo) lo = m; else hi = m; }
        const c = (lo + hi) / 2;
        const big = Math.max(Math.abs(fp(lo)), Math.abs(fp(hi)));
        events.push({ x: c, singular: big > 1e6 * Math.max(1, Math.abs(p), Math.abs(pv[k + 1])) });
      }
      if (k > 0 && k + 1 < pv.length && isFinite(pv[k - 1]) && isFinite(pv[k + 1])) {
        const ap = Math.abs(p);
        if (ap < Math.abs(pv[k - 1]) && ap <= Math.abs(pv[k + 1]) && pv[k - 1] * pv[k + 1] > 0) {
          const c = golden(x => Math.abs(fp(x)), X(k - 1), X(k + 1));
          if (Math.abs(fp(c)) < 1e-9) events.push({ x: c, singular: false });
        }
        if (ap > 1e3 && ap > Math.abs(pv[k - 1]) && ap >= Math.abs(pv[k + 1]) && pv[k - 1] * pv[k + 1] > 0) {
          const c = golden(x => -Math.abs(fp(x)), X(k - 1), X(k + 1));
          if (!(Math.abs(fp(c)) < 1e7)) events.push({ x: c, singular: true });
        }
      }
    }
    for (const e of events) {
      const r = snap(e.x);
      if (!e.singular) { cands.push({ ...r, kind: 'zero' }); continue; }
      const fc = f(r.x), d = 1e-7 * (1 + Math.abs(r.x));
      const continuous = isFinite(fc) && Math.abs(f(r.x - d) - fc) < 1e-2 * (1 + Math.abs(fc)) &&
        Math.abs(f(r.x + d) - fc) < 1e-2 * (1 + Math.abs(fc));
      if (continuous) cands.push({ ...r, kind: 'undef' });
      else poles.push({ x: r.x, tex: r.tex, closed: false });
    }
    // split the piece at poles
    let left = piece.l;
    for (const p of uniqPts(poles)) {
      if (p.x <= left.x || p.x >= piece.r.x) continue;
      out.push({ l: left, r: p });
      left = p;
    }
    out.push({ l: left, r: piece.r });
  }
  return { pieces: out, cands: uniqPts(cands) };
}

function golden(g, a, b) {
  const r = (Math.sqrt(5) - 1) / 2;
  let c = b - r * (b - a), d = a + r * (b - a);
  for (let i = 0; i < 100; i++) {
    if (g(c) < g(d)) b = d; else a = c;
    c = b - r * (b - a); d = a + r * (b - a);
  }
  return (a + b) / 2;
}

// Pick an easy test value strictly inside (l, r).
function testValue(l, r) {
  if (l === -Infinity && r === Infinity) return 0;
  if (l === -Infinity) return Math.floor(r) - 1;
  if (r === Infinity) return Math.ceil(l) + 1;
  const mid = (l + r) / 2, w = r - l;
  for (const q of [1, 2, 4, 10, 100, 1000]) {
    const cands = [];
    for (let p = Math.ceil(l * q); p <= Math.floor(r * q); p++) {
      const x = p / q;
      if (x > l + w * 1e-6 && x < r - w * 1e-6) cands.push(x);
    }
    if (cands.length) return cands.reduce((best, x) => (Math.abs(x - mid) < Math.abs(best - mid) ? x : best));
  }
  return mid;
}

function exactValue(node, v, at) {
  // value of node at x = at (an exact node), as tex, or null if it doesn't simplify nicely
  if (!at) return null;
  try {
    const s = simplify(substitute(node, { [v]: at }));
    if (s.type === 'num') return { tex: toTex(s), exactNum: true };
    if (freeSyms(s).size || contains(s, n => n.type === 'fn' || n.type === 'add') || size(s) > 14) return null;
    return { tex: toTex(s), exactNum: false };
  } catch { return null; }
}

const testNode = x => { const r = recognize(x); return r ? r.node : null; };

export function intervalTex(iv) {
  return `${iv.l.closed ? '[' : '('}${iv.l.tex}, ${iv.r.tex}${iv.r.closed ? ']' : ')'}`;
}

// Main entry. f and fp contain only the variable v. opts.interval = [a, b] or null.
export function analyze(f, fp, v, opts = {}) {
  const fC = compile(f), fpC = compile(fp);
  const F = x => fC({ [v]: x }), FP = x => fpC({ [v]: x });
  const periodic = contains(f, n => n.type === 'fn' && TRIG.has(n.name));
  const dom = exactDomain(f, v);
  const crit = exactCritical(fp, v);
  const notes = [];

  let mode, W;
  if (opts.interval) { mode = 'interval'; W = opts.interval; }
  else if (dom.complete && crit.complete && !periodic) mode = 'global';
  else if (periodic) { mode = 'window'; W = [-2 * Math.PI, 2 * Math.PI]; }
  else {
    mode = 'search';
    const xsKnown = [...dom.poles, ...(crit.complete ? [...crit.zeros, ...crit.undef] : [])].map(p => p.x);
    W = [Math.min(-30, ...xsKnown.map(x => x - 5)), Math.max(30, ...xsKnown.map(x => x + 5))];
  }

  let edges;
  if (mode === 'global' || mode === 'search') edges = [NINF, INF];
  else {
    // a window we chose ourselves is not a real endpoint, so leave it open
    const e = x => { const r = snap(x); return { x: r.x, tex: r.tex, closed: mode === 'interval' && isFinite(F(r.x)), node: r.node }; };
    edges = [e(W[0]), e(W[1])];
  }

  // domain pieces
  let pieces;
  let scanned = null;
  const doScan = () => scanned || (scanned = scan(F, FP, W ? W[0] : -30, W ? W[1] : 30, edges));
  if (dom.complete) {
    const lo = edges[0], hi = edges[1];
    const poles = dom.poles.filter(p => p.x > lo.x && p.x < hi.x).map(p => ({ ...p, closed: false }));
    pieces = [];
    let left = lo;
    for (const p of poles) { pieces.push({ l: left, r: p }); left = p; }
    pieces.push({ l: left, r: hi });
    if (!isFinite(F(lo.x)) && isFinite(lo.x)) lo.closed = false;
    if (!isFinite(F(hi.x)) && isFinite(hi.x)) hi.closed = false;
  } else pieces = doScan().pieces;

  // critical point candidates
  let cands;
  const inside = x => pieces.some(p => x > p.l.x && x < p.r.x);
  if (crit.complete) {
    cands = [...crit.zeros.map(z => ({ ...z, kind: 'zero' })), ...crit.undef.map(z => ({ ...z, kind: 'undef' }))]
      .filter(c => inside(c.x) && isFinite(F(c.x)));
  } else cands = doScan().cands.filter(c => inside(c.x));
  cands = uniqPts(cands);

  // f' undefined but f also undefined -> not critical (shown to students as a note)
  const excluded = crit.complete
    ? crit.undef.filter(z => !isFinite(F(z.x)) && (!W || (z.x >= W[0] && z.x <= W[1])))
    : [];

  // intervals
  const intervals = [];
  for (const p of pieces) {
    const pts = [p.l, ...cands.filter(c => c.x > p.l.x && c.x < p.r.x).map(c => ({ ...c, closed: false })), p.r];
    for (let k = 0; k + 1 < pts.length; k++) {
      const l = pts[k], r = pts[k + 1];
      const t = testValue(l.x, r.x);
      const val = FP(t);
      const ex = exactValue(fp, v, testNode(t));
      intervals.push({
        l: { ...l, closed: l.closed && k === 0 }, r: { ...r, closed: r.closed && k + 1 === pts.length - 1 },
        test: { x: t, tex: recognize(t) ? recognize(t).tex : fmt(t) },
        value: val, valueTex: ex && ex.exactNum ? ex.tex : fmt(val),
        sign: Math.abs(val) < 1e-12 ? 0 : Math.sign(val),
      });
    }
  }

  // classify
  const points = cands.map(c => {
    const left = intervals.find(iv => Math.abs(iv.r.x - c.x) < 1e-12);
    const right = intervals.find(iv => Math.abs(iv.l.x - c.x) < 1e-12);
    let type = 'neither';
    if (left && right) {
      if (left.sign > 0 && right.sign < 0) type = 'max';
      else if (left.sign < 0 && right.sign > 0) type = 'min';
    }
    return { ...c, type, ...yInfo(c) };
  });
  function yInfo(c) {
    const y = F(c.x);
    const ex = c.exact ? exactValue(f, v, c.node) : null;
    const yTex = ex ? (ex.exactNum ? ex.tex : `${ex.tex} \\approx ${fmt(y)}`) : `\\approx ${fmt(y)}`;
    return { y, yTex };
  }

  // endpoints of a closed interval or domain
  const endpoints = [];
  for (const iv of intervals) {
    for (const [end, side] of [[iv.l, 'left'], [iv.r, 'right']]) {
      if (!end.closed || !isFinite(end.x)) continue;
      if (endpoints.some(e => Math.abs(e.x - end.x) < 1e-12)) continue;
      const rising = iv.sign > 0;
      const type = side === 'left' ? (rising ? 'min' : 'max') : (rising ? 'max' : 'min');
      endpoints.push({ ...end, exact: !!end.node, type, ...yInfo({ ...end, exact: !!end.node }) });
    }
  }

  const merge = list => {
    // combine adjacent intervals with the same sign that meet at a non-extremum: (-inf,0) and (0,inf) -> keep separate per textbook convention
    return list.map(intervalTex);
  };
  const increasing = merge(intervals.filter(iv => iv.sign > 0));
  const decreasing = merge(intervals.filter(iv => iv.sign < 0));

  const domainTex = mode === 'window' && dom.complete && !dom.poles.length ? '(-\\infty, \\infty)'
    : pieces.length === 1 && pieces[0].l.x === -Infinity && pieces[0].r.x === Infinity
    ? '(-\\infty, \\infty)' : pieces.map(intervalTex).join(' \\cup ');

  if (mode === 'window') notes.push('This function contains trig functions, which repeat forever, so there are infinitely many critical points. We analyze one window, -2π ≤ x ≤ 2π. Use "Analyze on interval" to choose a different window.');
  if (mode === 'search') notes.push('These critical points were found numerically by searching from x = ' + fmt(W[0]) + ' to x = ' + fmt(W[1]) + '. Values marked ≈ are decimal approximations.');
  if (mode === 'interval') notes.push(`Analysis restricted to the interval [${fmt(W[0])}, ${fmt(W[1])}].`);

  return {
    mode, notes, domainTex, domainExact: dom.complete,
    domainWithinWindow: (mode === 'window' || mode === 'interval') && !(dom.complete && !dom.poles.length),
    factoredTex: toTex(crit.factored) !== toTex(fp) ? toTex(crit.factored) : null,
    zeros: cands.filter(c => c.kind === 'zero'),
    undef: cands.filter(c => c.kind === 'undef'),
    excluded,
    points, endpoints, intervals, increasing, decreasing,
    window: W || null,
  };
}

export { sym, num };
