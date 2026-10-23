// First Derivative Test: domain, critical points, sign chart, increasing/decreasing, extrema.
import { num, sym, add, mul, pow, fn, compile, contains, freeSyms, substitute, toTex, size, children } from './expr.js';
import { simplify, factorCommon } from './simplify.js';
import { toRational, realRoots, recognize, approxRoot, fmt, factorPolynomial } from './solve.js';

const MAX_POINTS = 8;
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

// sin(u) = 0, cos(u) = 0, tan(u) = 0 have infinitely many solutions. When u = ax + b or
// u = e^(ax + b), write the whole family:  e^{2x} = k pi  =>  x = (1/2) ln(k pi), k = 1, 2, 3, ...
function generalSolutions(factored, v) {
  const factors = factored.type === 'mul' ? factored.factors : [factored];
  const out = [];
  const K = sym('k'), PI = sym('pi');
  const fixK = t => t.replace(/\\pi k/g, 'k\\pi');
  for (let F of factors) {
    if (F.type === 'pow' && F.exp.type === 'num' && F.exp.n > 0) F = F.base;
    if (F.type !== 'fn' || !['sin', 'cos', 'tan'].includes(F.name)) continue;
    const u = F.arg;
    const rhs = F.name === 'cos' ? add([mul([num(1, 2), PI]), mul([K, PI])]) : mul([K, PI]);
    const rhsTex = F.name === 'cos' ? '\\frac{\\pi}{2} + k\\pi' : 'k\\pi';
    const isExp = u.type === 'pow' && u.base.type === 'sym' && u.base.name === 'e';
    const lin = toRational(isExp ? u.exp : u, v);
    if (!lin || lin.D.length !== 1 || lin.N.length !== 2) continue;
    const [b, a] = lin.N;
    const solve = w => simplify(mul([add([w, mul([num(-1), b])]), pow(a, num(-1))]));
    const xTex = fixK(toTex(solve(isExp ? fn('ln', rhs) : rhs)));
    const ks = !isExp ? 'k \\text{ any integer}' : F.name === 'cos' ? 'k = 0, 1, 2, \\dots' : 'k = 1, 2, 3, \\dots';
    const plain = u.type === 'sym' && u.name === v;
    out.push(plain
      ? `${toTex(F)} = 0 \\text{ when } ${v} = ${rhsTex}, \\quad ${ks}`
      : `\\begin{gathered}${toTex(F)} = 0 \\text{ when } ${toTex(u)} = ${rhsTex} \\\\ \\Rightarrow\\; ${v} = ${xTex}, \\quad ${ks}\\end{gathered}`);
  }
  return out;
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

  const openEdge = x => { const r = snap(x); return { x: r.x, tex: r.tex, closed: false, node: r.node }; };
  let edges;
  if (mode === 'global' || mode === 'search') edges = [NINF, INF];
  else {
    // a window we chose ourselves is not a real endpoint, so leave it open
    const e = x => ({ ...openEdge(x), closed: mode === 'interval' && isFinite(F(snap(x).x)) });
    edges = [e(W[0]), e(W[1])];
  }

  // domain pieces and critical number candidates between two edges
  function locate(edges, lo, hi) {
    let scanned = null;
    const doScan = () => scanned || (scanned = scan(F, FP, lo, hi, edges));
    let pieces;
    if (dom.complete) {
      const L = edges[0], H = edges[1];
      const poles = dom.poles.filter(p => p.x > L.x && p.x < H.x).map(p => ({ ...p, closed: false }));
      pieces = [];
      let left = L;
      for (const p of poles) { pieces.push({ l: left, r: p }); left = p; }
      pieces.push({ l: left, r: H });
      if (!isFinite(F(L.x)) && isFinite(L.x)) L.closed = false;
      if (!isFinite(F(H.x)) && isFinite(H.x)) H.closed = false;
    } else pieces = doScan().pieces;
    const inside = x => pieces.some(p => x > p.l.x && x < p.r.x);
    let cands;
    if (crit.complete) {
      cands = [...crit.zeros.map(z => ({ ...z, kind: 'zero' })), ...crit.undef.map(z => ({ ...z, kind: 'undef' }))]
        .filter(c => inside(c.x) && isFinite(F(c.x)));
    } else cands = doScan().cands.filter(c => inside(c.x));
    return { pieces, cands: uniqPts(cands), inside };
  }

  let { pieces, cands, inside } = locate(edges, W ? W[0] : -30, W ? W[1] : 30);

  // Too many critical numbers (cos(e^(2x)) has infinitely many, crowding together):
  // keep the MAX_POINTS closest to x = 0 and shrink the window around them.
  let truncated = false, center = 0;
  if (cands.length > MAX_POINTS) {
    truncated = true;
    center = (!W || (W[0] < 0 && W[1] > 0)) ? 0 : isFinite(pieces[0].l.x) ? pieces[0].l.x : cands[0].x;
    const keep = [...cands].sort((p, q) => Math.abs(p.x - center) - Math.abs(q.x - center)).slice(0, MAX_POINTS)
      .sort((p, q) => p.x - q.x);
    const first = keep[0].x, last = keep[keep.length - 1].x;
    const before = cands.filter(c => c.x < first), after = cands.filter(c => c.x > last);
    const span = Math.max(last - first, 1e-6);
    // with nothing dropped on a side, keep a student's own interval end, otherwise leave a little room
    const pad = Math.max(span / 2, 1);
    const L = before.length ? openEdge((before[before.length - 1].x + first) / 2)
      : edges[0].closed ? edges[0] : openEdge(Math.max(edges[0].x, first - pad));
    const H = after.length ? openEdge((last + after[0].x) / 2)
      : edges[1].closed ? edges[1] : openEdge(Math.min(edges[1].x, last + pad));
    edges = [L, H];
    W = [L.x, H.x];
    ({ pieces, cands } = locate(edges, L.x, H.x));
    cands = cands.slice(0, MAX_POINTS);
  }

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

  if (truncated) notes.push(`f′ = 0 at infinitely many (or a great many) x-values here, and they crowd together, so we analyze the ${cands.length} closest to x = ${fmt(center)}, on the window ${fmt(W[0])} < x < ${fmt(W[1])}. Use "Analyze on an interval" to look at a different stretch.`);
  else if (mode === 'window') notes.push('This function contains trig functions, which repeat forever, so there are infinitely many critical points. We analyze one window, -2π ≤ x ≤ 2π. Use "Analyze on interval" to choose a different window.');
  if (mode === 'search' && !truncated) notes.push('These critical points were found numerically by searching from x = ' + fmt(W[0]) + ' to x = ' + fmt(W[1]) + '. Values marked ≈ are decimal approximations.');
  if (mode === 'interval' && !truncated) notes.push(`Analysis restricted to the interval [${fmt(W[0])}, ${fmt(W[1])}].`);

  return {
    mode, notes, domainTex, domainExact: dom.complete, truncated,
    general: generalSolutions(crit.factored, v),
    domainWithinWindow: (mode === 'window' || mode === 'interval' || truncated) && !(dom.complete && !dom.poles.length),
    factoredTex: toTex(crit.factored) !== toTex(fp) ? toTex(crit.factored) : null,
    zeros: cands.filter(c => c.kind === 'zero'),
    undef: cands.filter(c => c.kind === 'undef'),
    excluded,
    points, endpoints, intervals, increasing, decreasing,
    window: W || null,
  };
}

export { sym, num };
