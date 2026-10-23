// Solving f'(x) = 0: exact polynomial / rational-function roots, plus a numeric fallback
// and recognition of "nice" numbers (1/3, pi/2, sqrt(2), e^-1).
import { num, radd, rmul, rdiv, isZero, gcd, add, mul, pow, sym, toTex, HALF } from './expr.js';
import { simplify } from './simplify.js';

// ---------- polynomials over the rationals (coefficients low -> high) ----------

const R0 = num(0), R1 = num(1);
const trim = p => { const q = p.slice(); while (q.length > 1 && isZero(q[q.length - 1])) q.pop(); return q; };
const deg = p => (p.length === 1 && isZero(p[0]) ? -Infinity : p.length - 1);
const lead = p => p[p.length - 1];

function padd(a, b) {
  const out = [];
  for (let i = 0; i < Math.max(a.length, b.length); i++) out.push(radd(a[i] || R0, b[i] || R0));
  return trim(out);
}
function pmul(a, b) {
  const out = Array(a.length + b.length - 1).fill(R0);
  a.forEach((x, i) => b.forEach((y, j) => { out[i + j] = radd(out[i + j], rmul(x, y)); }));
  return trim(out);
}
const pscale = (a, c) => trim(a.map(x => rmul(x, c)));
function pdivmod(a, b) {
  let r = trim(a);
  const q = Array(Math.max(1, a.length - b.length + 1)).fill(R0);
  while (deg(r) >= deg(b) && deg(r) > -Infinity) {
    const k = r.length - b.length;
    const c = rdiv(lead(r), lead(b));
    q[k] = c;
    r = padd(r, pscale([...Array(k).fill(R0), ...b], num(-c.n, c.d)));
  }
  return [trim(q), r];
}
function pgcd(a, b) {
  a = trim(a); b = trim(b);
  while (deg(b) > -Infinity) [a, b] = [b, pdivmod(a, b)[1]];
  return deg(a) === -Infinity ? [R1] : pscale(a, rdiv(R1, lead(a)));
}
const pderiv = p => (p.length === 1 ? [R0] : trim(p.slice(1).map((c, i) => rmul(c, num(i + 1)))));
const pevalR = (p, x) => p.reduceRight((acc, c) => radd(rmul(acc, x), c), R0);

// Rational function N/D in variable v, or null if the expression is not one.
export function toRational(n, v) {
  switch (n.type) {
    case 'num': return { N: [n], D: [R1] };
    case 'sym': return n.name === v ? { N: [R0, R1], D: [R1] } : null;
    case 'add': {
      let acc = { N: [R0], D: [R1] };
      for (const t of n.terms) {
        const r = toRational(t, v);
        if (!r) return null;
        acc = reduce({ N: padd(pmul(acc.N, r.D), pmul(r.N, acc.D)), D: pmul(acc.D, r.D) });
      }
      return acc;
    }
    case 'mul': {
      let acc = { N: [R1], D: [R1] };
      for (const f of n.factors) {
        const r = toRational(f, v);
        if (!r) return null;
        acc = reduce({ N: pmul(acc.N, r.N), D: pmul(acc.D, r.D) });
      }
      return acc;
    }
    case 'pow': {
      if (n.exp.type !== 'num' || n.exp.d !== 1 || Math.abs(n.exp.n) > 20) return null;
      const r = toRational(n.base, v);
      if (!r) return null;
      let acc = { N: [R1], D: [R1] };
      for (let i = 0; i < Math.abs(n.exp.n); i++) acc = { N: pmul(acc.N, r.N), D: pmul(acc.D, r.D) };
      return n.exp.n < 0 ? reduce({ N: acc.D, D: acc.N }) : reduce(acc);
    }
    default: return null;
  }
}

function reduce({ N, D }) {
  if (deg(N) === -Infinity) return { N: [R0], D: [R1] };
  const g = pgcd(N, D);
  N = pdivmod(N, g)[0]; D = pdivmod(D, g)[0];
  const c = lead(D);
  return { N: pscale(N, rdiv(R1, c)), D: pscale(D, rdiv(R1, c)) };
}

export function polyToNode(p, v) {
  return simplify(add(p.map((c, i) => mul([c, pow(sym(v), num(i))]))));
}

// Factor a polynomial over the rationals as far as rational roots allow:
// 3x^2 - 3  ->  3(x - 1)(x + 1).  Returns null when there is nothing to split off.
export function factorPolynomial(p, v) {
  p = trim(p);
  if (deg(p) < 2) return null;
  const linear = [];
  let rest = p, scale = R1;
  while (deg(rest) > 0 && isZero(rest[0])) { rest = trim(rest.slice(1)); linear.push(sym(v)); }
  let L = 1;
  for (const c of rest) L = lcm(L, c.d);
  if (deg(rest) >= 1) {
    const ps = divisors(rest[0].n * (L / rest[0].d)), qs = divisors(lead(rest).n * (L / lead(rest).d));
    if (ps.length * qs.length < 40000) {
      for (const pp of ps) for (const qq of qs) for (const sg of [1, -1]) {
        const c = num(sg * pp, qq);
        if (c.d !== qq || c.n !== sg * pp) continue;
        while (deg(rest) >= 1 && isZero(pevalR(rest, c))) {
          rest = pdivmod(rest, [num(-c.n, c.d), R1])[0];
          linear.push(add([mul([num(c.d), sym(v)]), num(-c.n)]));
          scale = rdiv(scale, num(c.d));
        }
      }
    }
  }
  if (!linear.length || (linear.length === 1 && deg(p) === 1)) return null;
  rest = pscale(rest, scale);
  // pull the numeric content out of what is left so it reads 3(x^2 + 1), not (3x^2 + 3)
  let content = rest[0];
  for (const c of rest.slice(1)) if (!isZero(c)) content = num(gcd(content.n, c.n) || c.n, lcm(content.d, c.d));
  if (isZero(content)) content = R1;
  if (lead(rest).n < 0) content = num(-Math.abs(content.n), content.d);
  const restNode = polyToNode(pscale(rest, rdiv(R1, content)), v);
  return simplify(mul([content, restNode, ...linear]));
}

// ---------- roots ----------

function divisors(n) {
  n = Math.abs(n);
  if (n === 0) return [];
  const out = [];
  for (let i = 1; i * i <= n && i < 2e6; i++) if (n % i === 0) { out.push(i); if (i * i !== n) out.push(n / i); }
  return out;
}

function lcm(a, b) { return a / gcd(a, b) * b; }

// Real roots of a rational polynomial. Each root: { x, tex, node, exact }.
export function realRoots(p) {
  p = trim(p);
  if (deg(p) <= 0) return [];
  // square-free part: repeated roots only need to be found once
  const g = pgcd(p, pderiv(p));
  if (deg(g) > 0) p = pdivmod(p, g)[0];
  const roots = [];
  if (isZero(p[0])) { roots.push(exactRoot(num(0))); p = trim(p.slice(1)); }
  let L = 1;
  for (const c of p) L = lcm(L, c.d);
  if (deg(p) >= 1) {
    const a0 = p[0].n * (L / p[0].d), an = lead(p).n * (L / lead(p).d);
    const ps = divisors(a0), qs = divisors(an);
    if (ps.length * qs.length < 40000) {
      const seen = new Set();
      for (const pp of ps) for (const qq of qs) for (const s of [1, -1]) {
        const c = num(s * pp, qq);
        const k = `${c.n}/${c.d}`;
        if (seen.has(k)) continue;
        seen.add(k);
        if (deg(p) >= 1 && isZero(pevalR(p, c))) {
          roots.push(exactRoot(c));
          p = pdivmod(p, [num(-c.n, c.d), R1])[0];
        }
      }
    }
  }
  if (deg(p) === 1) roots.push(exactRoot(rdiv(num(-p[0].n, p[0].d), p[1])));
  else if (deg(p) === 2) roots.push(...quadraticRoots(p));
  else if (deg(p) > 2) roots.push(...numericPolyRoots(p.map(c => c.n / c.d)).map(x => approxRoot(x)));
  return roots.sort((a, b) => a.x - b.x);
}

const exactRoot = c => ({ x: c.n / c.d, tex: toTex(c), node: c, exact: true });

export function approxRoot(x) {
  const r = recognize(x);
  return r || { x, tex: fmt(x), node: null, exact: false };
}

function quadraticRoots(p) {
  let L = 1;
  for (const c of p) L = lcm(L, c.d);
  const [c, b, a] = p.map(r => r.n * (L / r.d));
  const disc = b * b - 4 * a * c;
  if (disc < 0) return [];
  // disc = k^2 m with m square-free
  let k = 1, m = disc;
  for (let i = 2; i * i <= m; i++) while (m % (i * i) === 0) { m /= i * i; k *= i; }
  let A = 2 * a, B = -b, K = k;
  const g = gcd(gcd(A, B), K);
  A /= g; B /= g; K /= g;
  if (A < 0) { A = -A; B = -B; K = -K; }
  K = Math.abs(K);
  return [-1, 1].map(s => {
    const node = simplify(add([num(B, A), mul([num(s * K, A), pow(num(m), HALF)])]));
    const surd = `${K === 1 ? '' : K}\\sqrt{${m}}`;
    const top = B === 0 ? `${s < 0 ? '-' : ''}${surd}` : `${B} ${s < 0 ? '-' : '+'} ${surd}`;
    const tex = A === 1 ? top : `\\frac{${top}}{${A}}`;
    return { x: (B + s * K * Math.sqrt(m)) / A, tex, node, exact: true };
  });
}

// Durand–Kerner: all complex roots, keep the real ones and polish with Newton.
export function numericPolyRoots(c) {
  const n = c.length - 1;
  const a = c.map(x => x / c[n]);
  const bound = 1 + Math.max(...a.slice(0, n).map(Math.abs));
  let z = Array.from({ length: n }, (_, k) => {
    const t = 2 * Math.PI * k / n + 0.4;
    return [bound * Math.cos(t) * 0.9, bound * Math.sin(t) * 0.9];
  });
  const cm = (p, q) => [p[0] * q[0] - p[1] * q[1], p[0] * q[1] + p[1] * q[0]];
  const cd = (p, q) => { const d = q[0] * q[0] + q[1] * q[1]; return [(p[0] * q[0] + p[1] * q[1]) / d, (p[1] * q[0] - p[0] * q[1]) / d]; };
  const ev = w => a.reduceRight((acc, co) => { const m = cm(acc, w); return [m[0] + co, m[1]]; }, [0, 0]);
  for (let it = 0; it < 800; it++) {
    let moved = 0;
    z = z.map((zi, i) => {
      let den = [1, 0];
      z.forEach((zj, j) => { if (i !== j) den = cm(den, [zi[0] - zj[0], zi[1] - zj[1]]); });
      const step = cd(ev(zi), den);
      moved = Math.max(moved, Math.hypot(step[0], step[1]));
      return [zi[0] - step[0], zi[1] - step[1]];
    });
    if (moved < 1e-14) break;
  }
  const pf = x => a.reduceRight((acc, co) => acc * x + co, 0);
  const dpf = x => a.reduceRight((acc, co, i) => (i === 0 ? acc : acc * x + co * i), 0);
  const real = z.filter(w => Math.abs(w[1]) < 1e-6 * (1 + Math.abs(w[0]))).map(w => {
    let x = w[0];
    for (let i = 0; i < 30; i++) { const d = dpf(x); if (!d) break; const s = pf(x) / d; x -= s; if (Math.abs(s) < 1e-15) break; }
    return x;
  });
  return dedupe(real.sort((p, q) => p - q));
}

export function dedupe(xs, tol = 1e-7) {
  const out = [];
  for (const x of xs) if (!out.some(y => Math.abs(x - y) < tol * (1 + Math.abs(y)))) out.push(x);
  return out;
}

// ---------- recognizing nice numbers ----------

export function fmt(x) {
  if (!isFinite(x)) return x > 0 ? '\\infty' : '-\\infty';
  const r = Math.round(x * 1e4) / 1e4;
  return `${Object.is(r, -0) ? 0 : r}`;
}

function fraction(x, maxDen) {
  for (let q = 1; q <= maxDen; q++) {
    const p = Math.round(x * q);
    if (Math.abs(p / q - x) < 1e-9 * Math.max(1, Math.abs(x))) return num(p, q);
  }
  return null;
}

// Returns { x, tex, node, exact: true } for numbers like 3, -1/4, pi/2, sqrt(3), e^-1, else null.
export function recognize(x) {
  if (!isFinite(x)) return null;
  const f = fraction(x, 24);
  if (f) return exactRoot(f);
  const pi = fraction(x / Math.PI, 12);
  if (pi) {
    const node = simplify(mul([pi, sym('pi')]));
    return { x: pi.n * Math.PI / pi.d, tex: toTex(node), node, exact: true };
  }
  const sq = fraction(x * x, 12);
  if (sq && sq.n > 0) {
    const node = simplify(mul([num(x < 0 ? -1 : 1), pow(sq, HALF)]));
    return { x: Math.sign(x) * Math.sqrt(sq.n / sq.d), tex: toTex(node), node, exact: true };
  }
  if (x > 0) {
    const l = fraction(Math.log(x), 6);
    if (l && l.n !== 0) {
      const node = simplify(pow(sym('e'), l));
      return { x: Math.exp(l.n / l.d), tex: toTex(node), node, exact: true };
    }
  }
  return null;
}
