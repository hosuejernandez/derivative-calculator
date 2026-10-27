// Algebraic simplification into a canonical form, plus expansion and "pretty" final forms.
import {
  num, radd, rmul, isZero, isOne, add, mul, pow, fn, eq, key, sym, gcd, children,
} from './expr.js';

// Terms are ordered by degree in this variable (2ax + b, not b + 2ax).
let mainVar = 'x';
export function setMainVar(v) { mainVar = v; }

export function simplify(n) {
  switch (n.type) {
    case 'eq': return eq(simplify(n.lhs), simplify(n.rhs));
    case 'num': case 'sym': return n;
    case 'add': return sAdd(n.terms.map(simplify));
    case 'mul': return sMul(n.factors.map(simplify));
    case 'pow': return sPow(simplify(n.base), simplify(n.exp));
    case 'fn': return sFn(n.name, simplify(n.arg));
  }
}

// Split a term into its numeric coefficient and the rest (rest is null for a pure number).
export function splitCoef(t) {
  if (t.type === 'num') return [t, null];
  if (t.type === 'mul' && t.factors[0].type === 'num') {
    const rest = t.factors.slice(1);
    return [t.factors[0], rest.length === 1 ? rest[0] : mul(rest)];
  }
  return [num(1), t];
}

export function makeTerm(c, rest) {
  if (!rest) return c;
  if (isZero(c)) return c;
  if (isOne(c)) return rest;
  if (rest.type === 'mul') return mul([c, ...rest.factors]);
  return mul([c, rest]);
}

function degreeIn(t, v) {
  if (t.type === 'sym') return t.name === v ? 1 : 0;
  if (t.type === 'pow' && t.base.type === 'sym' && t.base.name === v && t.exp.type === 'num') return t.exp.n / t.exp.d;
  if (t.type === 'mul') return t.factors.reduce((s, f) => s + degreeIn(f, v), 0);
  return 0;
}

function totalDegree(t) {
  if (t.type === 'sym' && !t.deriv && t.name !== 'pi' && t.name !== 'e') return 1;
  if (t.type === 'pow' && t.exp.type === 'num') return totalDegree(t.base) * t.exp.n / t.exp.d;
  if (t.type === 'mul') return t.factors.reduce((s, f) => s + totalDegree(f), 0);
  return 0;
}

function sortTerms(terms) {
  const info = terms.map(t => {
    const [, rest] = splitCoef(t);
    return { t, isConst: !rest, d: rest ? degreeIn(rest, mainVar) : 0, td: rest ? totalDegree(rest) : 0, k: rest ? key(rest) : '' };
  });
  info.sort((a, b) => (a.isConst - b.isConst) || (b.d - a.d) || (b.td - a.td) || (a.k < b.k ? -1 : a.k > b.k ? 1 : 0));
  return info.map(i => i.t);
}

function sAdd(terms) {
  const flat = [];
  for (const t of terms) t.type === 'add' ? flat.push(...t.terms) : flat.push(t);
  let c = num(0);
  const groups = new Map();
  for (const t of flat) {
    if (t.type === 'num') { c = radd(c, t); continue; }
    const [k, rest] = splitCoef(t);
    const kk = key(rest);
    const g = groups.get(kk);
    if (g) g.coef = radd(g.coef, k);
    else groups.set(kk, { coef: k, rest });
  }
  const out = [];
  for (const g of groups.values()) if (!isZero(g.coef)) out.push(makeTerm(g.coef, g.rest));
  if (!isZero(c)) out.push(c);
  if (out.length === 0) return num(0);
  if (out.length === 1) return out[0];
  return add(sortTerms(out));
}

function factorRank(f) {
  const b = f.type === 'pow' ? f.base : f;
  if (b.type === 'sym') {
    if (b.name === 'pi') return 0;
    if (b.deriv) return 5;
    if (b.name === 'e') return 2;
    return 1;
  }
  if (b.type === 'num') return 0.5;
  if (b.type === 'fn') return 3;
  return 4;
}

function sortFactors(fs) {
  const k = f => key(f.type === 'pow' ? f.base : f);
  return fs.sort((a, b) => (factorRank(a) - factorRank(b)) || (k(a) < k(b) ? -1 : k(a) > k(b) ? 1 : 0));
}

function sMul(factors, depth = 0) {
  const flat = [];
  for (const f of factors) f.type === 'mul' ? flat.push(...f.factors) : flat.push(f);
  let c = num(1);
  const groups = new Map();
  for (const f of flat) {
    if (f.type === 'num') { c = rmul(c, f); continue; }
    const base = f.type === 'pow' ? f.base : f;
    const exp = f.type === 'pow' ? f.exp : num(1);
    const kk = key(base);
    const g = groups.get(kk);
    if (g) g.exps.push(exp); else groups.set(kk, { base, exps: [exp] });
  }
  if (isZero(c)) return num(0);
  let out = [], again = false;
  for (const g of groups.values()) {
    const e = g.exps.length === 1 ? g.exps[0] : sAdd(g.exps);
    const p = sPow(g.base, e);
    if (p.type === 'num') c = rmul(c, p);
    else if (p.type === 'mul') { out.push(...p.factors); again = true; }
    else out.push(p);
  }
  if (again && depth < 4) return sMul([c, ...out], depth + 1);
  if (isZero(c)) return num(0);
  out = sortFactors(out);
  if (out.length === 0) return c;
  if (isOne(c) && out.length === 1) return out[0];
  return mul(isOne(c) ? out : [c, ...out]);
}

function intRoot(n, q) {
  // exact integer q-th root of n >= 0, or null
  const r = Math.round(Math.pow(n, 1 / q));
  for (const c of [r - 1, r, r + 1]) if (c >= 0 && Math.pow(c, q) === n) return c;
  return null;
}

function bigPow(b, k) {
  const v = Math.pow(b, k);
  if (!Number.isSafeInteger(v)) throw new Error('A number got too large to handle exactly');
  return v;
}

export function sPow(b, e) {
  if (e.type === 'num') {
    if (isZero(e)) return num(1);
    if (isOne(e)) return b;
  }
  if (b.type === 'num') {
    if (isZero(b)) return e.type === 'num' && e.n > 0 ? num(0) : pow(b, e);
    if (isOne(b)) return num(1);
    if (e.type === 'num') {
      if (e.d === 1) {
        const k = Math.abs(e.n);
        if (k > 60) return pow(b, e);
        const r = num(bigPow(b.n, k), bigPow(b.d, k));
        return e.n < 0 ? num(r.d, r.n) : r;
      }
      if (b.d !== 1) return sMul([sPow(num(b.n), e), sPow(num(b.d), num(-e.n, e.d))]);
      if (b.n < 0 && e.d % 2 === 0) return pow(b, e);
      // exact root?  8^(2/3) = 4
      const r = intRoot(Math.abs(b.n), e.d);
      if (r !== null) return sPow(num(b.n < 0 ? -r : r), num(e.n));
      // pull out perfect powers:  sqrt(8) = 2 sqrt(2)
      if (b.n > 0 && Math.abs(e.n) === 1) {
        let k = 1, m = b.n;
        for (let c = 2; Math.pow(c, e.d) <= m && c < 10000; c++) {
          const cq = Math.pow(c, e.d);
          while (m % cq === 0) { m /= cq; k *= c; }
        }
        if (k > 1) return sMul([num(e.n > 0 ? k : 1, e.n > 0 ? 1 : k), pow(num(m), e)]);
      }
    }
    return pow(b, e);
  }
  if (b.type === 'pow') {
    if ((e.type === 'num' && e.d === 1) || (b.base.type === 'sym' && b.base.name === 'e'))
      return sPow(b.base, sMul([b.exp, e]));
  }
  if (b.type === 'mul' && e.type === 'num') {
    if (e.d === 1) return sMul(b.factors.map(f => sPow(f, e)));
    const c = b.factors[0];
    if (c.type === 'num' && c.n > 0) {
      const rest = b.factors.slice(1);
      return sMul([sPow(c, e), pow(rest.length === 1 ? rest[0] : mul(rest), e)]);
    }
  }
  if (b.type === 'sym' && b.name === 'e' && e.type === 'fn' && e.name === 'ln') return e.arg;
  // |u|^2 = u^2
  if (b.type === 'fn' && b.name === 'abs' && e.type === 'num' && e.d === 1 && e.n % 2 === 0) return sPow(b.arg, e);
  return pow(b, e);
}

function sFn(name, a) {
  if (a.type === 'num') {
    if (isZero(a)) {
      if (['sin', 'tan', 'asin', 'atan', 'abs'].includes(name)) return num(0);
      if (['cos', 'sec'].includes(name)) return num(1);
    }
    if (isOne(a) && (name === 'ln' || name === 'log')) return num(0);
    if (name === 'abs') return num(Math.abs(a.n), a.d);
  }
  const t = trigExact(name, a);
  if (t) return t;
  // |e| = e, |pi| = pi, |e^x| = e^x
  if (name === 'abs' && ((a.type === 'sym' && (a.name === 'e' || a.name === 'pi')) ||
    (a.type === 'pow' && a.base.type === 'sym' && a.base.name === 'e'))) return a;
  if (name === 'ln' && a.type === 'sym' && a.name === 'e') return num(1);
  if (name === 'ln' && a.type === 'pow' && a.base.type === 'sym' && a.base.name === 'e') return a.exp;
  return fn(name, a);
}

// sin, cos, tan at multiples of pi/6 and pi/4
const SQ2 = () => mul([num(1, 2), pow(num(2), num(1, 2))]);
const SQ3 = () => mul([num(1, 2), pow(num(3), num(1, 2))]);
function trigExact(name, a) {
  if (!['sin', 'cos', 'tan'].includes(name)) return null;
  let k;
  if (a.type === 'sym' && a.name === 'pi') k = num(1);
  else if (a.type === 'mul' && a.factors.length === 2 && a.factors[0].type === 'num' &&
    a.factors[1].type === 'sym' && a.factors[1].name === 'pi') k = a.factors[0];
  else return null;
  if (![1, 2, 3, 4, 6].includes(k.d)) return null;
  const x = Math.PI * k.n / k.d;
  const v = name === 'sin' ? Math.sin(x) : name === 'cos' ? Math.cos(x) : Math.tan(x);
  if (Math.abs(v) > 1e6) return null;
  const known = [[0, () => num(0)], [0.5, () => num(1, 2)], [1, () => num(1)],
    [Math.SQRT2 / 2, SQ2], [Math.sqrt(3) / 2, SQ3], [Math.sqrt(3), () => pow(num(3), num(1, 2))],
    [Math.sqrt(3) / 3, () => mul([num(1, 3), pow(num(3), num(1, 2))])]];
  for (const [val, make] of known) {
    if (Math.abs(Math.abs(v) - val) < 1e-12) return simplify(v < 0 ? mul([num(-1), make()]) : make());
  }
  return null;
}

// ---------- expansion ----------

const termsOf = n => (n.type === 'add' ? n.terms : [n]);

export function expand(n) {
  switch (n.type) {
    case 'add': return simplify(add(n.terms.map(expand)));
    case 'mul': {
      let acc = [num(1)];
      for (const f of n.factors.map(expand)) {
        const ts = termsOf(f);
        if (acc.length * ts.length > 400) return simplify(mul(n.factors));
        const nextAcc = [];
        for (const a of acc) for (const t of ts) nextAcc.push(simplify(mul([a, t])));
        acc = nextAcc;
      }
      return simplify(add(acc));
    }
    case 'pow': {
      const b = expand(n.base);
      if (b.type === 'add' && n.exp.type === 'num' && n.exp.d === 1 && n.exp.n >= 2 && n.exp.n <= 6)
        return expand(mul(Array(n.exp.n).fill(b)));
      return simplify(pow(b, n.exp));
    }
    default: return simplify(n);
  }
}

// Final, student-friendly form: products inside sums are multiplied out and like terms
// combined, but a top-level product such as 6x(x^2+1)^2 stays factored.
export function pretty(n) {
  n = simplify(n);
  switch (n.type) {
    case 'eq': return eq(pretty(n.lhs), pretty(n.rhs));
    case 'add': return expand(add(n.terms.map(prettyKeep)));
    case 'mul': {
      // 6(x y' + y) -> 6x y' + 6y
      if (n.factors.length === 2 && n.factors[0].type === 'num' && n.factors[1].type === 'add') return expand(n);
      return simplify(mul(n.factors.map(pretty)));
    }
    case 'pow': return simplify(pow(pretty(n.base), n.exp));
    case 'fn': return simplify(fn(n.name, pretty(n.arg)));
    default: return n;
  }
}
// inside a sum, keep function arguments and powers tidy but let expand() distribute products
function prettyKeep(t) {
  if (t.type === 'fn') return pretty(t);
  if (t.type === 'mul') return mul(t.factors.map(f => (f.type === 'fn' ? pretty(f) : f)));
  return t;
}

// ---------- common factors ----------

const rgcd = (a, b) => num(gcd(a.n, b.n), a.d * b.d / gcd(a.d, b.d));

function factorMap(t) {
  // term -> Map(key(base) -> {base, exp(num)}) for factors with numeric exponent
  const [c, rest] = splitCoef(t);
  const m = new Map();
  if (rest) for (const f of rest.type === 'mul' ? rest.factors : [rest]) {
    const base = f.type === 'pow' && f.exp.type === 'num' ? f.base : f;
    const exp = f.type === 'pow' && f.exp.type === 'num' ? f.exp : num(1);
    m.set(key(base), { base, exp });
  }
  return { c, m };
}

// x^2 e^x + 2x e^x  ->  x e^x (x + 2).  Returns the node unchanged if there is nothing to pull out.
export function factorCommon(n) {
  if (n.type !== 'add') return n;
  const maps = n.terms.map(factorMap);
  let content = maps[0].c;
  for (const { c } of maps.slice(1)) content = rgcd(content, c);
  if (maps[0].c.n < 0) content = num(-content.n, content.d);
  const common = [];
  for (const [k, { base, exp }] of maps[0].m) {
    let minE = exp;
    let inAll = true;
    for (const { m } of maps.slice(1)) {
      const o = m.get(k);
      if (!o) { inAll = false; break; }
      if (o.exp.n / o.exp.d < minE.n / minE.d) minE = o.exp;
    }
    if (inAll) common.push(pow(base, minE));
  }
  if (!common.length && isOne(content)) return n;
  const pulled = simplify(mul([content, ...common]));
  const inner = simplify(add(n.terms.map(t => mul([t, pow(pulled, num(-1))]))));
  return simplify(mul([pulled, inner]));
}

// Numerator / denominator over a common denominator with integer content removed.
export function tidyFraction(N, D) {
  N = expand(N); D = expand(D);
  const coefs = [...termsOf(N), ...termsOf(D)].map(t => splitCoef(t)[0]);
  let g = coefs[0];
  for (const c of coefs.slice(1)) g = rgcd(g, c);
  if (isNegative(termsOf(D)[0])) g = num(-g.n, g.d);
  if (!isZero(g) && !isOne(g)) {
    const inv = num(g.d, g.n);
    N = expand(mul([inv, N])); D = expand(mul([inv, D]));
  }
  return simplify(mul([N, pow(D, num(-1))]));
}

function isNegative(t) {
  return (t.type === 'num' && t.n < 0) || (t.type === 'mul' && t.factors[0].type === 'num' && t.factors[0].n < 0);
}

export { sym, children };
