// Step-by-step differentiation, including implicit differentiation and related rates.
import {
  num, sym, add, mul, pow, fn, eq, neg, sub, div, deriv, freeSyms, toTex, dTex, symTex,
  isNum, HALF, contains,
} from './expr.js';
import { simplify, pretty, expand, splitCoef, tidyFraction } from './simplify.js';

// Derivative of the outer function, written in terms of the inner function u.
const OUTER = {
  sin: u => fn('cos', u),
  cos: u => neg(fn('sin', u)),
  tan: u => pow(fn('sec', u), num(2)),
  sec: u => mul([fn('sec', u), fn('tan', u)]),
  csc: u => neg(mul([fn('csc', u), fn('cot', u)])),
  cot: u => neg(pow(fn('csc', u), num(2))),
  asin: u => pow(sub(num(1), pow(u, num(2))), num(-1, 2)),
  acos: u => neg(pow(sub(num(1), pow(u, num(2))), num(-1, 2))),
  atan: u => pow(add([num(1), pow(u, num(2))]), num(-1)),
  ln: u => pow(u, num(-1)),
  log: u => pow(mul([u, fn('ln', num(10))]), num(-1)),
  abs: u => mul([u, pow(fn('abs', u), num(-1))]),
};

const FN_RULE = {
  sin: ['Derivative of sine', '\\frac{d}{dV}[\\sin(u)] = \\cos(u)\\cdot u\''],
  cos: ['Derivative of cosine', '\\frac{d}{dV}[\\cos(u)] = -\\sin(u)\\cdot u\''],
  tan: ['Derivative of tangent', '\\frac{d}{dV}[\\tan(u)] = \\sec^2(u)\\cdot u\''],
  sec: ['Derivative of secant', '\\frac{d}{dV}[\\sec(u)] = \\sec(u)\\tan(u)\\cdot u\''],
  csc: ['Derivative of cosecant', '\\frac{d}{dV}[\\csc(u)] = -\\csc(u)\\cot(u)\\cdot u\''],
  cot: ['Derivative of cotangent', '\\frac{d}{dV}[\\cot(u)] = -\\csc^2(u)\\cdot u\''],
  asin: ['Derivative of arcsine', '\\frac{d}{dV}[\\arcsin(u)] = \\frac{u\'}{\\sqrt{1-u^2}}'],
  acos: ['Derivative of arccosine', '\\frac{d}{dV}[\\arccos(u)] = -\\frac{u\'}{\\sqrt{1-u^2}}'],
  atan: ['Derivative of arctangent', '\\frac{d}{dV}[\\arctan(u)] = \\frac{u\'}{1+u^2}'],
  ln: ['Derivative of natural log', '\\frac{d}{dV}[\\ln(u)] = \\frac{u\'}{u}'],
  log: ['Derivative of log base 10', '\\frac{d}{dV}[\\log(u)] = \\frac{u\'}{u\\ln(10)}'],
  abs: ['Derivative of absolute value', '\\frac{d}{dV}[|u|] = \\frac{u}{|u|}\\cdot u\''],
};

// d/dv of node. `deps` is the set of letters that are functions of v (y in dy/dx).
// Returns { result, steps } where steps is a tree for display.
export function differentiate(node, v, deps = new Set()) {
  const vt = symTex(v);
  const F = s => s.replace(/dV/g, `d${vt}`).replace(/\bx\b/g, vt);
  const varies = n => { const s = freeSyms(n); return s.has(v) || [...deps].some(d => s.has(d)); };
  const product = list => (list.length === 1 ? list[0] : mul(list));

  function mk(expr, raw, rule, formula, kids = []) {
    return { raw, step: { expr, result: pretty(raw), rule, formula: formula && F(formula), children: kids.map(k => k.step) } };
  }

  function D(n) {
    if (!varies(n)) return mk(n, num(0), 'Constant rule', '\\frac{d}{dV}[c] = 0');
    switch (n.type) {
      case 'sym':
        if (n.name === v) return mk(n, num(1), 'Variable rule', '\\frac{d}{dV}[x] = 1');
        return mk(n, deriv(n.name, v), 'Implicit differentiation',
          `${symTex(n.name)} \\text{ depends on } ${vt} \\text{, so } \\frac{d}{dV}[${symTex(n.name)}] = ${dTex(n.name, v)}`);
      case 'add': {
        const kids = n.terms.map(D);
        return mk(n, add(kids.map(k => k.raw)), 'Sum/difference rule',
          '\\frac{d}{dV}[f \\pm g] = f\' \\pm g\'', kids);
      }
      case 'mul': {
        const cs = n.factors.filter(f => !varies(f)), vs = n.factors.filter(varies);
        if (cs.length) {
          const k = D(product(vs));
          const c = product(cs);
          return mk(n, mul([c, k.raw]), 'Constant multiple rule', '\\frac{d}{dV}[c\\cdot f] = c\\cdot f\'', [k]);
        }
        const isDen = f => f.type === 'pow' && f.exp.type === 'num' && f.exp.n < 0;
        const numer = vs.filter(f => !isDen(f));
        const denom = vs.filter(isDen).map(f => (isNum(f.exp, -1) ? f.base : pow(f.base, num(-f.exp.n, f.exp.d))));
        if (numer.length && denom.length) {
          const N = product(numer), Dn = product(denom);
          const kN = D(N), kD = D(Dn);
          const raw = div(sub(mul([kN.raw, Dn]), mul([N, kD.raw])), pow(Dn, num(2)));
          return mk(n, raw, 'Quotient rule',
            '\\frac{d}{dV}\\left[\\frac{f}{g}\\right] = \\frac{f\'g - fg\'}{g^2}', [kN, kD]);
        }
        const kids = vs.map(D);
        const raw = add(vs.map((_, i) => mul(vs.map((g, j) => (i === j ? kids[i].raw : g)))));
        return mk(n, raw, 'Product rule',
          vs.length === 2 ? '\\frac{d}{dV}[f g] = f\'g + fg\'' : '\\frac{d}{dV}[f g h] = f\'gh + fg\'h + fgh\'', kids);
      }
      case 'pow': {
        const { base: b, exp: e } = n;
        if (!varies(e)) {
          const outer = mul([e, pow(b, add([e, num(-1)]))]);
          if (b.type === 'sym' && b.name === v)
            return mk(n, outer, 'Power rule', '\\frac{d}{dV}[x^n] = n x^{n-1}');
          const k = D(b);
          if (isNum(e, 1 / 2) && e.d === 2 && e.n === 1)
            return mk(n, mul([outer, k.raw]), 'Chain rule (square root)', '\\frac{d}{dV}[\\sqrt{u}] = \\frac{1}{2\\sqrt{u}}\\cdot u\'', [k]);
          return mk(n, mul([outer, k.raw]), 'Chain rule (power rule)', '\\frac{d}{dV}[u^n] = n u^{n-1}\\cdot u\'', [k]);
        }
        if (!varies(b)) {
          const k = D(e);
          const plain = e.type === 'sym' && e.name === v;
          if (b.type === 'sym' && b.name === 'e')
            return mk(n, mul([n, k.raw]), plain ? 'Exponential rule' : 'Exponential rule + chain rule',
              plain ? '\\frac{d}{dV}[e^x] = e^x' : '\\frac{d}{dV}[e^u] = e^u\\cdot u\'', plain ? [] : [k]);
          return mk(n, mul([n, fn('ln', b), k.raw]), plain ? 'Exponential rule' : 'Exponential rule + chain rule',
            plain ? '\\frac{d}{dV}[a^x] = a^x\\ln(a)' : '\\frac{d}{dV}[a^u] = a^u\\ln(a)\\cdot u\'', plain ? [] : [k]);
        }
        const inner = mul([e, fn('ln', b)]);
        const k = D(inner);
        return mk(n, mul([n, k.raw]), 'Logarithmic differentiation',
          '\\frac{d}{dV}[f^g] = f^g\\cdot\\frac{d}{dV}[g\\ln(f)]', [k]);
      }
      case 'fn': {
        const u = n.arg;
        const outer = OUTER[n.name](u);
        const [rule, formula] = FN_RULE[n.name];
        if (u.type === 'sym' && u.name === v) return mk(n, outer, rule, formula.replace(/\\cdot u'/, '').replace(/u'/g, '1').replace(/u/g, 'x'));
        const k = D(u);
        return mk(n, mul([outer, k.raw]), `${rule} + chain rule`, formula, [k]);
      }
    }
    throw new Error('Cannot differentiate this expression');
  }

  const out = D(node);
  return { result: pretty(out.raw), steps: out.step };
}

// Solve a linear equation for the symbol `target` (e.g. dy/dx). Returns { A, B, solution }
// where the equation was rearranged to A * target = B.
export function solveLinear(equation, target) {
  const E = expand(sub(equation.lhs, equation.rhs));
  const terms = E.type === 'add' ? E.terms : [E];
  const has = t => contains(t, n => n.type === 'sym' && n.name === target.name);
  const A = [], B = [];
  for (const t of terms) {
    if (!has(t)) { B.push(neg(t)); continue; }
    const c = simplify(mul([t, pow(target, num(-1))]));
    if (has(c)) return null;
    A.push(c);
  }
  if (!A.length) return null;
  let An = simplify(add(A)), Bn = simplify(add(B));
  if (isNum(An, 0)) return null;
  // keep the coefficient positive: -3 dy/dx = ...  ->  3 dy/dx = ...
  const lead = An.type === 'add' ? An.terms[0] : An;
  if (splitCoef(lead)[0].n < 0) { An = expand(neg(An)); Bn = expand(neg(Bn)); }
  return { A: An, B: Bn, solution: tidyFraction(Bn, An) };
}

// Differentiate both sides of an equation. Every letter in deps is treated as a function of v.
export function differentiateEquation(equation, v, deps) {
  const L = differentiate(equation.lhs, v, deps);
  const R = differentiate(equation.rhs, v, deps);
  const result = simplify(eq(L.result, R.result));
  const rates = [...deps].filter(d => contains(result, n => n.type === 'sym' && n.deriv && n.deriv.of === d))
    .map(d => deriv(d, v));
  return { result, lhsSteps: L.steps, rhsSteps: R.steps, rates };
}

export { toTex, splitCoef };
