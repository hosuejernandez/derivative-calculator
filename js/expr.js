// Expression trees: constructors, parser, LaTeX printer and numeric evaluation.
//
// Node shapes:
//   { type: 'num', n, d }            exact rational n/d (d > 0, reduced)
//   { type: 'sym', name, deriv? }    variable or constant (pi, e); deriv = { of, wrt } for dy/dx
//   { type: 'add', terms }
//   { type: 'mul', factors }
//   { type: 'pow', base, exp }
//   { type: 'fn', name, arg }        sin, cos, tan, sec, csc, cot, asin, acos, atan, ln, log, abs
//   { type: 'eq', lhs, rhs }         only at the top level

// ---------- rationals ----------

export function gcd(a, b) {
  a = Math.abs(a); b = Math.abs(b);
  while (b) [a, b] = [b, a % b];
  return a;
}

export function num(n, d = 1) {
  if (d === 0) throw new Error('Division by zero');
  if (!Number.isSafeInteger(n) || !Number.isSafeInteger(d)) throw new Error('A number got too large to handle exactly');
  if (d < 0) { n = -n; d = -d; }
  const g = gcd(n, d) || 1;
  return { type: 'num', n: n / g, d: d / g };
}

export const radd = (a, b) => num(a.n * b.d + b.n * a.d, a.d * b.d);
export const rmul = (a, b) => num(a.n * b.n, a.d * b.d);
export const rdiv = (a, b) => num(a.n * b.d, a.d * b.n);
export const isNum = (n, v) => n.type === 'num' && (v === undefined || n.n === v * n.d);
export const isZero = n => n.type === 'num' && n.n === 0;
export const isOne = n => n.type === 'num' && n.n === 1 && n.d === 1;
export const numVal = n => n.n / n.d;

// ---------- constructors ----------

export const sym = name => ({ type: 'sym', name });
export const add = terms => ({ type: 'add', terms });
export const mul = factors => ({ type: 'mul', factors });
export const pow = (base, exp) => ({ type: 'pow', base, exp });
export const fn = (name, arg) => ({ type: 'fn', name, arg });
export const eq = (lhs, rhs) => ({ type: 'eq', lhs, rhs });
export const deriv = (of, wrt) => ({ type: 'sym', name: `d${of}/d${wrt}`, deriv: { of, wrt } });
export const neg = a => mul([num(-1), a]);
export const sub = (a, b) => add([a, neg(b)]);
export const div = (a, b) => mul([a, pow(b, num(-1))]);
export const HALF = num(1, 2);

// ---------- structure helpers ----------

export function key(n) {
  switch (n.type) {
    case 'num': return n.d === 1 ? `${n.n}` : `${n.n}/${n.d}`;
    case 'sym': return n.name;
    case 'add': return `+(${n.terms.map(key).join(',')})`;
    case 'mul': return `*(${n.factors.map(key).join(',')})`;
    case 'pow': return `^(${key(n.base)},${key(n.exp)})`;
    case 'fn': return `${n.name}(${key(n.arg)})`;
    case 'eq': return `${key(n.lhs)}=${key(n.rhs)}`;
  }
}

export const same = (a, b) => key(a) === key(b);
export const CONSTANT_NAMES = new Set(['pi', 'e']);

export function children(n) {
  switch (n.type) {
    case 'add': return n.terms;
    case 'mul': return n.factors;
    case 'pow': return [n.base, n.exp];
    case 'fn': return [n.arg];
    case 'eq': return [n.lhs, n.rhs];
    default: return [];
  }
}

// Letters in the expression (pi and e are numbers, not letters).
export function freeSyms(n, out = new Set()) {
  if (n.type === 'sym') { if (!CONSTANT_NAMES.has(n.name)) out.add(n.name); }
  else children(n).forEach(c => freeSyms(c, out));
  return out;
}

export function contains(n, pred) {
  if (pred(n)) return true;
  return children(n).some(c => contains(c, pred));
}

export function size(n) {
  return 1 + children(n).reduce((s, c) => s + size(c), 0);
}

export function substitute(n, map) {
  switch (n.type) {
    case 'sym': return map[n.name] !== undefined ? map[n.name] : n;
    case 'num': return n;
    case 'add': return add(n.terms.map(t => substitute(t, map)));
    case 'mul': return mul(n.factors.map(t => substitute(t, map)));
    case 'pow': return pow(substitute(n.base, map), substitute(n.exp, map));
    case 'fn': return fn(n.name, substitute(n.arg, map));
    case 'eq': return eq(substitute(n.lhs, map), substitute(n.rhs, map));
  }
}

// ---------- parser ----------

const FUNCS = new Set(['sin', 'cos', 'tan', 'sec', 'csc', 'cot', 'asin', 'acos', 'atan',
  'arcsin', 'arccos', 'arctan', 'ln', 'log', 'sqrt', 'cbrt', 'exp', 'abs']);
// Longest names first so "arcsin" wins over "sin" and "sqrt" over "s".
const NAMES = ['arcsin', 'arccos', 'arctan', 'theta', 'alpha', 'sqrt', 'cbrt', 'asin', 'acos', 'atan',
  'beta', 'sin', 'cos', 'tan', 'sec', 'csc', 'cot', 'exp', 'abs', 'log', 'phi', 'ln', 'pi'];
const GREEK = { 'π': 'pi', 'θ': 'theta', 'α': 'alpha', 'β': 'beta', 'φ': 'phi' };
const INVERSE = { sin: 'asin', cos: 'acos', tan: 'atan' };
const ALIAS = { arcsin: 'asin', arccos: 'acos', arctan: 'atan' };

function tokenize(src) {
  const s = src.replace(/\*\*/g, '^').replace(/[·×∙⋅]/g, '*').replace(/[−–—]/g, '-').replace(/÷/g, '/');
  const toks = [];
  let i = 0;
  while (i < s.length) {
    const c = s[i];
    if (/\s/.test(c)) { i++; continue; }
    if (/[0-9.]/.test(c)) {
      const m = /^\d*\.?\d+|^\d+\.?/.exec(s.slice(i));
      if (!m) throw new Error(`Unexpected "${c}"`);
      toks.push({ t: 'num', v: m[0] }); i += m[0].length; continue;
    }
    if (/[a-zA-Zπθαβφ]/.test(c)) {
      const run = /^[a-zA-Zπθαβφ]+/.exec(s.slice(i))[0];
      i += run.length;
      let j = 0;
      while (j < run.length) {
        if (GREEK[run[j]]) { toks.push({ t: 'sym', v: GREEK[run[j]] }); j++; continue; }
        const name = NAMES.find(nm => run.startsWith(nm, j));
        if (name) {
          toks.push(FUNCS.has(name) ? { t: 'fn', v: ALIAS[name] || name } : { t: 'sym', v: name });
          j += name.length;
        } else { toks.push({ t: 'sym', v: run[j] }); j++; }
      }
      continue;
    }
    if (c === '√') { toks.push({ t: 'fn', v: 'sqrt' }); i++; continue; }
    if ('+-*/^()|=_,'.includes(c)) { toks.push({ t: c }); i++; continue; }
    if ('[{'.includes(c)) { toks.push({ t: '(' }); i++; continue; }
    if (']}'.includes(c)) { toks.push({ t: ')' }); i++; continue; }
    throw new Error(`I don't understand the character "${c}"`);
  }
  return toks;
}

function parseNumber(str) {
  if (!str.includes('.')) return num(parseInt(str, 10));
  const [a, b = ''] = str.split('.');
  const d = 10 ** b.length;
  return num(parseInt((a || '0') + b, 10), d);
}

export function parse(src) {
  if (!src || !src.trim()) throw new Error('Type a function to differentiate');
  const toks = tokenize(src);
  let p = 0;
  const peek = () => toks[p];
  const at = t => toks[p] && toks[p].t === t;
  const next = () => toks[p++];
  const expect = t => {
    if (!at(t)) throw new Error(t === ')' ? 'Missing a closing parenthesis ")"' : `Expected "${t}"`);
    return next();
  };

  function equation() {
    const lhs = expr();
    if (at('=')) {
      next();
      const rhs = expr();
      if (at('=')) throw new Error('Only one "=" sign is allowed');
      return eq(lhs, rhs);
    }
    return lhs;
  }

  function expr() {
    const terms = [term()];
    while (at('+') || at('-')) {
      const op = next().t;
      const t = term();
      terms.push(op === '-' ? neg(t) : t);
    }
    return terms.length === 1 ? terms[0] : add(terms);
  }

  const startsFactor = tk => tk && ['num', 'sym', 'fn', '('].includes(tk.t);

  function term() {
    const fs = [unary()];
    for (;;) {
      if (at('*')) { next(); fs.push(unary()); }
      else if (at('/')) { next(); fs.push(pow(unary(), num(-1))); }
      else if (startsFactor(peek())) fs.push(power());
      else break;
    }
    return fs.length === 1 ? fs[0] : mul(fs);
  }

  function unary() {
    if (at('-')) { next(); return neg(unary()); }
    if (at('+')) { next(); return unary(); }
    return power();
  }

  function exponent() {
    if (at('-')) { next(); return neg(exponent()); }
    if (at('+')) { next(); return exponent(); }
    return power();
  }

  function power() {
    const b = primary();
    if (at('^')) { next(); return pow(b, exponent()); }
    return b;
  }

  function primary() {
    const tk = next();
    if (!tk) throw new Error('The expression ends too early');
    switch (tk.t) {
      case 'num': return parseNumber(tk.v);
      case 'sym': return sym(tk.v);
      case '(': { const e = expr(); expect(')'); return e; }
      case '|': { const e = expr(); expect('|'); return fn('abs', e); }
      case 'fn': return func(tk.v);
      default: throw new Error(`Unexpected "${tk.t}"`);
    }
  }

  function func(name) {
    let power = null, base = null;
    if (at('^')) { next(); power = exponent(); }
    if (name === 'log' && at('_')) { next(); base = primary(); }
    let arg;
    if (at('(')) { next(); arg = expr(); expect(')'); }
    else if (at('|')) arg = primary();
    else {
      // sin x, sin 2x, sin x^2: the argument is the run of numbers and letters that follows
      if (!peek() || !['num', 'sym'].includes(peek().t)) throw new Error(`${name} needs an input, like ${name}(x)`);
      const fs = [power_()];
      while (peek() && ['num', 'sym'].includes(peek().t)) fs.push(power_());
      arg = fs.length === 1 ? fs[0] : mul(fs);
    }
    let out;
    const inverse = power && power.type === 'mul' && power.factors.length === 2 &&
      isNum(power.factors[0], -1) && isNum(power.factors[1], 1);
    if (inverse && INVERSE[name]) return fn(INVERSE[name], arg);
    switch (name) {
      case 'sqrt': out = pow(arg, HALF); break;
      case 'cbrt': out = pow(arg, num(1, 3)); break;
      case 'exp': out = pow(sym('e'), arg); break;
      case 'log': out = base ? div(fn('ln', arg), fn('ln', base)) : fn('log', arg); break;
      default: out = fn(name, arg);
    }
    return power ? pow(out, power) : out;
  }
  const power_ = power;

  const result = equation();
  if (p < toks.length) {
    const tk = toks[p];
    throw new Error(tk.t === ')' ? 'There is an extra ")"' : `Unexpected "${tk.v || tk.t}"`);
  }
  return result;
}

// ---------- LaTeX ----------

const FN_TEX = {
  sin: '\\sin', cos: '\\cos', tan: '\\tan', sec: '\\sec', csc: '\\csc', cot: '\\cot',
  asin: '\\arcsin', acos: '\\arccos', atan: '\\arctan', ln: '\\ln', log: '\\log',
};
const SYM_TEX = { pi: '\\pi', theta: '\\theta', alpha: '\\alpha', beta: '\\beta', phi: '\\phi' };

export const symTex = name => SYM_TEX[name] || name;
export const dTex = (of, wrt) => `\\frac{d${symTex(of)}}{d${symTex(wrt)}}`;

export function isNegative(t) {
  return (t.type === 'num' && t.n < 0) ||
    (t.type === 'mul' && t.factors[0].type === 'num' && t.factors[0].n < 0);
}

export function negateDisplay(t) {
  if (t.type === 'num') return num(-t.n, t.d);
  if (t.type === 'mul') {
    const c = num(-t.factors[0].n, t.factors[0].d);
    const rest = t.factors.slice(1);
    if (isOne(c)) return rest.length === 1 ? rest[0] : mul(rest);
    return mul([c, ...rest]);
  }
  return neg(t);
}

export function toTex(n) {
  switch (n.type) {
    case 'eq': return `${toTex(n.lhs)} = ${toTex(n.rhs)}`;
    case 'num':
      if (n.d === 1) return `${n.n}`;
      return n.n < 0 ? `-\\frac{${-n.n}}{${n.d}}` : `\\frac{${n.n}}{${n.d}}`;
    case 'sym': return n.deriv ? dTex(n.deriv.of, n.deriv.wrt) : symTex(n.name);
    case 'add': return leadPositive(n.terms).map((t, i) => {
      const negative = isNegative(t);
      const tex = toTex(negative ? negateDisplay(t) : t);
      if (i === 0) return negative ? `-${tex}` : tex;
      return negative ? ` - ${tex}` : ` + ${tex}`;
    }).join('');
    case 'mul': return mulTex(n);
    case 'pow': return powTex(n);
    case 'fn': return n.name === 'abs'
      ? `\\left|${toTex(n.arg)}\\right|`
      : `${FN_TEX[n.name]}\\left(${toTex(n.arg)}\\right)`;
  }
}

// Display -ln(x) + 1 as 1 - ln(x): start with a positive term when there is one.
function leadPositive(terms) {
  if (!isNegative(terms[0])) return terms;
  const i = terms.findIndex(t => !isNegative(t));
  return i < 0 ? terms : [terms[i], ...terms.slice(0, i), ...terms.slice(i + 1)];
}

const needsParensInProduct = f => f.type === 'add' || (f.type === 'num' && (f.n < 0 || f.d !== 1));

function factorsTex(list) {
  let out = '';
  list.forEach((f, i) => {
    let tex = toTex(f);
    if (needsParensInProduct(f) && (list.length > 1 || i > 0)) tex = `\\left(${tex}\\right)`;
    if (i > 0 && /^[0-9]/.test(tex)) out += ' \\cdot ';
    else if (i > 0) out += ' ';
    out += tex;
  });
  return out;
}

function mulTex(n) {
  let coef = num(1);
  const numer = [], denom = [], rates = [];
  for (const f of n.factors) {
    if (f.type === 'num') coef = rmul(coef, f);
    else if (f.type === 'sym' && f.deriv) rates.push(f);
    else if (f.type === 'pow' && f.exp.type === 'num' && f.exp.n < 0) {
      const e = num(-f.exp.n, f.exp.d);
      denom.push(isOne(e) ? f.base : pow(f.base, e));
    } else numer.push(f);
  }
  // keep dx/dt outside a fraction:  (x/y) dx/dt  rather than  (x dx/dt)/y
  if (rates.length && (denom.length || coef.d !== 1)) {
    const rest = n.factors.filter(f => !(f.type === 'sym' && f.deriv));
    const front = rest.length === 1 ? toTex(rest[0]) : mulTex(mul(rest));
    return `${front === '1' ? '' : front === '-1' ? '-' : front} ${rates.map(toTex).join(' ')}`;
  }
  numer.push(...rates);
  const sign = coef.n < 0 ? '-' : '';
  const cn = Math.abs(coef.n), cd = coef.d;
  const wrapSum = (list, c) => {
    // A lone sum on top or bottom of a fraction needs no parentheses.
    if (list.length === 1 && c === 1) return toTex(list[0]);
    const parts = c !== 1 ? [num(c), ...list] : list;
    return parts.length ? factorsTex(parts) : '1';
  };
  if (denom.length) return `${sign}\\frac{${wrapSum(numer, cn)}}{${wrapSum(denom, cd)}}`;
  if (cd !== 1) {
    if (!numer.length) return `${sign}\\frac{${cn}}{${cd}}`;
    // 3pi/2 rather than (3/2) pi when the top is just letters and powers
    if (numer.every(f => f.type === 'sym' || (f.type === 'pow' && f.base.type === 'sym')))
      return `${sign}\\frac{${wrapSum(numer, cn)}}{${cd}}`;
    // pi/3 (r^2 + ...) : letters go on top of the fraction, sums and functions after it
    const simpleF = f => f.type === 'sym' || (f.type === 'pow' && f.base.type === 'sym');
    const top = numer.filter(simpleF), after = numer.filter(f => !simpleF(f));
    const rest = after.length === 1 && after[0].type === 'add'
      ? `\\left(${toTex(after[0])}\\right)` : factorsTex(after);
    return `${sign}\\frac{${wrapSum(top, cn)}}{${cd}} ${rest}`;
  }
  if (!numer.length) return `${sign}${cn}`;
  if (cn === 1) {
    if (numer.length === 1 && numer[0].type === 'add') return `${sign}\\left(${toTex(numer[0])}\\right)`;
    return sign + factorsTex(numer);
  }
  return sign + factorsTex([num(cn), ...numer]);
}

function wrapBase(b) {
  const tex = toTex(b);
  const simple = (b.type === 'sym' && !b.deriv) || (b.type === 'num' && b.d === 1 && b.n >= 0) ||
    (b.type === 'fn' && b.name === 'abs');
  return simple ? tex : `\\left(${tex}\\right)`;
}

function powTex(n) {
  const { base, exp } = n;
  if (exp.type === 'num') {
    if (exp.n < 0) return `\\frac{1}{${powTex(pow(base, num(-exp.n, exp.d)))}}`;
    if (isOne(exp)) return toTex(base);
    if (exp.n === 1 && exp.d === 2) return `\\sqrt{${toTex(base)}}`;
    if (exp.n === 1) return `\\sqrt[${exp.d}]{${toTex(base)}}`;
    if (exp.d === 1) {
      if (base.type === 'fn' && base.name !== 'abs')
        return `${FN_TEX[base.name]}^{${exp.n}}\\left(${toTex(base.arg)}\\right)`;
      return `${wrapBase(base)}^{${exp.n}}`;
    }
    return `${wrapBase(base)}^{\\frac{${exp.n}}{${exp.d}}}`;
  }
  return `${wrapBase(base)}^{${toTex(exp)}}`;
}

// ---------- numeric evaluation ----------

const FN_EVAL = {
  sin: Math.sin, cos: Math.cos, tan: Math.tan,
  sec: x => 1 / Math.cos(x), csc: x => 1 / Math.sin(x), cot: x => 1 / Math.tan(x),
  asin: Math.asin, acos: Math.acos, atan: Math.atan,
  ln: Math.log, log: Math.log10, abs: Math.abs,
};

// Compile to a fast function of an environment object { x: 1.5, ... }.
export function compile(n) {
  switch (n.type) {
    case 'num': { const v = n.n / n.d; return () => v; }
    case 'sym':
      if (n.name === 'pi') return () => Math.PI;
      if (n.name === 'e') return () => Math.E;
      return env => (env[n.name] === undefined ? NaN : env[n.name]);
    case 'add': {
      const fs = n.terms.map(compile);
      return env => { let s = 0; for (const f of fs) s += f(env); return s; };
    }
    case 'mul': {
      const fs = n.factors.map(compile);
      return env => { let s = 1; for (const f of fs) s *= f(env); return s; };
    }
    case 'pow': {
      const b = compile(n.base);
      if (n.exp.type === 'num') {
        const { n: p, d: q } = n.exp;
        const e = p / q;
        if (q === 1) return env => Math.pow(b(env), e);
        if (q % 2 === 1) {
          // Odd roots of negative numbers are real: (-8)^(1/3) = -2.
          return env => {
            const x = b(env);
            if (x < 0) { const r = Math.pow(-x, e); return p % 2 === 0 ? r : -r; }
            return Math.pow(x, e);
          };
        }
        return env => Math.pow(b(env), e);
      }
      const e = compile(n.exp);
      return env => Math.pow(b(env), e(env));
    }
    case 'fn': { const a = compile(n.arg), f = FN_EVAL[n.name]; return env => f(a(env)); }
    default: throw new Error('Cannot evaluate an equation');
  }
}

export function evalAt(n, env) { return compile(n)(env); }
