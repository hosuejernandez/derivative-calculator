// Engine tests:  node tests/run.mjs
import { parse, toTex, compile } from '../js/expr.js';
import { simplify, setMainVar } from '../js/simplify.js';
import { differentiate, differentiateEquation, solveLinear } from '../js/diff.js';
import { analyze } from '../js/fdt.js';

let pass = 0, fail = 0;
function check(name, got, want) {
  if (got === want) { pass++; return; }
  fail++;
  console.log(`FAIL ${name}\n   got:  ${got}\n   want: ${want}`);
}

const d = (src, v = 'x') => { setMainVar(v); return toTex(differentiate(simplify(parse(src)), v).result); };

// exact answers
check('quadratic with constants', d('ax^2+bx+c'), '2 a x + b');
check('cubic', d('x^3-3x'), '3 x^{2} - 3');
check('product', d('x e^x'), 'x e^{x} + e^{x}');
check('chain', d('sin(x^2)'), '2 x \\cos\\left(x^{2}\\right)');
check('quotient', d('(x^2+1)/(x-1)'), '\\frac{x^{2} - 2 x - 1}{\\left(x - 1\\right)^{2}}');
check('log quotient', d('ln(x)/x'), '\\frac{1 - \\ln\\left(x\\right)}{x^{2}}');
check('cusp', d('x^(2/3)'), '\\frac{2}{3 \\sqrt[3]{x}}');
check('ln|x|', d('ln|x|'), '\\frac{1}{x}');
check('wrt t with constant', d('a t^2 + v t', 't'), '2 a t + v');

// implicit and related rates
function implicit(src, v, deps) {
  setMainVar(v);
  return differentiateEquation(simplify(parse(src)), v, new Set(deps));
}
let r = implicit('x^2+y^2=25', 'x', ['y']);
check('circle d/dx', toTex(solveLinear(r.result, r.rates[0]).solution), '-\\frac{x}{y}');
r = implicit('x^2+y^2=25', 't', ['x', 'y']);
check('circle d/dt', toTex(r.result), '2 x \\frac{dx}{dt} + 2 y \\frac{dy}{dt} = 0');
r = implicit('V = (1/3) pi r^2 h', 't', ['V', 'r', 'h']);
check('cone d/dt', toTex(r.result), '\\frac{dV}{dt} = \\frac{\\pi}{3} \\left(r^{2} \\frac{dh}{dt} + 2 h r \\frac{dr}{dt}\\right)');
r = implicit('x^3+y^3=6xy', 'x', ['y']);
check('folium', toTex(solveLinear(r.result, r.rates[0]).solution), '\\frac{x^{2} - 2 y}{2 x - y^{2}}');

// First Derivative Test
function fdt(src) {
  setMainVar('x');
  const f = simplify(parse(src));
  return analyze(f, differentiate(f, 'x').result, 'x');
}
const summary = a => a.points.map(p => `${p.tex}:${p.type}`).join(' ');
check('fdt cubic', summary(fdt('x^3-3x')), '-1:max 1:min');
check('fdt cubic inc', fdt('x^3-3x').increasing.join(' U '), '(-\\infty, -1) U (1, \\infty)');
check('fdt cusp', summary(fdt('x^(2/3)')), '0:min');
check('fdt no extremum', summary(fdt('x^4-4x^3')), '0:neither 3:min');
check('fdt rational', fdt('(x^2+1)/(x-1)').domainTex, '(-\\infty, 1) \\cup (1, \\infty)');
check('fdt x e^x', summary(fdt('x e^x')), '-1:min');
check('fdt ln(x)/x', summary(fdt('ln(x)/x')), 'e:max');
check('fdt x ln x', summary(fdt('x ln x')), '\\frac{1}{e}:min');
check('fdt cbrt', summary(fdt('x^(2/3)(x-5)')), '0:max 2:min');
check('fdt semicircle', summary(fdt('sqrt(4-x^2)')), '0:max');
check('fdt sin', summary(fdt('sin x')), '-\\frac{3 \\pi}{2}:max -\\frac{\\pi}{2}:min \\frac{\\pi}{2}:max \\frac{3 \\pi}{2}:min');

// infinitely many critical numbers: capped, with the general pattern shown
const many = fdt('cos(e^(2x))');
check('cap count', many.points.length <= 8 && many.truncated, true);
check('cap first point', Math.abs(many.points[0].x - Math.log(Math.PI) / 2) < 1e-6, true);
check('cap general', many.general.some(t => t.includes('\\ln\\left(k\\pi\\right)')), true);
const sinx = fdt('sin x');
check('sin not truncated', sinx.truncated === false && sinx.points.length === 4, true);

// concavity: run the same analysis on f''
function conc(src) {
  setMainVar('x');
  const f = simplify(parse(src));
  const fpp = differentiate(differentiate(f, 'x').result, 'x').result;
  return analyze(f, fpp, 'x', { prime: '″', pointWord: 'possible inflection points' });
}
const infl = a => a.points.map(p => `${p.tex}:${p.type === 'neither' ? 'no' : 'yes'}`).join(' ');
check('conc cubic', infl(conc('x^3-3x')), '0:yes');
check('conc cubic up', conc('x^3-3x').increasing.join(' U '), '(0, \\infty)');
check('conc quartic', infl(conc('x^4')), '0:no');
check('conc x^4-4x^3', infl(conc('x^4-4x^3')), '0:yes 2:yes');
check('conc cube root', infl(conc('x^(1/3)')), '0:yes');
check('conc 1/x', conc('1/x').points.length + ' ' + conc('1/x').increasing.join(' U '), '0 (0, \\infty)');
check('conc gaussian', infl(conc('e^(-x^2)')), '-\\frac{\\sqrt{2}}{2}:yes \\frac{\\sqrt{2}}{2}:yes');

// every derivative agrees with a finite difference at random points
const FUNCS = ['x^3-3x', 'x e^x', 'sin(x^2)', 'ln(x)/x', '(x^2+1)/(x-1)', 'x^(2/3)(x-5)', 'sqrt(x^2+1)',
  'x^x', 'tan x', '1/x^2', 'x^2(x+1)^3', 'e^(-x^2)', '2^x', 'arctan(2x)', 'sin^2 x', 'ln|x|', 'cos(3x)sin(x)',
  'sec(x)', 'csc(x) cot(x)', 'arcsin(x/2)', 'log(x)', 'sqrt(x)/(1+x)', 'e^(sin x)', '(2x+1)^(1/3)', 'x/sqrt(x^2+4)'];
for (const src of FUNCS) {
  setMainVar('x');
  const f = simplify(parse(src));
  const fp = differentiate(f, 'x').result;
  const F = compile(f), FP = compile(fp);
  let worst = 0;
  for (let i = 0; i < 30; i++) {
    const x = 0.2 + Math.random() * 1.6;
    const h = 1e-6;
    const num = (F({ x: x + h }) - F({ x: x - h })) / (2 * h);
    const err = Math.abs(num - FP({ x })) / (1 + Math.abs(num));
    if (isFinite(err)) worst = Math.max(worst, err);
  }
  check(`numeric ${src}`, worst < 1e-5 ? 'ok' : `max error ${worst} for f'=${toTex(fp)}`, 'ok');
}

console.log(`\n${pass} passed, ${fail} failed`);
process.exit(fail ? 1 : 0);
