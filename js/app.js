// Page wiring: read the inputs, run the math, render the derivative, analysis and graph.
import {
  parse, toTex, freeSyms, substitute, compile, num, sym, deriv, dTex, symTex, contains, sub,
} from './expr.js';
import { simplify, setMainVar, pretty } from './simplify.js';
import { differentiate, differentiateEquation, solveLinear } from './diff.js';
import { analyze } from './fdt.js';
import { Graph } from './graph.js';
import { fmt } from './solve.js';

const $ = id => document.getElementById(id);
const M = (tex, display = false) => katex.renderToString(tex, { throwOnError: false, displayMode: display });
const esc = s => s.replace(/[&<>"]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));

const EXAMPLES = [
  ['x^3 - 3x', 'x', 'Cubic: one max, one min'],
  ['ax^2 + bx + c', 'x', 'Quadratic with constants a, b, c'],
  ['(x^2 + 1)/(x - 1)', 'x', 'Quotient rule'],
  ['x e^x', 'x', 'Product rule'],
  ['sin(x^2)', 'x', 'Chain rule'],
  ['ln(x)/x', 'x', 'Logarithm'],
  ['x^(2/3)(x - 5)', 'x', 'Cusp: f′ undefined'],
  ['x^4 - 4x^3', 'x', 'Critical point that is not an extremum'],
  ['sqrt(4 - x^2)', 'x', 'Domain endpoints'],
  ['sin(x) + cos(x)', 'x', 'Trig (one window)'],
  ['f(x) = x^2 e^(-x)', 'x', 'Named function f(x) = …'],
  ['y = x^3 - 6x^2 + 2', 'x', 'y = … form'],
  ['x^2 + y^2 = 25', 'x', 'Implicit: circle'],
  ['x^3 + y^3 = 6xy', 'x', 'Implicit: folium of Descartes'],
  ['x^2 + y^2 = 25', 't', 'Related rates: circle, d/dt'],
  ['V = (1/3) pi r^2 h', 't', 'Related rates: cone volume'],
  ['A = pi r^2', 't', 'Related rates: circle area'],
  ['x^x', 'x', 'Logarithmic differentiation'],
];

// Letters that are treated as constants unless the student says otherwise.
const CONSTANT_LETTERS = new Set(['a', 'b', 'c', 'd', 'k', 'm', 'n']);

const state = {
  overrides: new Map(),     // letter -> true (depends on wrt) / false (constant)
  overridesFor: '',         // wrt variable the overrides belong to
  params: new Map(),        // constant letter -> value string
  current: null,            // last successful computation (for second derivative, eval)
};

let graph;

// ---------- input handling ----------

function splitNamed(src) {
  // "f(x) = ..." -> { name: 'f', arg: 'x', body: '...' }
  const m = /^\s*([a-zA-Z])\s*\(\s*([a-zA-Z])\s*\)\s*=(.*)$/.exec(src);
  return m ? { name: m[1], arg: m[2], body: m[3] } : null;
}

function readWrt() {
  const v = $('wrt').value.trim();
  if (!v) throw new Error('Type the variable to differentiate with respect to (usually x).');
  const parsed = parse(v);
  if (parsed.type !== 'sym' || ['pi', 'e'].includes(parsed.name)) throw new Error(`"${v}" can't be the variable. Use a single letter like x or t.`);
  return parsed.name;
}

function readInput() {
  const src = $('expr').value;
  const named = splitNamed(src);
  const node = parse(named ? named.body : src);
  if (named && node.type === 'eq') throw new Error('Only one "=" sign is allowed');
  return { node, named };
}

function defaultDependent(letter, v, node) {
  if (node.type !== 'eq') return false;
  if (CONSTANT_LETTERS.has(letter)) return false;
  if (v === 'x') return letter === 'y';
  if (v === 'y') return letter === 'x';
  return true;
}

function depsFor(node, v) {
  if (state.overridesFor !== v) { state.overrides.clear(); state.overridesFor = v; }
  const letters = [...freeSyms(node)].filter(l => l !== v).sort();
  const deps = new Set();
  for (const l of letters) {
    const o = state.overrides.get(l);
    if (o === undefined ? defaultDependent(l, v, node) : o) deps.add(l);
  }
  return { letters, deps };
}

function renderChips(letters, deps, v) {
  const box = $('chips');
  if (!letters.length) { box.hidden = true; box.innerHTML = ''; return; }
  box.hidden = false;
  box.innerHTML = `<span class="lead">Other letters — tap to switch. <b>Blue</b> = changes with ${esc(v)} (a function of ${esc(v)}); white = constant.</span>` +
    letters.map(l => `<button class="chip ${deps.has(l) ? 'dep' : ''}" data-letter="${esc(l)}" aria-pressed="${deps.has(l)}">${M(symTex(l))}<small>${deps.has(l) ? `function of ${esc(v)}` : 'constant'}</small></button>`).join('');
}

function renderParams(constLetters) {
  const box = $('params');
  if (!constLetters.length) { box.hidden = true; box.innerHTML = ''; return; }
  box.hidden = false;
  box.innerHTML = `<span class="lead">The derivative keeps the constants as letters. To run the First Derivative Test and draw the graph, pick values for them:</span>` +
    constLetters.map(l => `<label>${M(symTex(l))} = <input type="text" data-param="${esc(l)}" value="${esc(state.params.get(l) ?? '1')}"></label>`).join('');
}

function readNumber(str, what) {
  const n = simplify(parse(str));
  if (freeSyms(n).size) throw new Error(`${what} must be a number`);
  const v = compile(n)({});
  if (!isFinite(v)) throw new Error(`${what} must be a number`);
  return { node: n, value: v };
}

function paramValues(constLetters) {
  const map = {};
  for (const l of constLetters) {
    const str = state.params.get(l) ?? '1';
    map[l] = readNumber(str || '0', `The value of ${l}`).node;
  }
  return map;
}

function updatePreview() {
  const pv = $('preview');
  try {
    const { node, named } = readInput();
    let v;
    try { v = readWrt(); } catch { v = 'x'; }
    setMainVar(v);
    const shown = simplifyForPreview(node);
    let tex;
    if (named) tex = `${named.name}(${symTex(named.arg)}) = ${toTex(shown)}`;
    else if (node.type === 'eq') tex = `${toTex(shown)}`;
    else tex = `\\frac{d}{d${symTex(v)}}\\left[${toTex(shown)}\\right]`;
    pv.className = 'preview';
    pv.innerHTML = M(tex, true);
    const { letters, deps } = depsFor(node, v);
    renderChips(letters, deps, v);
    const consts = letters.filter(l => !deps.has(l));
    renderParams(consts);
  } catch (e) {
    const src = $('expr').value.trim();
    pv.className = src ? 'preview bad' : 'preview';
    pv.innerHTML = src ? esc(e.message) : '<span class="hint-text">Your expression will appear here as you type.</span>';
  }
}

function simplifyForPreview(node) {
  // show what was typed, lightly cleaned up (no reordering surprises beyond simplify)
  try { return simplify(node); } catch { return node; }
}

// y = f(x): returns { name, body } when the equation just defines one letter by a formula in v.
function explicitSide(node, v, deps) {
  for (const [a, b] of [[node.lhs, node.rhs], [node.rhs, node.lhs]]) {
    if (a.type !== 'sym' || a.name === v || ['pi', 'e'].includes(a.name)) continue;
    const others = [...freeSyms(b)];
    if (others.includes(a.name)) continue;
    if (others.some(l => deps.has(l))) continue;
    return { name: a.name, body: b };
  }
  return null;
}

// ---------- main computation ----------

function compute() {
  $('error').hidden = true;
  try {
    const v = readWrt();
    setMainVar(v);
    const { node, named } = readInput();
    const { letters, deps } = depsFor(node, v);
    const simplified = simplify(node);

    if (simplified.type !== 'eq') {
      runExplicit(simplified, v, deps, letters, named ? { name: named.name, kind: 'f' } : { kind: 'expr' });
      return;
    }
    const ex = explicitSide(simplified, v, deps);
    if (ex) { runExplicit(ex.body, v, deps, letters.filter(l => l !== ex.name), { name: ex.name, kind: 'y' }); return; }
    runImplicit(simplified, v, deps, letters);
  } catch (e) {
    console.error(e);
    showError(e.message || String(e));
  }
}

function showError(msg) {
  const box = $('error');
  box.textContent = msg;
  box.hidden = false;
  ['deriv-card', 'analysis-card', 'concavity-card', 'graph-card'].forEach(id => { $(id).hidden = true; });
}

function derivLabel(how, v) {
  const vt = symTex(v);
  if (how.kind === 'f') return `${how.name}'(${vt})`;
  if (how.kind === 'y') return dTex(how.name, v);
  return null;
}

function runExplicit(f, v, deps, letters, how) {
  const d = differentiate(f, v, deps);
  const vt = symTex(v);
  const label = derivLabel(how, v);
  const lhs = label ? label : `\\frac{d}{d${vt}}\\left[${toTex(f)}\\right]`;
  $('deriv-result').innerHTML = M(`${lhs} = ${toTex(d.result)}`, true);
  $('steps').innerHTML = stepTree(d.steps, v, 0);
  showCard('deriv-card');

  const fName = how.kind === 'f' ? how.name : how.kind === 'y' ? how.name : 'f';
  state.current = { kind: 'explicit', f, fp: d.result, v, deps, fName, how };
  $('second').hidden = false;
  $('second').textContent = 'Second derivative';
  $('second-out').innerHTML = '';

  // rates such as dx/dt in the answer: no First Derivative Test
  const constLetters = letters.filter(l => !deps.has(l));
  if (contains(d.result, n => n.type === 'sym' && !!n.deriv) || [...deps].some(l => freeSyms(f).has(l))) {
    $('second').hidden = true;
    $('analysis-card').hidden = true;
    $('concavity-card').hidden = true;
    $('graph-card').hidden = true;
    return;
  }

  const values = paramValues(constLetters);
  const fN = simplify(substitute(f, values));
  const fpN = pretty(substitute(d.result, values));
  const interval = readInterval();
  const a = analyze(fN, fpN, v, { interval });
  renderAnalysis(a, fN, fpN, v, fName, constLetters, values);

  // Second Derivative Test (concavity). If it fails, the First Derivative Test still shows.
  let fppN = null, conc = null;
  try {
    const d2 = differentiate(d.result, v, deps);
    fppN = pretty(substitute(d2.result, values));
    conc = analyze(fN, fppN, v, { interval, prime: '″', pointWord: 'possible inflection points' });
    renderConcavity(conc, a, fN, fppN, v, fName, constLetters, values);
  } catch (e) {
    console.error(e);
    $('concavity-card').hidden = true;
  }

  // graph
  const fc = compile(fN), fpc = compile(fpN), fppc = fppN ? compile(fppN) : null;
  showCard('graph-card');
  $('deriv-toggle').hidden = false;
  $('deriv-name').textContent = `${fName}′`;
  $('color-by-wrap').hidden = !fppN;
  setLegend(fName);
  graph.setExplicit({
    f: x => fc({ [v]: x }), fp: x => fpc({ [v]: x }), fpp: fppc ? x => fppc({ [v]: x }) : null,
    points: a.points, inflections: conc ? conc.points.filter(p => p.type !== 'neither') : [],
    window: a.window, xName: v, fName,
  });
}

function setLegend(fName) {
  const n = esc(fName);
  $('legend').innerHTML = (graph.colorBy === 'concavity'
    ? `<span><i style="background:var(--up)"></i>${n} concave up (${n}″ &gt; 0)</span>` +
      `<span><i style="background:var(--down)"></i>${n} concave down (${n}″ &lt; 0)</span>`
    : `<span><i style="background:var(--inc)"></i>${n} increasing (${n}′ &gt; 0)</span>` +
      `<span><i style="background:var(--dec)"></i>${n} decreasing (${n}′ &lt; 0)</span>`) +
    `<span><i style="background:var(--deriv)"></i>${n}′ (dashed, optional)</span>` +
    `<span><i class="ring"></i>inflection point</span>` +
    `<span><i style="background:#f59e0b"></i>tangent line</span>`;
}

function readInterval() {
  const A = $('ia').value.trim(), B = $('ib').value.trim();
  if (!A && !B) return null;
  if (!A || !B) throw new Error('Fill in both ends of the interval, or clear them both.');
  const a = readNumber(A, 'The start of the interval').value, b = readNumber(B, 'The end of the interval').value;
  if (!(a < b)) throw new Error('The interval start must be less than its end.');
  return [a, b];
}

function showCard(id) { $(id).hidden = false; }

// ---------- steps ----------

function stepTree(step, v, depth) {
  const head = `<span class="rule">${esc(step.rule)}</span><span class="step-math">${M(`\\frac{d}{d${symTex(v)}}\\left[${toTex(step.expr)}\\right] = ${toTex(step.result)}`)}</span>`;
  const formula = step.formula ? `<div class="formula">Rule: ${M(step.formula)}</div>` : '';
  const kids = step.children.filter(c => !(depth > 0 && c.rule === 'Variable rule'));
  if (!kids.length) return `<div class="step"><div class="leaf">${head}${formula}</div></div>`;
  return `<div class="step"><details ${depth < 2 ? 'open' : ''}><summary>${head}</summary><div class="step-body">${formula}${kids.map(k => stepTree(k, v, depth + 1)).join('')}</div></details></div>`;
}

// ---------- First Derivative Test ----------

// Stages 1-4 are the same test for f' and f'': only the words change.
function testStages(a, o) {
  const { vt, F, d } = o;
  const D = `${d}(${vt})`;
  const list = pts => pts.map(p => M(`${vt} = ${p.tex}`)).join(', ');
  const where = a.truncated ? ' in the window analyzed' : '';
  const Pts = o.points[0].toUpperCase() + o.points.slice(1);

  let cand = `<p>${Pts} are the ${M(vt)}-values <b>in the domain of ${esc(F)}</b> where ${M(`${D} = 0`)} or ${M(D)} is undefined.</p>`;
  if (a.factoredTex) cand += `<div class="math-line">${M(`${D} = ${a.factoredTex}`, true)}</div>`;
  if (a.general.length) {
    cand += `<p>A trig factor makes ${M(`${D} = 0`)} at infinitely many places. The whole family of solutions:</p>` +
      a.general.map(t => `<div class="math-line">${M(t, true)}</div>`).join('');
  }
  cand += `<p>${M(`${D} = 0`)}${where} when: ${a.zeros.length ? list(a.zeros) : '<i>never (no solutions)</i>'}</p>`;
  cand += `<p>${M(D)} is undefined (but ${esc(F)} is defined) at: ${a.undef.length ? list(a.undef) : '<i>no such points</i>'}</p>`;
  if (a.excluded.length) cand += `<p class="note">${M(D)} is also undefined at ${list(a.excluded)}, but ${esc(F)} itself is not defined there, so ${a.excluded.length > 1 ? 'they are not' : 'it is not'} ${o.one}. It still splits the number line into separate intervals.</p>`;
  cand += a.points.length
    ? `<p><b>${Pts}${where}:</b> ${list(a.points)}</p>`
    : `<p><b>There are no ${o.points}</b>, so ${esc(F)} never switches between ${o.up.word} and ${o.down.word}${a.intervals.length > 1 ? ' except across the breaks in its domain' : ''}.</p>`;

  const { numline, table } = signChart(a, vt, d, F, o.words);
  const cup = arr => (arr.length ? M(arr.join(' \\cup ')) : '<i>nowhere</i>');
  const lines = a.points.map(p => (p.type === 'neither'
    ? `<li><span class="tag neither">neither</span>At ${M(`${vt} = ${p.tex}`)}, ${M(d)} does not change sign, so there is ${o.none} there.</li>`
    : `<li><span class="tag ${o.tag(p)}">${o.tagText(p)}</span>${M(`${vt} = ${p.tex}`)}: ${M(d)} changes ${p.type === 'max' ? 'from + to −' : 'from − to +'}, so there is ${o.result(p)}.</li>`)).join('');

  return stageHTML(1, o.stage1,
      `<div class="math-line">${M(`${D} = ${toTex(o.deriv)}`, true)}</div>
      <p>Domain of ${esc(F)}: ${M(a.domainTex)}${a.domainWithinWindow ? ' <i>(within the window analyzed)</i>' : ''}</p>`, true) +
    stageHTML(2, `Find the ${o.points}`, cand) +
    stageHTML(3, `Make a sign chart for ${M(d)}`,
      `<p>The ${o.points} and domain breaks split the number line into intervals. Pick a test value in each interval and check the sign of ${M(d)}.</p>
      <p>${M(`${d} > 0`)} means ${esc(F)} is <b>${o.up.word}</b> ${o.up.sym}; ${M(`${d} < 0`)} means ${esc(F)} is <b>${o.down.word}</b> ${o.down.sym}.</p>
      ${numline}${table}`) +
    stageHTML(4, 'Conclusions',
      `<ul class="conclusions">
        <li><span class="tag ${o.up.tag}">${o.up.word}</span>${esc(F)} is ${o.up.word} on ${cup(a.increasing)}</li>
        <li><span class="tag ${o.down.tag}">${o.down.word}</span>${esc(F)} is ${o.down.word} on ${cup(a.decreasing)}</li>
        ${lines}${o.extra || ''}
      </ul>`);
}

const usingValuesHTML = (f, vt, F, constLetters, values) => (constLetters.length
  ? `<p class="note">Using ${constLetters.map(l => M(`${symTex(l)} = ${toTex(values[l])}`)).join(', ')}: ${M(`${F}(${vt}) = ${toTex(f)}`)}</p>` : '');
const yPartOf = F => p => (p.yTex.startsWith('\\approx') ? `${F}(${p.tex}) ${p.yTex}` : `${F}(${p.tex}) = ${p.yTex}`);

function renderAnalysis(a, f, fp, v, fName, constLetters, values) {
  const vt = symTex(v), F = fName, yPart = yPartOf(F);
  const ends = a.endpoints.map(p => `<li><span class="tag ${p.type}">endpoint ${p.type}</span>At the endpoint ${M(`${vt} = ${p.tex}`)}, ${M(yPart(p))}.</li>`).join('');
  $('analysis-card').innerHTML = cardHead('First Derivative Test: Increasing &amp; Decreasing') +
    usingValuesHTML(f, vt, F, constLetters, values) + a.notes.map(n => `<p class="note">${esc(n)}</p>`).join('') +
    testStages(a, {
      vt, F, d: `${fName}'`, deriv: fp, words: INC_WORDS,
      stage1: 'Find the derivative and the domain',
      points: 'critical numbers', one: 'a critical number',
      up: { word: 'increasing', sym: '↗', tag: 'inc' }, down: { word: 'decreasing', sym: '↘', tag: 'dec' },
      none: 'no local max or min',
      tag: p => p.type, tagText: p => `local ${p.type}`,
      result: p => `a local ${p.type === 'max' ? 'maximum' : 'minimum'} value of ${M(yPart(p))}`,
      extra: ends,
    });
  $('analysis-card').hidden = false;
}

const INC_WORDS = { posCls: 'pos', negCls: 'neg', pos: '↗ inc', neg: '↘ dec', zero: 'flat', posLong: 'increasing ↗', negLong: 'decreasing ↘', zeroLong: 'constant', row: 'is' };
const CONC_WORDS = { posCls: 'cup', negCls: 'cap', pos: '∪ up', neg: '∩ down', zero: 'flat', posLong: 'concave up ∪', negLong: 'concave down ∩', zeroLong: 'linear', row: 'is' };

// Number line and test-value table for the sign of a derivative (d is its TeX name, like f' or f'').
function signChart(a, vt, d, F, w) {
  const segs = a.intervals.map(iv => {
    const cls = iv.sign > 0 ? w.posCls : iv.sign < 0 ? w.negCls : 'zero';
    const sg = iv.sign > 0 ? '+' : iv.sign < 0 ? '−' : '0';
    return `<div class="seg ${cls}"><span class="sgn">${sg}</span><span>${iv.sign > 0 ? w.pos : iv.sign < 0 ? w.neg : w.zero}</span><span class="tv">test ${M(`${vt}=${iv.test.tex}`)}</span></div>`;
  });
  const pts = [];
  a.intervals.forEach((iv, i) => {
    if (i === 0) pts.push(ptHTML(iv.l, true));
    pts.push(segs[i]);
    const next = a.intervals[i + 1];
    const joined = next && Math.abs(next.l.x - iv.r.x) < 1e-12;
    pts.push(ptHTML(iv.r, !next, joined ? isCrit(iv.r, a) : false));
    if (next && !joined) pts.push(ptHTML(next.l, true));
  });
  const cls = iv => (iv.sign > 0 ? w.posCls : iv.sign < 0 ? w.negCls : '');
  const numline = `<div class="numline-wrap"><div class="numline">${pts.join('')}</div></div>`;
  const table = `<div class="table-wrap"><table class="signs">
    <tr><th>Interval</th>${a.intervals.map(iv => `<td>${M(intervalTex(iv))}</td>`).join('')}</tr>
    <tr><th>Test value</th>${a.intervals.map(iv => `<td>${M(`${vt} = ${iv.test.tex}`)}</td>`).join('')}</tr>
    <tr><th>${M(`${d}(\\text{test})`)}</th>${a.intervals.map(iv => `<td>${M(`${d}(${iv.test.tex}) ${iv.valueTex.startsWith('\\approx') ? '' : '='} ${iv.valueTex}`)}</td>`).join('')}</tr>
    <tr><th>Sign of ${M(d)}</th>${a.intervals.map(iv => `<td class="${cls(iv)}">${iv.sign > 0 ? '+' : iv.sign < 0 ? '−' : '0'}</td>`).join('')}</tr>
    <tr><th>${esc(F)} ${w.row}</th>${a.intervals.map(iv => `<td class="${cls(iv)}">${iv.sign > 0 ? w.posLong : iv.sign < 0 ? w.negLong : w.zeroLong}</td>`).join('')}</tr>
  </table></div>`;
  return { numline, table };
}

const stageHTML = (n, title, body, open = false) =>
  `<details class="stage"${open ? ' open' : ''}><summary><span class="num">${n}</span>${title}</summary><div class="stage-body">${body}</div></details>`;
const cardHead = title => `<div class="card-head"><h2>${title}</h2><button class="ghost expand-stages">Expand all</button></div>`;

function isCrit(pt, a) { return a.points.some(p => Math.abs(p.x - pt.x) < 1e-12); }

function ptHTML(pt, isEnd, crit = false) {
  const cls = !isFinite(pt.x) ? 'pt end' : crit || pt.closed ? 'pt' : 'pt open';
  return `<div class="${cls}"><div class="tick"></div><div class="plab">${M(pt.tex)}</div></div>`;
}

function intervalTex(iv) {
  return `${iv.l.closed ? '[' : '('}${iv.l.tex}, ${iv.r.tex}${iv.r.closed ? ']' : ')'}`;
}

// ---------- Second Derivative Test: concavity and inflection points ----------

function renderConcavity(c, fdt, f, fpp, v, fName, constLetters, values) {
  const card = $('concavity-card');
  const vt = symTex(v), F = fName, d = `${fName}''`;
  const point = p => `\\left(${p.tex},\\ ${p.yTex.replace(/^\\approx\s*/, '')}\\right)`;
  // Second Derivative Test for the critical numbers found by the First Derivative Test
  const fppC = compile(fpp);
  const sdt = fdt.points.map(p => {
    const at = M(`${vt} = ${p.tex}`);
    if (p.kind === 'undef') return `<li><span class="tag neither">does not apply</span>${at}: ${M(`${fName}'`)} is undefined there, so the Second Derivative Test can't be used. Use the First Derivative Test.</li>`;
    let val = fppC({ [v]: p.x }), tex = fmt(val), exact = false;
    if (p.node) {
      try {
        const e = simplify(substitute(fpp, { [v]: p.node }));
        if (e.type === 'num') { tex = toTex(e); val = e.n / e.d; exact = true; }
      } catch { /* keep the decimal */ }
    }
    if (!exact && Math.abs(val) < 1e-9) { val = 0; tex = '0'; }
    const value = M(`${d}(${p.tex}) ${exact || tex === '0' ? '=' : '\\approx'} ${tex}`);
    if (!isFinite(val)) return `<li><span class="tag neither">does not apply</span>${at}: ${value} is undefined. Use the First Derivative Test.</li>`;
    if (val > 0) return `<li><span class="tag min">local min</span>${at}: ${value} &gt; 0, so ${esc(F)} is concave up there and has a <b>local minimum</b>.</li>`;
    if (val < 0) return `<li><span class="tag max">local max</span>${at}: ${value} &lt; 0, so ${esc(F)} is concave down there and has a <b>local maximum</b>.</li>`;
    return `<li><span class="tag neither">inconclusive</span>${at}: ${value}, so the Second Derivative Test gives no answer. The First Derivative Test says: ${p.type === 'neither' ? 'neither' : `local ${p.type}`}.</li>`;
  }).join('');

  card.innerHTML = cardHead('Second Derivative Test: Concavity') +
    usingValuesHTML(f, vt, F, constLetters, values) + c.notes.map(n => `<p class="note">${esc(n)}</p>`).join('') +
    testStages(c, {
      vt, F, d, deriv: fpp, words: CONC_WORDS,
      stage1: 'Find the second derivative and the domain',
      points: 'possible inflection points', one: 'a possible inflection point',
      up: { word: 'concave up', sym: '∪', tag: 'up' }, down: { word: 'concave down', sym: '∩', tag: 'down' },
      none: 'no inflection point',
      tag: () => 'infl', tagText: () => 'inflection point',
      result: p => `an inflection point at ${M(point(p))}${p.yTex.startsWith('\\approx') ? ' (approximately)' : ''}`,
    }) +
    stageHTML(5, 'Second Derivative Test for local extrema',
      fdt.points.length
        ? `<p>At each critical number ${M('c')} where ${M(`${fName}'(c) = 0`)}: if ${M(`${d}(c) > 0`)} there is a local min; if ${M(`${d}(c) < 0`)} a local max; if ${M(`${d}(c) = 0`)} the test is inconclusive.</p><ul class="conclusions">${sdt}</ul>`
        : '<p>There are no critical numbers, so there is nothing to test.</p>');
  card.hidden = false;
}

// ---------- second derivative ----------

function secondDerivative() {
  const c = state.current;
  if (!c || c.kind !== 'explicit') return;
  const out = $('second-out');
  if (out.innerHTML) { out.innerHTML = ''; $('second').textContent = 'Second derivative'; return; }
  setMainVar(c.v);
  const d2 = differentiate(c.fp, c.v, c.deps);
  const vt = symTex(c.v);
  const lhs = c.how.kind === 'y' ? `\\frac{d^2${symTex(c.fName)}}{d${vt}^2}` : c.how.kind === 'f' ? `${c.fName}''(${vt})` : `\\frac{d^2}{d${vt}^2}\\left[${toTex(c.f)}\\right]`;
  out.innerHTML = `<h3>Second derivative</h3><div class="result">${M(`${lhs} = ${toTex(d2.result)}`, true)}</div>
    <details><summary>Steps (differentiate the first derivative)</summary><div class="steps">${stepTree(d2.steps, c.v, 0)}</div></details>`;
  $('second').textContent = 'Hide second derivative';
}

// ---------- implicit differentiation & related rates ----------

function runImplicit(equation, v, deps, letters) {
  if (!deps.size) {
    throw new Error(`Every letter in this equation is set as a constant, so there is nothing that changes with ${v}. Tap a letter above to mark it as a function of ${v}.`);
  }
  const r = differentiateEquation(equation, v, deps);
  const vt = symTex(v);
  state.current = { kind: 'implicit', equation, v, deps, r };
  $('concavity-card').hidden = true;
  $('second').hidden = true;
  $('second-out').innerHTML = '';

  const depList = [...deps].map(l => M(symTex(l))).join(', ');
  $('deriv-result').innerHTML = `<p>Treat ${depList} as ${deps.size > 1 ? 'functions' : 'a function'} of ${M(vt)} and differentiate both sides:</p>` +
    `<div class="result">${M(`\\frac{d}{d${vt}}\\left[${toTex(equation.lhs)}\\right] = \\frac{d}{d${vt}}\\left[${toTex(equation.rhs)}\\right]`, true)}</div>` +
    `<div class="result">${M(toTex(r.result), true)}</div>`;
  $('steps').innerHTML = `<div class="side-title">Left side</div>${stepTree(r.lhsSteps, v, 0)}<div class="side-title">Right side</div>${stepTree(r.rhsSteps, v, 0)}`;
  showCard('deriv-card');

  renderSolvePanel(r, v, letters, deps, equation);
  renderImplicitGraph(equation, v, deps, letters, r);
}

function renderSolvePanel(r, v, letters, deps, equation) {
  const card = $('analysis-card');
  const vt = symTex(v);
  const rates = r.rates;
  if (!rates.length) { card.hidden = true; return; }
  const single = rates.length === 1;
  const chosen = state.solveFor && rates.some(t => t.name === state.solveFor) ? state.solveFor : (single ? rates[0].name : '');
  const opts = rates.map(t => `<option value="${esc(t.name)}" ${t.name === chosen ? 'selected' : ''}>${esc(t.name)}</option>`).join('');
  let html = single && v !== 't'
    ? `<h2>Solve for ${M(toTex(rates[0]))}</h2>`
    : `<h2>Related rates</h2><p>The equation above relates the rates. Choose the rate you want, then plug in what you know.</p>
       <label class="check">Solve for <select id="solve-for"><option value="">— choose —</option>${opts}</select></label>`;

  if (chosen) {
    const target = rates.find(t => t.name === chosen);
    const s = solveLinear(r.result, target);
    if (!s) html += `<p class="note">Could not isolate ${M(toTex(target))}.</p>`;
    else {
      const tT = toTex(target);
      html += `<div class="stage"><p>Collect the ${M(tT)} terms on one side and everything else on the other:</p>
        <div class="math-line">${M(`${wrapTex(s.A)}\\,${tT} = ${toTex(s.B)}`, true)}</div>
        <p>Divide both sides by ${M(wrapTex(s.A))}:</p>
        <div class="result">${M(`${tT} = ${toTex(s.solution)}`, true)}</div></div>`;
      state.current.solution = { target, expr: s.solution };
      if (single && v !== 't') html += tangentNotes(s.solution, v, [...deps][0]);
      const unknowns = [...freeSyms(s.solution)].sort((p, q) => (p.includes('/') - q.includes('/')) || (p < q ? -1 : 1));
      if (unknowns.length) {
        html += `<h3>${single && v !== 't' ? 'Slope at a point' : 'Plug in known values'}</h3>
          <div class="eval-grid">${unknowns.map(u => `<label>${M(u.includes('/') ? toTex(symFromName(u)) : symTex(u))} = <input type="text" data-eval="${esc(u)}" value="${esc((state.evalVals || {})[u] || '')}"></label>`).join('')}</div>
          <div class="eval-out" id="eval-out"></div>`;
      }
    }
  }
  card.innerHTML = html;
  card.hidden = false;
  updateEval();
}

const symFromName = name => { const m = /^d(.+)\/d(.+)$/.exec(name); return m ? deriv(m[1], m[2]) : sym(name); };
const wrapTex = n => (n.type === 'add' ? `\\left(${toTex(n)}\\right)` : toTex(n));

function tangentNotes(solution, v, dep) {
  const vt = symTex(v), dt = symTex(dep);
  let N = solution, D = num(1);
  if (solution.type === 'mul') {
    const top = [], bot = [];
    for (const f of solution.factors) {
      if (f.type === 'pow' && f.exp.type === 'num' && f.exp.n < 0) bot.push(simplify({ type: 'pow', base: f.base, exp: num(-f.exp.n, f.exp.d) }));
      else top.push(f);
    }
    N = simplify({ type: 'mul', factors: top.length ? top : [num(1)] });
    D = bot.length ? simplify({ type: 'mul', factors: bot }) : num(1);
  } else if (solution.type === 'pow' && solution.exp.type === 'num' && solution.exp.n < 0) {
    N = num(1); D = simplify({ type: 'pow', base: solution.base, exp: num(-solution.exp.n, solution.exp.d) });
  }
  return `<p class="note">The First Derivative Test is for functions ${M(`${dt} = f(${vt})`)}. This relation is not written as a function, so instead we read the tangent lines from ${M(dTex(dep, v))}:</p>
    <ul class="conclusions">
      <li><span class="tag inc">horizontal tangent</span>where the numerator is zero: ${M(`${toTex(N)} = 0`)} (and the point is on the curve)</li>
      <li><span class="tag dec">vertical tangent</span>where the denominator is zero: ${D.type === 'num' ? '<i>never</i>' : M(`${toTex(D)} = 0`)}</li>
    </ul>`;
}

function updateEval() {
  const out = $('eval-out');
  const sol = state.current && state.current.solution;
  if (!out || !sol) return;
  const inputs = [...document.querySelectorAll('[data-eval]')];
  state.evalVals = state.evalVals || {};
  const map = {};
  let missing = false;
  try {
    for (const inp of inputs) {
      const name = inp.dataset.eval, val = inp.value.trim();
      state.evalVals[name] = val;
      if (!val) { missing = true; continue; }
      map[name] = readNumber(val, `The value of ${name}`).node;
    }
    if (missing) { out.innerHTML = '<span class="hint">Fill in every value to get a number.</span>'; return; }
    const exact = simplify(substitute(sol.expr, map));
    const value = compile(exact)({});
    const tT = toTex(sol.target);
    if (!isFinite(value)) { out.innerHTML = `${M(`${tT}`)} is undefined at these values (division by zero → vertical tangent or no rate).`; return; }
    const exactTex = toTex(exact);
    const dec = fmt(value);
    out.innerHTML = M(exact.type === 'num' && exact.d === 1 ? `${tT} = ${exactTex}` : `${tT} = ${exactTex} \\approx ${dec}`, true);
  } catch (e) { out.innerHTML = `<span class="hint">${esc(e.message)}</span>`; }
}

function renderImplicitGraph(equation, v, deps, letters, r) {
  const consts = letters.filter(l => !deps.has(l));
  const vars = [...freeSyms(equation)].filter(l => !consts.includes(l));
  const card = $('graph-card');
  if (vars.length !== 2) { card.hidden = true; return; }
  let values;
  try { values = paramValues(consts); } catch { card.hidden = true; return; }
  const [hx, vy] = vars.includes(v) ? [v, vars.find(l => l !== v)] : vars.sort();
  const Fexpr = simplify(substitute(sub(equation.lhs, equation.rhs), values));
  const Fc = compile(Fexpr);
  let slope = null;
  const sol = state.current.solution;
  if (r.rates.length === 1 && v === hx && sol) {
    const sc = compile(simplify(substitute(sol.expr, values)));
    slope = (x, y) => sc({ [hx]: x, [vy]: y });
  }
  card.hidden = false;
  $('deriv-toggle').hidden = true;
  $('legend').innerHTML = `<span><i style="background:#2563eb"></i>the curve ${M(toTex(simplify(substitute(equation, values))))}</span>` +
    `<span><i style="background:var(--inc)"></i>horizontal tangent</span><span><i style="background:var(--dec)"></i>vertical tangent</span>` +
    `<span><i style="background:#f59e0b"></i>tangent line</span>`;
  graph.setImplicit({ F: (x, y) => Fc({ [hx]: x, [vy]: y }), slope, xName: hx, yName: vy });
}

// ---------- events ----------

function insertAtCursor(text, close = '') {
  const el = $('expr');
  const s = el.selectionStart ?? el.value.length, e = el.selectionEnd ?? el.value.length;
  const sel = el.value.slice(s, e);
  el.value = el.value.slice(0, s) + text + sel + close + el.value.slice(e);
  const pos = s + text.length + sel.length + (sel ? close.length : 0);
  el.focus();
  el.setSelectionRange(pos, pos);
  updatePreview();
}

function init() {
  graph = new Graph($('graph'), $('readout'));

  $('examples').innerHTML = '<option value="">Choose an example…</option>' +
    EXAMPLES.map(([e, v, d], i) => `<option value="${i}">${esc(d)}:  ${esc(e)}${v !== 'x' ? `  (d/d${v})` : ''}</option>`).join('');
  $('examples').addEventListener('change', ev => {
    const ex = EXAMPLES[ev.target.value];
    if (!ex) return;
    $('expr').value = ex[0];
    $('wrt').value = ex[1];
    state.solveFor = '';
    state.evalVals = {};
    $('ia').value = ''; $('ib').value = '';
    updatePreview();
    compute();
  });

  $('expr').addEventListener('input', () => {
    const named = splitNamed($('expr').value);
    if (named && named.arg !== $('wrt').value.trim()) $('wrt').value = named.arg;
    updatePreview();
  });
  $('expr').addEventListener('keydown', e => { if (e.key === 'Enter') compute(); });
  $('wrt').addEventListener('input', updatePreview);
  $('wrt').addEventListener('keydown', e => { if (e.key === 'Enter') compute(); });
  $('go').addEventListener('click', compute);

  $('keypad').addEventListener('click', e => {
    const b = e.target.closest('button');
    if (b) insertAtCursor(b.dataset.insert, b.dataset.close || '');
  });

  $('chips').addEventListener('click', e => {
    const b = e.target.closest('[data-letter]');
    if (!b) return;
    const l = b.dataset.letter;
    state.overrides.set(l, b.getAttribute('aria-pressed') !== 'true');
    updatePreview();
    if (state.current) compute();
  });

  $('params').addEventListener('change', e => {
    const inp = e.target.closest('[data-param]');
    if (!inp) return;
    state.params.set(inp.dataset.param, inp.value.trim());
    compute();
  });

  for (const id of ['ia', 'ib']) {
    $(id).addEventListener('keydown', e => { if (e.key === 'Enter') compute(); });
    $(id).addEventListener('change', () => { if (state.current) compute(); });
  }
  $('clear-interval').addEventListener('click', () => { $('ia').value = ''; $('ib').value = ''; compute(); });

  $('toggle-steps').addEventListener('click', () => {
    const s = $('steps');
    s.hidden = !s.hidden;
    $('toggle-steps').textContent = s.hidden ? 'Show steps' : 'Hide steps';
  });
  $('second').addEventListener('click', secondDerivative);

  $('analysis-card').addEventListener('change', e => {
    if (e.target.id === 'solve-for') {
      state.solveFor = e.target.value;
      const c = state.current;
      renderSolvePanel(c.r, c.v, [...freeSyms(c.equation)].filter(l => l !== c.v), c.deps, c.equation);
    }
  });
  $('analysis-card').addEventListener('input', e => { if (e.target.dataset.eval) updateEval(); });
  document.addEventListener('click', e => {
    if (!e.target.classList.contains('expand-stages')) return;
    const stages = [...e.target.closest('.card').querySelectorAll('details.stage')];
    const open = !stages.every(d => d.open);
    stages.forEach(d => { d.open = open; });
    e.target.textContent = open ? 'Collapse all' : 'Expand all';
  });
  document.addEventListener('toggle', e => {
    if (!e.target.matches || !e.target.matches('details.stage')) return;
    const card = e.target.closest('.card'), btn = card && card.querySelector('.expand-stages');
    if (btn) btn.textContent = [...card.querySelectorAll('details.stage')].every(d => d.open) ? 'Collapse all' : 'Expand all';
  }, true);
  $('color-by').addEventListener('change', e => {
    graph.colorBy = e.target.value;
    if (state.current && state.current.fName) setLegend(state.current.fName);
    graph.draw();
  });

  $('zoom-in').addEventListener('click', () => graph.zoom(1 / 1.4));
  $('zoom-out').addEventListener('click', () => graph.zoom(1.4));
  $('zoom-reset').addEventListener('click', () => graph.reset());
  $('show-deriv').addEventListener('change', e => { graph.showDeriv = e.target.checked; graph.draw(); });
  $('show-tangent').addEventListener('change', e => { graph.showTangent = e.target.checked; graph.draw(); });

  $('expr').value = 'x^3 - 3x';
  updatePreview();
  compute();
}

init();
