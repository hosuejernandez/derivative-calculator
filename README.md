# Derivative Calculator

A web page for calculus students. You type a function or relation and choose the variable to differentiate with respect to. The page then shows:

- **The derivative, with steps.** Each step names its rule (power, product, quotient, chain, trig, exponential, log, implicit).
- **CAS-style constants.** Other letters stay as constants, so `ax^2 + bx + c` gives `2ax + b`.
- **Implicit differentiation.** `x^2 + y^2 = 25` gives `dy/dx = -x/y`, plus where the horizontal and vertical tangents are.
- **Related rates.** With respect to `t`, `x^2 + y^2 = 25` gives `2x dx/dt + 2y dy/dt = 0`. You can solve for any rate and plug in values.
- **The First Derivative Test.** It finds the domain and the critical numbers, makes a sign chart with test values, lists the increasing/decreasing intervals, and names each local max/min.
- **A graph.** The function is drawn green where it increases and red where it decreases, with the critical points labeled. There is an optional f′ overlay and a tangent line that follows the pointer.

There is no build step and nothing to install. It is plain HTML, CSS and JavaScript modules. The only outside library is KaTeX (math typesetting), loaded from a CDN.

## Embedding

Once the site is on GitHub Pages:

```html
<iframe src="https://hosuejernandez.github.io/derivative-calculator/" width="100%" height="900" style="border:0"></iframe>
```

## Publishing to GitHub Pages

1. Create a repository named `derivative-calculator` and push these files to `main`.
2. In the repo, go to **Settings → Pages → Build and deployment**, choose **Deploy from a branch**, then pick `main` and `/ (root)`.
3. After a minute the page is live at the address above.

## Running it locally

The JavaScript modules have to be served over HTTP. Opening `index.html` directly from disk does not work.

```bash
python3 -m http.server 8765
```

Then open http://localhost:8765.

## Tests

```bash
node tests/run.mjs
```

The tests check exact answers for derivatives, implicit and related-rates results, and First Derivative Test results. They also compare every derivative against a numeric finite-difference estimate.

## Files

| File | What it does |
| --- | --- |
| `js/expr.js` | Parser (`2x`, `ax^2`, `sin x`, `|x|`, `log_2(x)`, `f(x) = …`), LaTeX output, numeric evaluation |
| `js/simplify.js` | Simplification, expansion, common factors |
| `js/diff.js` | Step-by-step differentiation, implicit differentiation, solving for a rate |
| `js/solve.js` | Exact polynomial roots (rational roots, quadratic formula), numeric roots, recognizing numbers like π/2 or 1/e |
| `js/fdt.js` | First Derivative Test: domain, critical numbers, sign chart, intervals, extrema |
| `js/graph.js` | Canvas graph |
| `js/app.js` | Page wiring |

## Notes on behavior

- **Which letters count as functions of the variable.** For d/dx, `y` changes with `x`. For d/dt, every letter changes with `t` except a, b, c, d, k, m, n, which stay constants. Students can tap a letter's chip to switch it.
- **Constants in the First Derivative Test.** If the function has constants, students enter values for them. The test and graph use those values, while the derivative itself keeps the letters.
- **Trig functions.** These have infinitely many critical points, so the test runs on −2π ≤ x ≤ 2π, or on whatever interval the student enters.
- **Hard equations.** When f′ = 0 can't be solved exactly (for example `e^x + x^2`), the critical numbers are found numerically and marked ≈.
