// Stamps every module URL in index.html with a fresh version so browsers never mix old and new
// files after an update.  Run before each commit:  node tools/stamp.mjs
import { readFileSync, writeFileSync, readdirSync } from 'node:fs';

const v = Date.now().toString(36);
const mods = readdirSync('js').filter(f => f.endsWith('.js'));
const map = { imports: Object.fromEntries(mods.map(f => [`./js/${f}`, `./js/${f}?v=${v}`])) };
let html = readFileSync('index.html', 'utf8');
html = html.replace(/\s*<script type="importmap">[\s\S]*?<\/script>/, '');
html = html.replace(/<script type="module" src="[^"]*"><\/script>/,
  `<script type="importmap">${JSON.stringify(map)}</script>\n  <script type="module" src="js/app.js?v=${v}"></script>`);
html = html.replace(/href="css\/style\.css(\?v=[^"]*)?"/, `href="css/style.css?v=${v}"`);
writeFileSync('index.html', html);
console.log(`stamped ${mods.length} modules with v=${v}`);
