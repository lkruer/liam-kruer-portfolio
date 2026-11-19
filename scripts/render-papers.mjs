import {readFile,writeFile} from 'node:fs/promises';
import {research} from '../dist/research-catalog.js';
import {paperNotes} from '../dist/paper-notes.js';
import { hexagonWorks, hexagonSubmissions } from '../dist/hexagon-research.js';

const escape=value=>String(value).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const cards=research.map(paper=>{
  const note=paperNotes[paper.id];
  if(!note)throw new Error('Missing reading note: '+paper.id);
  const group=paper.id.startsWith('green')?'green':'erdos';
  return `          <article class="paper-card" data-paper="${paper.id}" data-group="${group}" aria-labelledby="card-${paper.id}">
            <button type="button" class="paper-cover" data-research="${paper.id}" aria-label="Preview ${escape(paper.title)}">
              <span class="paper-sheet"><img src="${paper.pages[0]}" alt="First page of ${escape(paper.title)}" width="${paper.id==='unit-distances'?990:1082}" height="1400" loading="lazy" decoding="async"></span>
            </button>
            <div class="paper-card-content"><p class="paper-card-meta"><span>${escape(note.topic)}</span><span>${escape(paper.problem)}</span><span>${paper.pageCount} pages · ${escape(paper.status)}</span></p>
              <h3 id="card-${paper.id}">${escape(paper.title)}</h3><p class="paper-card-summary">${escape(note.summary)}</p>
              <p class="paper-card-credit">${escape(note.credit||'With Jensen Kohlmeyer')}</p>
            </div>
            <div class="paper-card-actions"><button type="button" data-research="${paper.id}" aria-label="Read ${escape(paper.title)} preview">Read preview</button><a href="${paper.pdf}" download aria-label="Download ${escape(paper.title)} PDF">Download PDF</a><a href="${paper.bundle}" download aria-label="Download ${escape(paper.title)} source bundle">Source files</a></div>
          </article>`;
}).join('\n');

const featured = hexagonSubmissions.map(paper => {
  const title = escape(paper.title);
  return `          <article class="paper-card" aria-labelledby="card-${paper.id}">
            <button type="button" class="paper-cover" data-research="${paper.id}" aria-label="Preview ${title}">
              <span class="paper-sheet"><img src="${paper.pages[0]}" alt="First page of ${title}" width="966" height="1250" loading="lazy" decoding="async"></span>
            </button>
            <div class="paper-card-content">
              <p class="paper-card-meta"><span>${escape(paper.topic)}</span><span>${paper.pageCount} pages</span></p>
              <h4 class="hexagon-paper-title" id="card-${paper.id}">${title}</h4>
              <p class="paper-card-summary">${escape(paper.summary)}</p>
              <p class="paper-card-credit">${escape(paper.credit)}</p>
            </div>
            <div class="paper-card-actions">
              <button type="button" data-research="${paper.id}" aria-label="Read ${title} preview">Read preview</button>
              <a href="${paper.pdf}" download aria-label="Download ${title} PDF">Download PDF</a>
              <a href="${paper.record}" aria-label="View the Hexagon record for ${title}">Hexagon record</a>
            </div>
          </article>`;
}).join('\n');

const date = new Intl.DateTimeFormat('en-US', { month: 'short', day: 'numeric', year: 'numeric', timeZone: 'UTC' });
const contributions = hexagonWorks.filter(paper => !paper.submittedByLiam).map(paper => {
  const title = escape(paper.title);
  return `            <li>
              <div>
                <h4><a href="${paper.record}">${title}</a></h4>
                <p class="meta">${escape(paper.topic)} · <time datetime="${paper.date}">${date.format(new Date(paper.date))}</time></p>
              </div>
              <a href="${paper.pdf}" download aria-label="Download ${title} PDF">Download PDF</a>
            </li>`;
}).join('\n');

const file=new URL('../dist/index.html',import.meta.url);
let html=await readFile(file,'utf8');
for (const [marker, indentation, content] of [
  ['PAPER CARDS', '          ', cards],
  ['HEXAGON SUBMISSIONS', '          ', featured],
  ['HEXAGON CONTRIBUTIONS', '            ', contributions],
]) {
  const start = `<!-- ${marker} START -->`;
  const end = `<!-- ${marker} END -->`;
  const body = new RegExp(start + '[\\s\\S]*?' + end);
  if (!body.test(html)) throw new Error('Missing render markers for ' + marker);
  html = html.replace(body, () => `${start}\n${content}\n${indentation}${end}`);
}
await writeFile(file,html);
console.log(`Rendered ${research.length} working manuscripts and ${hexagonWorks.length} Hexagon works.`);
