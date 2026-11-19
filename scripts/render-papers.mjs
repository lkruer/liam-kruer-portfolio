import { readFile, writeFile } from 'node:fs/promises';
import { research } from '../dist/research-catalog.js';
import { paperNotes } from '../dist/paper-notes.js';
import { hexagonWorks, hexagonSubmissions } from '../dist/hexagon-research.js';

const entities = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' };
const escape = value => String(value).replace(/[&<>"']/g, character => entities[character]);

const date = new Intl.DateTimeFormat('en-US', { month: 'short', day: 'numeric', year: 'numeric', timeZone: 'UTC' });

function renderRow(paper) {
  const note = paper.record ? paper : paperNotes[paper.id];
  if (!note) throw new Error('Missing reading note for ' + paper.id);

  const title = escape(paper.title);
  const pages = paper.pageCount + (paper.pageCount === 1 ? ' page' : ' pages');
  const meta = paper.record
    ? [note.topic, date.format(new Date(paper.date)), pages]
    : [paper.problem, note.topic, paper.status, pages];
  const searchTerms = [meta.join(' '), note.summary, note.credit, paper.problem, paper.id.replace(/^hexagon-/, '')]
    .filter(Boolean).join(' ');
  const read = paper.pages
    ? `<button type="button" data-research="${paper.id}" aria-label="Read ${title} preview">Read preview</button>`
    : '';
  const related = paper.record
    ? `<a href="${escape(paper.record)}" aria-label="Hexagon record for ${title}">Hexagon record</a>`
    : `<a href="${escape(paper.bundle)}" download aria-label="Download ${title} source bundle">Source files</a>`;

  return `            <li class="paper-row" data-paper-search="${escape(searchTerms)}">
              <div class="paper-row-info">
                <h3>${title}</h3>
                <p class="meta">${escape(meta.join(' · '))}</p>
              </div>
              <div class="paper-row-actions">
                ${[read, `<a href="${escape(paper.pdf)}" download aria-label="Download ${title} PDF">Download PDF</a>`, related].filter(Boolean).join('\n                ')}
              </div>
            </li>`;
}

const groups = [
  ['HEXAGON SUBMISSIONS', hexagonSubmissions],
  ['HEXAGON CONTRIBUTIONS', hexagonWorks.filter(paper => !paper.submittedByLiam)],
  ['WORKING MANUSCRIPTS', research],
];
const file = new URL('../dist/index.html', import.meta.url);
let html = await readFile(file, 'utf8');
for (const [marker, papers] of groups) {
  const start = `<!-- ${marker} START -->`;
  const end = `<!-- ${marker} END -->`;
  const body = new RegExp(start + '[\\s\\S]*?' + end);
  if (!body.test(html)) throw new Error('Missing render markers for ' + marker);
  html = html.replace(body, () => `${start}\n${papers.map(renderRow).join('\n')}\n            ${end}`);
}
await writeFile(file, html);
console.log(`Rendered ${research.length} working manuscripts and ${hexagonWorks.length} Hexagon works.`);
