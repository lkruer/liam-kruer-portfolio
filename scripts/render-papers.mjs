import {readFile,writeFile} from 'node:fs/promises';
import {research} from '../dist/research-catalog.js';
import {paperNotes} from '../dist/paper-notes.js';

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
const file=new URL('../dist/index.html',import.meta.url);
let html=await readFile(file,'utf8');
if(!html.includes('<!-- PAPER CARDS START -->'))throw new Error('Paper card markers missing');
html=html.replace(/<!-- PAPER CARDS START -->[\s\S]*?<!-- PAPER CARDS END -->/,'<!-- PAPER CARDS START -->\n'+cards+'\n          <!-- PAPER CARDS END -->');
await writeFile(file,html);
console.log(`Rendered ${research.length} manuscript cards from the research catalog.`);
