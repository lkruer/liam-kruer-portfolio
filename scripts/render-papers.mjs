import {readFile,writeFile} from 'node:fs/promises';
import {research} from '../dist/research-catalog.js';
import {paperNotes} from '../dist/paper-notes.js';

const escape=value=>String(value).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const cards=research.map((paper,index)=>{
  const note=paperNotes[paper.id];
  if(!note)throw new Error('Missing reading note: '+paper.id);
  const number=String(index+1).padStart(2,'0'),group=paper.id.startsWith('green')?'green':'erdos';
  return `          <article class="paper-card" data-paper="${paper.id}" data-group="${group}" aria-labelledby="card-${paper.id}">
            <div class="paper-card-index"><span>PAPER / ${number}</span><span>${escape(note.topic)}</span></div>
            <button type="button" class="paper-cover" data-research="${paper.id}" aria-label="Preview ${escape(paper.title)}">
              <span class="cover-cross" aria-hidden="true">+</span><span class="cover-reference" aria-hidden="true">${escape(paper.problem)}</span>
              <span class="paper-sheet"><img src="${paper.pages[0]}" alt="First page of ${escape(paper.title)}" width="${paper.id==='unit-distances'?990:1082}" height="1400" loading="lazy" decoding="async"></span>
              <span class="cover-open" aria-hidden="true">OPEN MANUSCRIPT ↗</span>
            </button>
            <div class="paper-card-content"><p class="paper-card-meta"><span>${escape(paper.problem)}</span><span>${paper.pageCount} pages · ${escape(paper.status)}</span></p>
              <h3 id="card-${paper.id}">${escape(paper.title)}</h3><p class="paper-card-summary">${escape(note.summary)}</p>
              <p class="paper-card-credit">${escape(note.credit||'With Jensen Kohlmeyer')}</p>
            </div>
            <div class="paper-card-actions"><button type="button" data-research="${paper.id}" aria-label="Read ${escape(paper.title)} preview">Read preview <span aria-hidden="true">↗</span></button><a href="${paper.pdf}" download aria-label="Download ${escape(paper.title)} PDF">Download PDF <span aria-hidden="true">↓</span></a><a href="${paper.bundle}" download aria-label="Download ${escape(paper.title)} source bundle">Source files <span aria-hidden="true">↓</span></a></div>
          </article>`;
}).join('\n');
const file=new URL('../dist/index.html',import.meta.url);
let html=await readFile(file,'utf8');
if(!html.includes('<!-- PAPER CARDS START -->'))throw new Error('Paper card markers missing');
html=html.replace(/<!-- PAPER CARDS START -->[\s\S]*?<!-- PAPER CARDS END -->/,'<!-- PAPER CARDS START -->\n'+cards+'\n          <!-- PAPER CARDS END -->');
await writeFile(file,html);
console.log(`Rendered ${research.length} manuscript cards from the research catalog.`);
