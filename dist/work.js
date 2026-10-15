import {research} from './research-catalog.js';
import {games} from './content.js';
import {paperNotes} from './paper-notes.js';

export function initWork(){
  const dialog=document.querySelector('#research-dialog'),select=document.querySelector('#paper-select'),nav=document.querySelector('#paper-nav');
  const image=document.querySelector('#paper-image'),pageInput=document.querySelector('#paper-page'),stage=document.querySelector('#paper-stage');
  let current=research[0],page=1,textRequest=0;
  const textCache=new Map();
  const lock=()=>{document.body.style.overflow=document.querySelector('dialog[open]')?'hidden':'';};
  function showModal(target){document.querySelectorAll('dialog[open]').forEach(d=>d.close());target.showModal();if(target===dialog){document.querySelector('.reader-document').scrollTop=0;stage.scrollTop=0;}lock();}
  function wireDialog(target){target.querySelector('.viewer-close').addEventListener('click',()=>target.close());target.addEventListener('close',lock);target.addEventListener('click',e=>{const r=target.getBoundingClientRect();if(e.clientX<r.left||e.clientX>r.right||e.clientY<r.top||e.clientY>r.bottom)target.close();});}
  wireDialog(dialog);
  for(const paper of research){
    const option=document.createElement('option');option.value=paper.id;option.textContent=paper.problem+' — '+paper.title;select.append(option);
    const button=document.createElement('button');button.type='button';button.dataset.paperId=paper.id;
    const tag=document.createElement('span');tag.textContent=paper.problem+' / '+paper.status;
    const title=document.createElement('strong');title.textContent=paper.title;
    button.append(tag,title);button.addEventListener('click',()=>choosePaper(paper.id));nav.append(button);
  }
  function download(label,href,title){const a=document.createElement('a');a.href=href;a.download='';a.textContent=label;a.title=title||label;return a;}
  const cards=[...document.querySelectorAll('.paper-card')],filters=[...document.querySelectorAll('[data-paper-filter]')],search=document.querySelector('#paper-search');
  let activeFilter='all';
  function filterPapers(){
    const query=search.value.trim().toLocaleLowerCase().normalize('NFD').replace(/[\u0300-\u036f]/g,'');
    let visible=0;
    for(const card of cards){
      const text=card.textContent.toLocaleLowerCase().normalize('NFD').replace(/[\u0300-\u036f]/g,'');
      card.hidden=!(activeFilter==='all'||card.dataset.group===activeFilter)||!text.includes(query);
      if(!card.hidden)visible++;
    }
    document.querySelector('#archive-results').textContent=visible===cards.length?'Showing all '+visible+' papers':'Showing '+visible+' of '+cards.length+' papers';
    document.querySelector('#archive-empty').hidden=visible!==0;
    filters.forEach(button=>{const selected=button.dataset.paperFilter===activeFilter;button.classList.toggle('selected',selected);button.setAttribute('aria-pressed',String(selected));});
    const grid=document.querySelector('#paper-grid'),toolbar=document.querySelector('.archive-toolbar'),header=document.querySelector('.site-header');
    if(grid.getBoundingClientRect().top<toolbar.getBoundingClientRect().bottom){window.scrollTo({top:window.scrollY+grid.getBoundingClientRect().top-header.offsetHeight-toolbar.offsetHeight-20,behavior:'instant'});}
  }
  filters.forEach(button=>button.addEventListener('click',()=>{activeFilter=button.dataset.paperFilter;filterPapers();}));
  search.addEventListener('input',filterPapers);
  document.querySelector('#reset-papers').addEventListener('click',()=>{activeFilter='all';search.value='';filterPapers();search.focus();});
  function choosePaper(id){
    current=research.find(r=>r.id===id)||research[0];page=1;select.value=current.id;
    document.querySelector('#paper-title').textContent=current.title;
    document.querySelector('#paper-status').textContent=current.problem+' / '+current.status;
    const note=paperNotes[current.id];
    document.querySelector('#paper-subtitle').textContent=(note.credit||'With Jensen Kohlmeyer')+' · '+note.topic;
    const downloads=document.querySelector('#paper-downloads');downloads.replaceChildren(download('PDF ↓',current.pdf),download('Source bundle ↓',current.bundle));
    current.lean.forEach((file,i)=>downloads.append(download(current.lean.length>1?'Lean '+(i+1)+' ↓':'Lean ↓',file,file.split('/').at(-1))));
    nav.querySelectorAll('button').forEach(b=>{const selected=b.dataset.paperId===current.id;b.classList.toggle('selected',selected);b.setAttribute('aria-current',String(selected));});
    document.querySelector('#page-zoom').setAttribute('aria-pressed','false');document.querySelector('#page-zoom').textContent='Zoom in +';stage.classList.remove('zoomed');
    drawPage();
  }
  async function drawPage(){
    const paper=current,targetPage=page,request=++textRequest;
    image.src=paper.pages[targetPage-1];image.alt=`${paper.title}, page ${targetPage} of ${paper.pageCount}`;
    pageInput.max=String(paper.pageCount);pageInput.value=String(targetPage);document.querySelector('#paper-page-total').textContent='/ '+paper.pageCount;
    document.querySelector('#page-prev').disabled=targetPage===1;document.querySelector('#page-next').disabled=targetPage===paper.pageCount;stage.scrollTop=0;stage.scrollLeft=0;
    document.querySelector('.reader-document').scrollTop=0;
    const pre=document.querySelector('#paper-text');pre.textContent='Loading page text…';
    try{if(!textCache.has(paper.id)){const r=await fetch(paper.text);if(!r.ok)throw new Error('Text unavailable');textCache.set(paper.id,await r.json());}if(request===textRequest)pre.textContent=textCache.get(paper.id)[targetPage-1]||'This page is best viewed in the original PDF.';}
    catch{if(request===textRequest)pre.textContent='The original page is shown above. The PDF download also preserves the text and mathematical notation.';}
  }
  function turn(delta){const next=Math.min(current.pageCount,Math.max(1,page+delta));if(next!==page){page=next;drawPage();}}
  select.addEventListener('change',()=>choosePaper(select.value));
  document.querySelector('#page-prev').addEventListener('click',()=>turn(-1));document.querySelector('#page-next').addEventListener('click',()=>turn(1));
  pageInput.addEventListener('change',()=>{const n=Number(pageInput.value);page=Number.isInteger(n)?Math.max(1,Math.min(current.pageCount,n)):page;drawPage();});
  stage.addEventListener('keydown',e=>{if(e.key==='ArrowLeft'){e.preventDefault();turn(-1);}if(e.key==='ArrowRight'){e.preventDefault();turn(1);}});
  document.querySelector('#page-zoom').addEventListener('click',e=>{const zoomed=stage.classList.toggle('zoomed');e.currentTarget.setAttribute('aria-pressed',String(zoomed));e.currentTarget.textContent=zoomed?'Fit width −':'Zoom in +';});
  document.querySelectorAll('[data-research]').forEach(button=>button.addEventListener('click',()=>{choosePaper(button.dataset.research);showModal(dialog);}));
  document.querySelector('#paper-count').textContent=research.length+' manuscripts · '+research.reduce((n,p)=>n+p.pageCount,0)+' pages';

  const media=document.querySelector('#media-dialog'),mediaStage=document.querySelector('#media-stage');wireDialog(media);
  function openMedia(title,kicker,url,help,kind){
    media.dataset.kind=kind;
    document.querySelector('#media-title').textContent=title;document.querySelector('#media-kicker').textContent=kicker;document.querySelector('#media-help').textContent=help;
    const iframe=document.createElement('iframe');iframe.title=title;iframe.src=url;iframe.allow='autoplay; fullscreen; gamepad';iframe.allowFullscreen=true;iframe.referrerPolicy='strict-origin-when-cross-origin';
    mediaStage.replaceChildren(iframe);showModal(media);
  }
  document.querySelectorAll('[data-play]').forEach(button=>button.addEventListener('click',()=>{const game=games.find(g=>g.id===button.dataset.play);if(game)openMedia(game.title,'PLAY ON SITE',game.playUrl,'WASD or arrow keys to drive · Space to drift · Use the game’s pause menu, or the × above to close.','game');}));
  document.querySelectorAll('[data-video]').forEach(button=>button.addEventListener('click',()=>openMedia(button.dataset.title,'WATCH ON SITE','https://www.youtube-nocookie.com/embed/'+encodeURIComponent(button.dataset.video)+'?rel=0','Video playback is provided by YouTube.','video')));
  media.addEventListener('close',()=>mediaStage.replaceChildren());
  document.querySelector('#media-fullscreen').addEventListener('click',async()=>{try{await mediaStage.requestFullscreen();}catch{document.querySelector('#media-help').textContent='Full screen is unavailable in this browser. The player still works here.';}});
}
