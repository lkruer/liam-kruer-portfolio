import {research} from './research-catalog.js';
import {hexagonSubmissions} from './hexagon-research.js';
import {games} from './content.js';
import {paperNotes} from './paper-notes.js';

function initPaperSearch() {
  const search = document.querySelector('#paper-search');
  const status = document.querySelector('#archive-results');
  const empty = document.querySelector('#archive-empty');
  const normalize = text => text.toLowerCase().normalize('NFD').replace(/\p{M}/gu, '');
  const groups = [...document.querySelectorAll('.research-group')].map(group => ({
    group,
    count: group.querySelector('[data-group-count]'),
    rows: [...group.querySelectorAll('.paper-row')].map(row => ({
      row,
      text: normalize(row.querySelector('h3').textContent + ' ' + row.dataset.paperSearch),
    })),
  }));
  const total = groups.reduce((sum, { rows }) => sum + rows.length, 0);
  let openedBeforeSearch;

  function filterPapers() {
    const words = normalize(search.value).trim().split(/\s+/).filter(Boolean);
    const searching = words.length > 0;
    if (searching && !openedBeforeSearch) {
      openedBeforeSearch = groups.map(({ group }) => group.open);
    }

    let matches = 0;
    groups.forEach(({ group, count, rows }, index) => {
      let groupMatches = 0;
      rows.forEach(({ row, text }) => {
        row.hidden = !words.every(word => text.includes(word));
        if (!row.hidden) groupMatches += 1;
      });
      group.hidden = searching && groupMatches === 0;
      if (searching) group.open = groupMatches > 0;
      else if (openedBeforeSearch) group.open = openedBeforeSearch[index];
      count.textContent = groupMatches + (groupMatches === 1 ? ' paper' : ' papers');
      matches += groupMatches;
    });

    if (!searching) openedBeforeSearch = undefined;
    status.textContent = searching ? matches + ' of ' + total + ' papers' : total + ' papers';
    empty.hidden = matches > 0;
  }

  function openLinkedGroup() {
    const entry = groups.find(({ group }) => location.hash === '#' + group.id);
    if (entry && !entry.group.hidden) entry.group.open = true;
  }

  search.addEventListener('input', filterPapers);
  document.querySelector('#reset-papers').addEventListener('click', () => {
    search.value = '';
    filterPapers();
    search.focus();
  });
  filterPapers();
  openLinkedGroup();
  window.addEventListener('hashchange', openLinkedGroup);
}

export function initWork(){
  const papers = [...hexagonSubmissions, ...research];
  const dialog=document.querySelector('#research-dialog'),select=document.querySelector('#paper-select'),nav=document.querySelector('#paper-nav');
  const image=document.querySelector('#paper-image'),pageInput=document.querySelector('#paper-page'),stage=document.querySelector('#paper-stage');
  let current=papers[0],page=1,textRequest=0;
  const textCache=new Map();
  const lock=()=>{document.body.style.overflow=document.querySelector('dialog[open]')?'hidden':'';};
  function showModal(target){document.querySelectorAll('dialog[open]').forEach(d=>d.close());target.showModal();if(target===dialog){document.querySelector('.reader-document').scrollTop=0;stage.scrollTop=0;}lock();}
  function wireDialog(target){target.querySelector('.viewer-close').addEventListener('click',()=>target.close());target.addEventListener('close',lock);target.addEventListener('click',e=>{const r=target.getBoundingClientRect();if(e.clientX<r.left||e.clientX>r.right||e.clientY<r.top||e.clientY>r.bottom)target.close();});}
  wireDialog(dialog);
  for(const paper of papers){
    const option=document.createElement('option');option.value=paper.id;option.textContent=paper.problem+' — '+paper.title;select.append(option);
    const button=document.createElement('button');button.type='button';button.dataset.paperId=paper.id;
    const tag=document.createElement('span');tag.textContent=paper.problem+' / '+paper.status;
    const title=document.createElement('strong');title.textContent=paper.title;
    button.append(tag,title);button.addEventListener('click',()=>choosePaper(paper.id));nav.append(button);
  }
  function download(label,href,title){const a=document.createElement('a');a.href=href;a.download='';a.textContent=label;a.title=title||label;return a;}
  initPaperSearch();
  function choosePaper(id){
    current=papers.find(paper=>paper.id===id)||papers[0];page=1;select.value=current.id;
    document.querySelector('#paper-title').textContent=current.title;
    document.querySelector('#paper-status').textContent=current.problem+' / '+current.status;
    const note = current.record ? current : paperNotes[current.id];
    document.querySelector('#paper-subtitle').textContent = (note.credit || 'With Jensen Kohlmeyer') + ' · ' + note.topic;
    document.querySelector('#paper-summary').textContent = note.summary;
    const downloads=document.querySelector('#paper-downloads');downloads.replaceChildren(download('PDF',current.pdf),download('Source bundle',current.bundle));
    const leanFiles = current.lean || [];
    leanFiles.forEach((file, i) => {
      const label = leanFiles.length > 1 ? 'Lean ' + (i + 1) : 'Lean';
      downloads.append(download(label, file, file.split('/').at(-1)));
    });
    if (current.record) {
      const record = document.createElement('a');
      record.href = current.record;
      record.textContent = 'Hexagon record';
      downloads.append(record);
    }
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

  const media=document.querySelector('#media-dialog'),mediaStage=document.querySelector('#media-stage');wireDialog(media);
  function openMedia(title,kicker,url,help,kind){
    media.dataset.kind=kind;
    document.querySelector('#media-title').textContent=title;document.querySelector('#media-kicker').textContent=kicker;document.querySelector('#media-help').textContent=help;
    const iframe=document.createElement('iframe');iframe.title=title;iframe.src=url;iframe.allow='autoplay; fullscreen; gamepad';iframe.allowFullscreen=true;iframe.referrerPolicy='strict-origin-when-cross-origin';
    mediaStage.replaceChildren(iframe);showModal(media);
  }
  document.querySelectorAll('[data-play]').forEach(button=>button.addEventListener('click',()=>{const game=games.find(g=>g.id===button.dataset.play);if(game)openMedia(game.title,'Browser game',game.playUrl,'WASD or arrow keys to drive · Space to drift · Use the game’s pause menu, or the × above to close.','game');}));
  document.querySelectorAll('[data-video]').forEach(button => button.addEventListener('click', () => {
    const videoId = encodeURIComponent(button.dataset.video);
    openMedia(button.dataset.title, 'Video', 'https://www.youtube-nocookie.com/embed/' + videoId + '?rel=0', '', 'video');
    const link = document.createElement('a');
    link.href = 'https://www.youtube.com/watch?v=' + videoId;
    link.target = '_blank';
    link.rel = 'noopener noreferrer';
    link.textContent = 'Watch on YouTube';
    document.querySelector('#media-help').append(link);
  }));
  media.addEventListener('close',()=>mediaStage.replaceChildren());
  document.querySelector('#media-fullscreen').addEventListener('click',async()=>{try{await mediaStage.requestFullscreen();}catch{document.querySelector('#media-help').textContent='Full screen is unavailable in this browser. The player still works here.';}});
}
