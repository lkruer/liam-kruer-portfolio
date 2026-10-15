import {initMath} from './math.js?v=design-audit-1';
import {initSculpture} from './sculpture-webgl.js';
import {games,articles} from './content.js';
import {initWork} from './work.js?v=design-audit-1';

const reduceMotion=matchMedia('(prefers-reduced-motion: reduce)');
let moving=!reduceMotion.matches;
const sculpture=initSculpture(moving);
const motionButton=document.querySelector('#motion-toggle');
function updateMotion(){sculpture.setMotion(moving&&!document.querySelector('dialog[open]'));motionButton.setAttribute('aria-pressed',String(!moving));motionButton.innerHTML=moving?'<span aria-hidden="true">Ⅱ</span> Pause motion':'<span aria-hidden="true">▷</span> Resume motion';document.body.classList.toggle('motion-paused',!moving);}
motionButton.addEventListener('click',()=>{moving=!moving;updateMotion();});
reduceMotion.addEventListener('change',event=>{moving=!event.matches;updateMotion();});updateMotion();
initMath();

const menu=document.querySelector('#main-nav'),toggle=document.querySelector('.menu-toggle');
function closeMenu(){toggle.setAttribute('aria-expanded','false');toggle.setAttribute('aria-label','Open navigation');menu.classList.remove('open');}
toggle.addEventListener('click',()=>{const open=toggle.getAttribute('aria-expanded')!=='true';toggle.setAttribute('aria-expanded',String(open));toggle.setAttribute('aria-label',open?'Close navigation':'Open navigation');menu.classList.toggle('open',open);});
menu.querySelectorAll('a').forEach(link=>link.addEventListener('click',closeMenu));
document.addEventListener('pointerdown',event=>{if(toggle.getAttribute('aria-expanded')==='true'&&!document.querySelector('.site-header').contains(event.target))closeMenu();});
matchMedia('(min-width: 801px)').addEventListener('change',event=>{if(event.matches)closeMenu();});
document.addEventListener('keydown',event=>{if(event.key==='Escape')closeMenu();});
const chapterObserver=new IntersectionObserver(entries=>{const selected=entries.find(e=>e.isIntersecting);if(selected)menu.querySelectorAll('a').forEach(a=>a.classList.toggle('active',a.hash==='#'+selected.target.id));},{rootMargin:'-12% 0px -65% 0px'});
document.querySelectorAll('main>section[id]').forEach(section=>chapterObserver.observe(section));

const list=document.querySelector('#game-list');
games.filter(game=>game.id!=='sundrift').forEach((game,index)=>{const link=document.createElement('button');link.type='button';link.className='shelf-game';link.dataset.play=game.id;
  const items=[['span',String(games.indexOf(game)+1).padStart(2,'0'),'shelf-number'],['strong',game.title,''],['span',game.subtitle,'shelf-subtitle'],['span',game.platform+' / '+game.year,'shelf-platform'],['span','PLAY ↗','shelf-play']];
  items.forEach(([tag,text,className])=>{const element=document.createElement(tag);element.textContent=text;element.className=className;link.append(element);});list.append(link);
});document.querySelector('#game-count').textContent='['+String(games.length).padStart(2,'0')+']';
document.querySelector('.game-shelf').classList.toggle('shelf-empty',list.children.length===0);
initWork();
const modalMotionObserver=new MutationObserver(updateMotion);
document.querySelectorAll('dialog').forEach(dialog=>modalMotionObserver.observe(dialog,{attributes:true,attributeFilter:['open']}));

const articleDialog=document.querySelector('#article-dialog'),articleContent=document.querySelector('#article-content');
document.querySelectorAll('[data-article]').forEach(button=>button.addEventListener('click',()=>{const article=articles[button.dataset.article];articleContent.replaceChildren();
  const kicker=document.createElement('p');kicker.className='dialog-kicker';kicker.textContent=article.category;articleContent.append(kicker);
  const title=document.createElement('h2');title.id='article-title';title.textContent=article.title;articleContent.append(title);
  article.body.forEach(([tag,text])=>{const p=document.createElement(tag);p.textContent=text;articleContent.append(p);});
  const downloads=document.createElement('div');downloads.className='note-downloads';
  const source=document.createElement('a');source.className='text-link';source.href='assets/work/notes/'+button.dataset.article+'.md';source.download='';source.textContent='Download this note ↓';downloads.append(source);
  const full=document.createElement('a');full.className='text-link';full.href='assets/work/sundrift/NOTES.md';full.download='';full.textContent='Full development log ↓';downloads.append(full);articleContent.append(downloads);
  const note=document.createElement('p');note.className='article-note';note.textContent='A summary of the public Sundrift development record. Built and iterated with AI-assisted tools; source and development notes linked above.';articleContent.append(note);
  articleDialog.showModal();articleDialog.scrollTop=0;document.body.style.overflow='hidden';
}));
document.querySelector('.dialog-close').addEventListener('click',()=>articleDialog.close());
articleDialog.addEventListener('close',()=>{document.body.style.overflow=document.querySelector('dialog[open]')?'hidden':'';});
articleDialog.addEventListener('click',event=>{const r=articleDialog.getBoundingClientRect();if(event.clientX<r.left||event.clientX>r.right||event.clientY<r.top||event.clientY>r.bottom)articleDialog.close();});

const jump=document.querySelector('#jump-dialog'),search=document.querySelector('#jump-search'),jumpLinks=[...document.querySelectorAll('#jump-links a')];
function filterJump(){let count=0;for(const link of jumpLinks){const match=link.textContent.toLowerCase().includes(search.value.toLowerCase());link.hidden=!match;if(match)count++;}document.querySelector('#jump-empty').hidden=count>0;}
function openJump(){document.querySelectorAll('dialog[open]').forEach(dialog=>dialog.close());closeMenu();search.value='';filterJump();jump.showModal();document.body.style.overflow='hidden';search.focus();}
document.querySelector('#quick-jump').addEventListener('click',openJump);
document.querySelector('.jump-close').addEventListener('click',()=>jump.close());
jump.addEventListener('close',()=>{document.body.style.overflow=document.querySelector('dialog[open]')?'hidden':'';});
jump.addEventListener('click',event=>{const r=jump.getBoundingClientRect();if(event.clientX<r.left||event.clientX>r.right||event.clientY<r.top||event.clientY>r.bottom)jump.close();});
search.addEventListener('input',filterJump);
search.addEventListener('keydown',event=>{if(event.key==='ArrowDown'){event.preventDefault();jumpLinks.find(a=>!a.hidden)?.focus();}if(event.key==='Enter'){event.preventDefault();jumpLinks.find(a=>!a.hidden)?.click();}});
jumpLinks.forEach(link=>{link.addEventListener('click',()=>jump.close());link.addEventListener('keydown',event=>{if(event.key==='ArrowDown'||event.key==='ArrowUp'){event.preventDefault();const shown=jumpLinks.filter(a=>!a.hidden),current=shown.indexOf(link);shown[(current+(event.key==='ArrowDown'?1:-1)+shown.length)%shown.length].focus();}});});
document.addEventListener('keydown',event=>{if((event.ctrlKey||event.metaKey)&&event.key.toLowerCase()==='k'){event.preventDefault();jump.open?jump.close():openJump();}});
if(/Mac|iPhone|iPad/.test(navigator.platform))document.querySelector('.quick-jump kbd').textContent='⌘ K';

const progress=document.querySelector('.reading-progress');let scrollPending=false;
function updateProgress(){const max=document.documentElement.scrollHeight-innerHeight;progress.style.transform='scaleX('+(max>0?scrollY/max:0)+')';scrollPending=false;}
addEventListener('scroll',()=>{if(!scrollPending){scrollPending=true;requestAnimationFrame(updateProgress);}},{passive:true});
addEventListener('resize',updateProgress);updateProgress();
new ResizeObserver(updateProgress).observe(document.body);
document.querySelector('#year').textContent=new Date().getFullYear();

// Resolve a shared section link after fonts and initial layout have settled.
// Respect a visitor who has already started scrolling or chosen another section.
if(location.hash){
  const initialHash=location.hash;
  let interrupted=false;
  for(const event of ['wheel','touchstart','keydown'])addEventListener(event,()=>{interrupted=true;},{once:true,passive:true});
  const loaded=document.readyState==='complete'?Promise.resolve():new Promise(resolve=>addEventListener('load',resolve,{once:true}));
  Promise.all([document.fonts.ready,loaded]).then(()=>{
    let target;
    try{target=document.getElementById(decodeURIComponent(initialHash.slice(1)));}catch{return;}
    if(target&&!interrupted&&location.hash===initialHash)requestAnimationFrame(()=>target.scrollIntoView({behavior:'instant',block:'start'}));
  });
}
