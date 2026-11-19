import {initMath} from './math.js?v=engineering';
import {games,articles} from './content.js';
import {initWork} from './work.js?v=compact';

initMath();

const menu=document.querySelector('#main-nav'),toggle=document.querySelector('.menu-toggle');
function closeMenu(){toggle.setAttribute('aria-expanded','false');toggle.setAttribute('aria-label','Open navigation');menu.classList.remove('open');}
toggle.addEventListener('click',()=>{const open=toggle.getAttribute('aria-expanded')!=='true';toggle.setAttribute('aria-expanded',String(open));toggle.setAttribute('aria-label',open?'Close navigation':'Open navigation');menu.classList.toggle('open',open);});
menu.querySelectorAll('a').forEach(link=>link.addEventListener('click',closeMenu));
document.addEventListener('pointerdown',event=>{if(toggle.getAttribute('aria-expanded')==='true'&&!document.querySelector('.site-header').contains(event.target))closeMenu();});
matchMedia('(min-width: 801px)').addEventListener('change',event=>{if(event.matches)closeMenu();});
document.addEventListener('keydown',event=>{if(event.key==='Escape')closeMenu();});
const chapters = [...document.querySelectorAll('main > section[id]')];
const navLinks = new Map([...menu.querySelectorAll('a')].map(link => [link.hash, link]));
const header = document.querySelector('.site-header');
let activeLink;
let updateQueued = false;

function updateSectionNav() {
  updateQueued = false;
  const page = document.documentElement;
  const atBottom = scrollY > 0 && Math.ceil(scrollY + page.clientHeight) >= page.scrollHeight - 2;
  const readingLine = header.offsetHeight + Math.min(160, page.clientHeight * .16);
  let current = chapters[0];

  if (atBottom) {
    current = chapters.at(-1);
  } else {
    for (const chapter of chapters) {
      if (chapter.getBoundingClientRect().top > readingLine) break;
      current = chapter;
    }
  }

  const nextLink = navLinks.get('#' + current.id);
  if (nextLink === activeLink) return;
  activeLink?.removeAttribute('aria-current');
  nextLink?.setAttribute('aria-current', 'location');
  activeLink = nextLink;
}

function queueSectionNavUpdate() {
  if (updateQueued) return;
  updateQueued = true;
  requestAnimationFrame(updateSectionNav);
}

addEventListener('scroll', queueSectionNavUpdate, { passive: true });
addEventListener('resize', queueSectionNavUpdate);
updateSectionNav();

const headingObserver = new IntersectionObserver(entries => {
  for (const entry of entries) {
    if (!entry.isIntersecting) continue;
    entry.target.classList.add('section-arrival');
    headingObserver.unobserve(entry.target);
  }
}, { rootMargin: '0px 0px -8% 0px' });
document.querySelectorAll('main > section h2[id]').forEach(heading => {
  headingObserver.observe(heading.closest('.section-heading') ?? heading);
});

const list = document.querySelector('#game-list');
for (const game of games.filter(game => game.id !== 'sundrift')) {
  const button = document.createElement('button');
  button.type = 'button';
  button.className = 'button secondary';
  button.dataset.play = game.id;
  button.textContent = 'Play ' + game.title;
  list.append(button);
}
list.hidden = list.children.length === 0;
initWork();

const articleDialog=document.querySelector('#article-dialog'),articleContent=document.querySelector('#article-content');
document.querySelectorAll('[data-article]').forEach(button=>button.addEventListener('click',()=>{const article=articles[button.dataset.article];articleContent.replaceChildren();
  const kicker=document.createElement('p');kicker.className='dialog-kicker';kicker.textContent=article.category;articleContent.append(kicker);
  const title=document.createElement('h2');title.id='article-title';title.textContent=article.title;articleContent.append(title);
  article.body.forEach(([tag,text])=>{const p=document.createElement(tag);p.textContent=text;articleContent.append(p);});
  const downloads=document.createElement('div');downloads.className='note-downloads';
  const source=document.createElement('a');source.className='text-link';source.href='assets/work/notes/'+button.dataset.article+'.md';source.download='';source.textContent='Download this note';downloads.append(source);
  const full=document.createElement('a');full.className='text-link';full.href='assets/work/sundrift/NOTES.md';full.download='';full.textContent='Full development log';downloads.append(full);articleContent.append(downloads);
  const note=document.createElement('p');note.className='article-note';note.textContent='A summary of the public Sundrift development record. Built and iterated with AI-assisted tools; source and development notes linked above.';articleContent.append(note);
  articleDialog.showModal();articleDialog.scrollTop=0;document.body.style.overflow='hidden';
}));
document.querySelector('.dialog-close').addEventListener('click',()=>articleDialog.close());
articleDialog.addEventListener('close',()=>{document.body.style.overflow=document.querySelector('dialog[open]')?'hidden':'';});
articleDialog.addEventListener('click',event=>{const r=articleDialog.getBoundingClientRect();if(event.clientX<r.left||event.clientX>r.right||event.clientY<r.top||event.clientY>r.bottom)articleDialog.close();});

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
