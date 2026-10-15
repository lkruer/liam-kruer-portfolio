const tau = Math.PI * 2;
const normalize = v => { const length = Math.hypot(...v) || 1; return v.map(n => n / length); };
const cross = (a, b) => [a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0]];
const dot = (a,b) => a[0]*b[0]+a[1]*b[1]+a[2]*b[2];
const forms = [
  {name:'CHROMATIC RIBBON', p:1, q:2, wave:.13, width:.57, thickness:.022, twist:1},
  {name:'DOUBLE TWIST', p:1, q:3, wave:.18, width:.48, thickness:.022, twist:2},
  {name:'WOVEN RIBBON', p:2, q:3, wave:.34, width:.32, thickness:.018, twist:1}
];

export function initSculpture(initialMotion) {
  const canvas = document.querySelector('#sculpture-canvas'), ctx = canvas.getContext('2d');
  const hero = document.querySelector('.hero');
  let width=700,height=650,motion=initialMotion,visible=true,formIndex=0,mesh=[],faces=[],frame=0,time=0,last=0;
  let pointerX=0,pointerY=0,tiltX=0,tiltY=0;
  const light=normalize([-.35,-.7,1]), half=normalize([-.18,-.35,1.4]);
  function center(u,f){const radius=1.12+f.wave*Math.cos(f.q*u);return [radius*Math.cos(f.p*u),radius*Math.sin(f.p*u),f.wave*1.3*Math.sin(f.q*u)];}
  function makeMesh(){
    const f=forms[formIndex], rings=width<500?104:156,sides=width<500?16:22; mesh=[];faces=[];
    for(let i=0;i<rings;i++){
      const u=i/rings*tau,c=center(u,f),c2=center(u+.001,f),t=normalize(c2.map((a,j)=>a-c[j]));
      const radial=[Math.cos(f.p*u),Math.sin(f.p*u),0];
      const n=normalize(radial.map((v,j)=>v-t[j]*dot(radial,t))),b=cross(t,n);
      const twist=f.twist*u+.25+Math.sin(f.q*u)*.12;
      const nn=n.map((x,k)=>x*Math.cos(twist)+b[k]*Math.sin(twist)),bb=b.map((x,k)=>x*Math.cos(twist)-n[k]*Math.sin(twist));
      for(let j=0;j<sides;j++){const v=j/sides*tau,cs=Math.cos(v),sn=Math.sin(v),px=Math.sign(cs)*Math.pow(Math.abs(cs),.48)*f.width,py=Math.sign(sn)*Math.pow(Math.abs(sn),.48)*f.thickness;
        const normal=normalize(nn.map((x,k)=>x*cs/f.width+bb[k]*sn/f.thickness));
        mesh.push({point:c.map((x,k)=>x+nn[k]*px+bb[k]*py),normal,u,v});}
    }
    for(let i=0;i<rings;i++)for(let j=0;j<sides;j++)faces.push([i*sides+j,((i+1)%rings)*sides+j,((i+1)%rings)*sides+(j+1)%sides,i*sides+(j+1)%sides]);
  }
  function resize(){const r=canvas.getBoundingClientRect();width=r.width;height=r.height;const dpr=Math.min(window.devicePixelRatio||1,1.75);canvas.width=Math.round(width*dpr);canvas.height=Math.round(height*dpr);ctx.setTransform(dpr,0,0,dpr,0,0);makeMesh();draw();}
  function draw(){
    if(!width||!height)return;
    ctx.clearRect(0,0,width,height);
    const scale=Math.min(width*.265,height*.275),cx=width*.51,cy=height*.50;
    const rx=.85+tiltY*.23,ry=-.23+Math.sin(time*.12)*.22+tiltX*.3,rz=-.35+time*.08;
    const sx=Math.sin(rx),cxr=Math.cos(rx),sy=Math.sin(ry),cyr=Math.cos(ry),sz=Math.sin(rz),cz=Math.cos(rz);
    function rotate(v){let [x,y,z]=v;[y,z]=[y*cxr-z*sx,y*sx+z*cxr];[x,z]=[x*cyr+z*sy,-x*sy+z*cyr];return [x*cz-y*sz,x*sz+y*cz,z];}
    ctx.save();ctx.translate(cx,cy);ctx.rotate(-.36);ctx.strokeStyle='#90bdc224';ctx.lineWidth=.65;ctx.beginPath();ctx.ellipse(0,0,scale*2.02,scale*.95,0,0,tau);ctx.stroke();
    ctx.strokeStyle='#a7be8b24';ctx.beginPath();ctx.ellipse(0,0,scale*2.13,scale*1.02,0,0,tau);ctx.stroke();
    const orbit=time*.25+.75;ctx.fillStyle='#d3ec89';ctx.shadowColor='#d3ec89';ctx.shadowBlur=13;ctx.beginPath();ctx.arc(Math.cos(orbit)*scale*2.02,Math.sin(orbit)*scale*.95,3.1,0,tau);ctx.fill();ctx.restore();
    const transformed=mesh.map(v=>{const p=rotate(v.point),n=rotate(v.normal),perspective=4.7/(4.7-p[2]);return{x:cx+p[0]*scale*perspective,y:cy+p[1]*scale*perspective,z:p[2],normal:n,u:v.u,v:v.v};});
    const sorted=faces.map(ids=>({ids,depth:ids.reduce((s,i)=>s+transformed[i].z,0)/4})).sort((a,b)=>a.depth-b.depth);
    for(const face of sorted){
      const v=face.ids.map(i=>transformed[i]),normal=normalize([0,1,2].map(k=>v.reduce((s,p)=>s+p.normal[k],0)));
      const diffuse=Math.max(0,dot(normal,light)),spec=Math.pow(Math.max(0,dot(normal,half)),24),rim=Math.pow(1-Math.abs(normal[2]),3);
      const warmth=(Math.sin(v[0].u*1.3+1.4)+1)/2,shade=.17+diffuse*.77;
      let r=(75+175*warmth)*shade+155*spec+19*rim,g=(35+142*(1-warmth))*shade+150*spec+28*rim,b=(230-50*warmth)*shade+140*spec+33*rim;
      ctx.fillStyle=`rgb(${Math.min(255,r)|0},${Math.min(255,g)|0},${Math.min(255,b)|0})`;ctx.strokeStyle=ctx.fillStyle;ctx.lineWidth=.55;
      ctx.beginPath();v.forEach((p,i)=>i?ctx.lineTo(p.x,p.y):ctx.moveTo(p.x,p.y));ctx.closePath();ctx.fill();ctx.stroke();
    }
    // A small coordinate marker gives the generated sculpture a drawing-board origin.
    const originX=cx-scale*1.72,originY=cy+scale*1.33;ctx.strokeStyle='#8aa3a64a';ctx.lineWidth=.7;ctx.beginPath();ctx.moveTo(originX-6,originY);ctx.lineTo(originX+6,originY);ctx.moveTo(originX,originY-6);ctx.lineTo(originX,originY+6);ctx.stroke();
  }
  function loop(timestamp){frame=requestAnimationFrame(loop);if(!visible||document.hidden||!motion)return;if(timestamp-last<32)return;const dt=Math.min((timestamp-last)/1000,.06);last=timestamp;time+=dt;tiltX+=(pointerX-tiltX)*.055;tiltY+=(pointerY-tiltY)*.055;draw();}
  hero.addEventListener('pointermove',e=>{const r=hero.getBoundingClientRect();pointerX=(e.clientX-r.left)/r.width-.5;pointerY=(e.clientY-r.top)/r.height-.5;});
  hero.addEventListener('pointerleave',()=>{pointerX=pointerY=0;});
  new IntersectionObserver(entries=>{visible=entries[0].isIntersecting;},{threshold:0}).observe(hero);
  new ResizeObserver(resize).observe(canvas);
  document.querySelector('#remix-form').addEventListener('click',()=>{formIndex=(formIndex+1)%forms.length;makeMesh();draw();document.querySelector('#form-label').innerHTML=`FIG. 0${formIndex+1} — ${forms[formIndex].name}<br><b>IDEAS INTO MOTION</b>`;document.querySelector('#form-count').textContent=`0${formIndex+1} / 03`;});
  resize();frame=requestAnimationFrame(loop);
  return {setMotion(value){motion=value;last=0;},destroy(){cancelAnimationFrame(frame);}};
}
