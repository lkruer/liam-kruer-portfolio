import {initSculpture as initFallback} from './sculpture.js';

const TAU=Math.PI*2;
const forms=[{name:'CHROMATIC RIBBON',p:1,q:2,wave:.13,width:.57,thickness:.022,twist:1},{name:'DOUBLE TWIST',p:1,q:3,wave:.18,width:.48,thickness:.022,twist:2},{name:'WOVEN RIBBON',p:2,q:3,wave:.34,width:.32,thickness:.018,twist:1}];
const normalize=v=>{const l=Math.hypot(...v)||1;return v.map(n=>n/l);};
const cross=(a,b)=>[a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]];
const dot=(a,b)=>a[0]*b[0]+a[1]*b[1]+a[2]*b[2];

const vertexSource=`
precision highp float;
attribute vec3 a_position;
attribute vec3 a_normal;
attribute vec2 a_uv;
uniform mat3 u_rotation;
uniform vec2 u_scale;
uniform vec2 u_offset;
uniform float u_shell;
varying vec3 v_position;
varying vec3 v_normal;
varying vec2 v_uv;
void main(){
  vec3 p=u_rotation*(a_position*u_shell);
  float w=5.2-p.z;
  gl_Position=vec4(p.xy*u_scale*5.2+u_offset*w,-p.z*.25*w,w);
  v_position=p;
  v_normal=u_rotation*a_normal;
  v_uv=a_uv;
}`;

const fragmentSource=`
precision highp float;
varying vec3 v_position;
varying vec3 v_normal;
varying vec2 v_uv;
uniform vec2 u_pointer;
vec3 palette(float t){
  t=fract(t)*4.0;
  vec3 cyan=vec3(.005,.78,1.0);
  vec3 violet=vec3(.25,.025,1.0);
  vec3 pink=vec3(1.0,.018,.29);
  vec3 orange=vec3(1.0,.37,.08);
  if(t<1.0)return mix(cyan,violet,smoothstep(0.0,1.0,t));
  if(t<2.0)return mix(violet,pink,smoothstep(1.0,2.0,t));
  if(t<3.0)return mix(pink,orange,smoothstep(2.0,3.0,t));
  return mix(orange,cyan,smoothstep(3.0,4.0,t));
}
float softbox(vec3 r,vec3 direction,float sharpness){return pow(max(dot(r,normalize(direction)),0.0),sharpness);}
void main(){
  vec3 n=normalize(v_normal);
  vec3 eye=normalize(vec3(0.0,0.0,5.2)-v_position);
  vec3 r=reflect(-eye,n);
  float facing=max(dot(n,eye),0.0);
  vec3 base=palette(v_uv.x*.91+v_uv.y*.075+.035);
  vec3 light=normalize(vec3(-1.1+u_pointer.x*.85,1.3+u_pointer.y*.65,2.3));
  float diffuse=max(dot(n,light),0.0);
  float fresnel=pow(1.0-facing,3.0);
  // Soft studio reflections move across the interpolated surface normals.
  float key=softbox(r,vec3(-.62+u_pointer.x*.40,.88+u_pointer.y*.3,1.0),38.0);
  float broad=softbox(r,vec3(.4,-.28,1.0),5.0);
  float strip=pow(max(1.0-abs(dot(r,normalize(vec3(.87,.36,.27))))/.095,0.0),2.0);
  float stripEnd=smoothstep(-.45,.3,r.y);
  float cyan=softbox(r,vec3(-1.2,-.25,.4),12.0);
  float pink=softbox(r,vec3(1.2,.1,.3),10.0);
  vec3 metal=base*(.30+diffuse*.72+broad*.78);
  metal+=mix(base,vec3(1.0),.65)*key*2.2;
  metal+=mix(base,vec3(.65,.91,1.0),.72)*strip*stripEnd*1.45;
  metal+=vec3(.005,.8,1.0)*cyan*.64;
  metal+=vec3(1.0,.025,.46)*pink*.57;
  metal+=palette(v_uv.x+.13)*fresnel*.72;
  metal*=.985+.015*sin(v_uv.y*900.0);
  vec3 color=vec3(1.0)-exp(-metal*1.12);
  color=pow(color,vec3(.78));
  gl_FragColor=vec4(color,1.0);
}`;

const wireSource=`
precision highp float;
varying vec3 v_normal;
varying vec3 v_position;
varying vec2 v_uv;
uniform float u_alpha;
void main(){
  vec3 eye=normalize(vec3(0.0,0.0,5.2)-v_position);
  float front=.13+.87*max(dot(normalize(v_normal),eye),0.0);
  vec3 color=mix(vec3(.03,.83,1.0),vec3(.9,.10,1.0),smoothstep(.1,.9,v_uv.x));
  float alpha=u_alpha*front;
  gl_FragColor=vec4(color*alpha,alpha);
}`;

function compile(gl,type,source){const shader=gl.createShader(type);gl.shaderSource(shader,source);gl.compileShader(shader);if(!gl.getShaderParameter(shader,gl.COMPILE_STATUS))throw new Error(gl.getShaderInfoLog(shader));return shader;}
function program(gl,fragment){const p=gl.createProgram();const v=compile(gl,gl.VERTEX_SHADER,vertexSource),f=compile(gl,gl.FRAGMENT_SHADER,fragment);gl.attachShader(p,v);gl.attachShader(p,f);gl.linkProgram(p);gl.deleteShader(v);gl.deleteShader(f);if(!gl.getProgramParameter(p,gl.LINK_STATUS))throw new Error(gl.getProgramInfoLog(p));return p;}
function rotation(rx,ry,rz){
  const sx=Math.sin(rx),cx=Math.cos(rx),sy=Math.sin(ry),cy=Math.cos(ry),sz=Math.sin(rz),cz=Math.cos(rz);
  return new Float32Array([cz*cy,sz*cy,-sy,cz*sy*sx-sz*cx,sz*sy*sx+cz*cx,cy*sx,cz*sy*cx+sz*sx,sz*sy*cx-cz*sx,cy*cx]);
}

function buildMesh(form){
  const rings=256,sides=64,stride=sides+1,positions=[];
  function center(u){const r=1.12+form.wave*Math.cos(form.q*u);return[r*Math.cos(form.p*u),r*Math.sin(form.p*u),form.wave*1.3*Math.sin(form.q*u)];}
  for(let i=0;i<rings;i++){
    const u=i/rings*TAU,c=center(u),prev=center(u-.001),next=center(u+.001),t=normalize(next.map((v,k)=>v-prev[k]));
    const radial=[Math.cos(form.p*u),Math.sin(form.p*u),0],n=normalize(radial.map((v,k)=>v-t[k]*dot(radial,t))),b=cross(t,n);
    // A broad, nearly flat strip with a tiny rounded edge, twisted along its length.
    // The superellipse gives it two large faces and a thin rim rather than a tubular section.
    const twist=form.twist*u+.25+Math.sin(form.q*u)*.12;
    const normal=n.map((v,k)=>v*Math.cos(twist)+b[k]*Math.sin(twist));
    const binormal=b.map((v,k)=>v*Math.cos(twist)-n[k]*Math.sin(twist));
    for(let j=0;j<sides;j++){
      const v=j/sides*TAU,crossX=Math.sign(Math.cos(v))*Math.pow(Math.abs(Math.cos(v)),.48)*form.width;
      const crossY=Math.sign(Math.sin(v))*Math.pow(Math.abs(Math.sin(v)),.48)*form.thickness;
      positions.push(c.map((x,k)=>x+normal[k]*crossX+binormal[k]*crossY));
    }
  }
  const at=(i,j)=>positions[((i+rings)%rings)*sides+(j+sides)%sides],data=[];
  for(let i=0;i<=rings;i++)for(let j=0;j<=sides;j++){
    const pos=at(i,j),u1=at(i+1,j),u0=at(i-1,j),v1=at(i,j+1),v0=at(i,j-1);
    const du=u1.map((v,k)=>v-u0[k]),dv=v1.map((v,k)=>v-v0[k]),normal=normalize(cross(dv,du));
    data.push(...pos,...normal,i/rings,j/sides);
  }
  const triangles=[],wire=[],ghost=[];
  for(let i=0;i<rings;i++)for(let j=0;j<sides;j++){
    const a=i*stride+j,b=(i+1)*stride+j;triangles.push(a,a+1,b,a+1,b+1,b);
    if(i%8===0)wire.push(a,a+1);if(j%8===0)wire.push(a,b);
    if(i%32===0)ghost.push(a,a+1);if(j%16===0)ghost.push(a,b);
  }
  return{data:new Float32Array(data),triangles:new Uint16Array(triangles),wire:new Uint16Array(wire),ghost:new Uint16Array(ghost)};
}

export function initSculpture(initialMotion){
  const canvas=document.querySelector('#sculpture-canvas'),hero=document.querySelector('.hero'),container=document.querySelector('.sculpture');
  let gl,solid,wire;
  try{gl=canvas.getContext('webgl',{alpha:true,antialias:true,premultipliedAlpha:true,powerPreference:'low-power'});if(!gl)throw new Error('WebGL unavailable');solid=program(gl,fragmentSource);wire=program(gl,wireSource);}
  catch{const replacement=canvas.cloneNode();canvas.replaceWith(replacement);container.classList.add('fallback-renderer');document.querySelector('#wire-toggle').hidden=true;return initFallback(initialMotion);}
  canvas.dataset.renderer='smooth-webgl';
  const field=document.createElement('canvas');field.className='wire-field';field.setAttribute('aria-hidden','true');container.insertBefore(field,canvas);const ctx=field.getContext('2d');
  let width=1,height=1,dpr=1,time=0,last=0,frame=0,moving=initialMotion,visible=true,formIndex=0,meshMode=false;
  let pointerX=0,pointerY=0,tiltX=0,tiltY=0,yaw=0,pitch=0,dragging=false,lastX=0,lastY=0;
  const buffers={vertex:gl.createBuffer(),triangles:gl.createBuffer(),wire:gl.createBuffer(),ghost:gl.createBuffer()};let counts={};
  const uniforms=new Map();
  for(const p of [solid,wire])uniforms.set(p,Object.fromEntries(['rotation','scale','offset','shell','pointer','alpha'].map(key=>[key,gl.getUniformLocation(p,'u_'+key)])));
  function geometry(){const mesh=buildMesh(forms[formIndex]);gl.bindBuffer(gl.ARRAY_BUFFER,buffers.vertex);gl.bufferData(gl.ARRAY_BUFFER,mesh.data,gl.STATIC_DRAW);for(const key of ['triangles','wire','ghost']){gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER,buffers[key]);gl.bufferData(gl.ELEMENT_ARRAY_BUFFER,mesh[key],gl.STATIC_DRAW);counts[key]=mesh[key].length;}}
  function bind(p,rot,scale,cx,cy,shell){
    gl.useProgram(p);gl.bindBuffer(gl.ARRAY_BUFFER,buffers.vertex);
    for(const [name,size,offset]of [['a_position',3,0],['a_normal',3,12],['a_uv',2,24]]){const location=gl.getAttribLocation(p,name);if(location>=0){gl.enableVertexAttribArray(location);gl.vertexAttribPointer(location,size,gl.FLOAT,false,32,offset);}}
    const u=uniforms.get(p);gl.uniformMatrix3fv(u.rotation,false,rot);gl.uniform2f(u.scale,scale*2/width,scale*2/height);gl.uniform2f(u.offset,cx/width*2-1,1-cy/height*2);gl.uniform1f(u.shell,shell);if(u.pointer)gl.uniform2f(u.pointer,tiltX,-tiltY);
  }
  function fieldDraw(cx,cy,scale){
    ctx.clearRect(0,0,width,height);ctx.lineWidth=.7;ctx.save();ctx.translate(cx,cy);ctx.rotate(-.3+tiltX*.13);
    const a=scale*2.12,b=scale*.93;
    for(let ring=-3;ring<=3;ring++){const t=ring/4,r=Math.sqrt(1-t*t);ctx.strokeStyle=ring%2?'rgba(38,210,255,.11)':'rgba(148,77,255,.14)';ctx.beginPath();ctx.ellipse(t*scale*.27,t*scale*.66,a*r,b*r,0,0,TAU);ctx.stroke();}
    for(let j=0;j<8;j++){ctx.strokeStyle=j%2?'rgba(32,184,255,.08)':'rgba(122,83,255,.09)';ctx.beginPath();ctx.ellipse(0,0,a*Math.max(.04,Math.abs(Math.cos(j/8*Math.PI+time*.028))),b,0,0,TAU);ctx.stroke();}
    ctx.setLineDash([2,8]);ctx.strokeStyle='rgba(27,230,255,.26)';ctx.beginPath();ctx.ellipse(0,0,a*1.14,b*1.13,0,0,TAU);ctx.stroke();ctx.setLineDash([]);
    for(let i=0;i<3;i++){const angle=time*(i===1?-.16:.13)+i*2.2;ctx.fillStyle=i===1?'#ff39ca':'#2ae6ff';ctx.shadowColor=ctx.fillStyle;ctx.shadowBlur=12;ctx.beginPath();ctx.arc(Math.cos(angle)*a*1.14,Math.sin(angle)*b*1.13,2.4,0,TAU);ctx.fill();}
    ctx.restore();ctx.shadowBlur=0;ctx.strokeStyle='rgba(24,217,255,.32)';ctx.beginPath();ctx.moveTo(cx-scale*2.27,cy);ctx.lineTo(cx-scale*2.08,cy);ctx.moveTo(cx,cy+scale*1.58);ctx.lineTo(cx,cy+scale*1.76);ctx.stroke();
  }
  function render(){
    if(!width||!height)return;const scale=Math.min(width*.245,height*.265),cx=width*.51+tiltX*24,cy=height*.48+tiltY*16;fieldDraw(cx,cy,scale);
    gl.viewport(0,0,canvas.width,canvas.height);gl.clearColor(0,0,0,0);gl.clear(gl.COLOR_BUFFER_BIT|gl.DEPTH_BUFFER_BIT);
    const rot=rotation(.75+tiltY*.90+pitch,-.2+tiltX*1.18+yaw,-.32+time*.065+tiltX*.13);gl.enable(gl.BLEND);gl.blendFunc(gl.ONE,gl.ONE_MINUS_SRC_ALPHA);
    if(!meshMode){
      gl.disable(gl.DEPTH_TEST);bind(wire,rot,scale,cx,cy,1.055);gl.uniform1f(uniforms.get(wire).alpha,.14);gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER,buffers.ghost);gl.drawElements(gl.LINES,counts.ghost,gl.UNSIGNED_SHORT,0);
      gl.enable(gl.DEPTH_TEST);gl.depthFunc(gl.LEQUAL);bind(solid,rot,scale,cx,cy,1);gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER,buffers.triangles);gl.drawElements(gl.TRIANGLES,counts.triangles,gl.UNSIGNED_SHORT,0);
    }else{gl.disable(gl.DEPTH_TEST);bind(wire,rot,scale,cx,cy,1);gl.uniform1f(uniforms.get(wire).alpha,.48);gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER,buffers.wire);gl.drawElements(gl.LINES,counts.wire,gl.UNSIGNED_SHORT,0);}
    canvas.dataset.form=String(formIndex+1);canvas.dataset.mode=meshMode?'wireframe':'chrome';
  }
  function resize(){const bounds=canvas.getBoundingClientRect();width=bounds.width;height=bounds.height;dpr=Math.min(devicePixelRatio||1,2);canvas.width=Math.round(width*dpr);canvas.height=Math.round(height*dpr);field.width=canvas.width;field.height=canvas.height;ctx.setTransform(dpr,0,0,dpr,0,0);render();}
  function tick(now){frame=requestAnimationFrame(tick);const dt=last?Math.min((now-last)/1000,.05):0;last=now;if(!visible||document.hidden||!moving)return;time+=dt;const follow=1-Math.exp(-dt*8);tiltX+=(pointerX-tiltX)*follow;tiltY+=(pointerY-tiltY)*follow;render();}
  hero.addEventListener('pointermove',event=>{if(event.pointerType==='touch')return;const r=hero.getBoundingClientRect();pointerX=Math.max(-1,Math.min(1,((event.clientX-r.left)/r.width-.5)*2));pointerY=Math.max(-1,Math.min(1,((event.clientY-r.top)/r.height-.5)*2));if(dragging&&moving){yaw+=(event.clientX-lastX)*.008;pitch+=(event.clientY-lastY)*.006;lastX=event.clientX;lastY=event.clientY;}});
  hero.addEventListener('pointerleave',()=>{pointerX=pointerY=0;});
  canvas.addEventListener('pointerdown',event=>{if(event.pointerType!=='mouse'||!moving)return;dragging=true;lastX=event.clientX;lastY=event.clientY;canvas.setPointerCapture(event.pointerId);canvas.classList.add('dragging');});
  function release(){dragging=false;canvas.classList.remove('dragging');}
  canvas.addEventListener('pointerup',release);canvas.addEventListener('pointercancel',release);canvas.addEventListener('lostpointercapture',release);
  document.querySelector('#remix-form').addEventListener('click',()=>{formIndex=(formIndex+1)%forms.length;yaw=pitch=0;geometry();render();document.querySelector('#form-label').innerHTML=`FIG. 0${formIndex+1} — ${forms[formIndex].name}<br><b>IDEAS INTO MOTION</b>`;document.querySelector('#form-count').textContent=`0${formIndex+1} / 03`;});
  document.querySelector('#wire-toggle').addEventListener('click',event=>{meshMode=!meshMode;event.currentTarget.setAttribute('aria-pressed',String(meshMode));event.currentTarget.querySelector('.view-label').textContent=meshMode?'CHROME VIEW':'WIREFRAME';container.classList.toggle('is-wireframe',meshMode);render();});
  const observer=new IntersectionObserver(entries=>{visible=entries[0].isIntersecting;},{threshold:0});observer.observe(hero);const sizeObserver=new ResizeObserver(resize);sizeObserver.observe(canvas);
  canvas.addEventListener('webglcontextlost',event=>{event.preventDefault();cancelAnimationFrame(frame);});canvas.addEventListener('webglcontextrestored',()=>location.reload());
  document.querySelector('#form-label').innerHTML=`FIG. 01 — ${forms[0].name}<br><b>IDEAS INTO MOTION</b>`;
  geometry();resize();frame=requestAnimationFrame(tick);
  return{setMotion(value){moving=value;last=0;if(!moving)release();},destroy(){cancelAnimationFrame(frame);observer.disconnect();sizeObserver.disconnect();for(const b of Object.values(buffers))gl.deleteBuffer(b);gl.deleteProgram(solid);gl.deleteProgram(wire);field.remove();}};
}
