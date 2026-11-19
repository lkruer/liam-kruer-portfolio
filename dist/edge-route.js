const svgNamespace = 'http://www.w3.org/2000/svg';
const desktop = matchMedia('(min-width: 921px)');

// A parallel line meets at the intersection of the adjoining offset segments.
// Keeping the offset perpendicular also keeps the gap even across 45° corners.
function parallel(points, gap) {
  const normals = points.slice(1).map(([x, y], i) => {
    const dx = x - points[i][0], dy = y - points[i][1];
    const length = Math.hypot(dx, dy);
    return [dy / length, -dx / length];
  });
  return points.map(([x, y], i) => {
    const a = normals[Math.max(0, i - 1)];
    const b = normals[Math.min(i, normals.length - 1)];
    const scale = gap / (1 + a[0] * b[0] + a[1] * b[1]);
    return [x + (a[0] + b[0]) * scale, y + (a[1] + b[1]) * scale];
  });
}

function crossover(start, end, height, level, fold) {
  const direction = Math.sign(end - start);
  const elbow = 22, step = 12;
  return [
    [start, 0], [start, level - elbow], [start + direction * elbow, level],
    [fold, level], [fold + direction * step, level + step],
    [end - direction * elbow, level + step], [end, level + step + elbow], [end, height],
  ];
}

function entrance(start, end, height, level) {
  const reach = end - start, direction = Math.sign(reach);
  const bevel = Math.min(16, Math.abs(reach) / 3);
  return [[start, 0], [start, level - bevel], [start + direction * bevel, level],
    [end - direction * bevel, level], [end, level + bevel], [end, height]];
}

export function initSectionRails() {
  if (!('ResizeObserver' in window)) return;
  const hero = document.querySelector('.hero-art');
  const primaryTrace = document.querySelector('.hero-traces');
  const sections = [...document.querySelectorAll('.thread-section')];
  const layers = sections.map(section => {
    const svg = document.createElementNS(svgNamespace, 'svg');
    svg.classList.add('section-rail');
    svg.setAttribute('aria-hidden', 'true');
    svg.setAttribute('focusable', 'false');
    const lines = Array.from({ length: 2 }, () => svg.appendChild(document.createElementNS(svgNamespace, 'polyline')));
    section.prepend(svg);
    return lines;
  });

  function update() {
    const heroBox = hero.getBoundingClientRect();
    const origin = ['::before', '::after'].map(pseudo => {
      const style = getComputedStyle(primaryTrace, pseudo);
      return heroBox.left + heroBox.width * Number(style.getPropertyValue('--trace')) +
        parseFloat(style.getPropertyValue('--trace-width')) / 2;
    });
    const wide = desktop.matches;
    sections.forEach((section, i) => {
      const wrap = section.querySelector('.wrap').getBoundingClientRect();
      const height = section.clientHeight + section.clientTop;
      const width = section.clientWidth;
      const margin = (width - wrap.width) / 2;
      const outside = Math.min(margin * .53, 32);
      const right = wrap.right + outside;
      const gap = 7;
      let route = [[right, 0], [right, height]];
      let companion;
      if (section.id === 'engineering') {
        route = entrance(origin[0], right, height, wide ? 40 : 24);
        companion = entrance(origin[1], right + gap, height, 26);
      } else if (wide && section.classList.contains('edge-route')) {
        const left = wrap.left - outside - gap;
        const fold = wrap.left + wrap.width * .62;
        route = section.id === 'math' ? crossover(right, left, height, 32, fold)
          : crossover(left, right, height, height - 62, fold);
      }
      [route, companion ?? parallel(route, gap)].forEach((points, lane) => {
        layers[i][lane].setAttribute('points', points.map(([x, y]) => x.toFixed(2) + ',' + y.toFixed(2)).join(' '));
      });
    });
  }

  const observer = new ResizeObserver(update);
  for (const section of sections) observer.observe(section);
  observer.observe(hero);
  desktop.addEventListener('change', update);
  update();
}
