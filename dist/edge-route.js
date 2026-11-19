const wideScreen = matchMedia('(min-width: 921px)');

function outline(segments, width) {
  const near = [], far = [];
  for (const [segment, [start, control1, control2, end]] of segments.entries()) {
    for (let step = segment === 0 ? 0 : 1; step <= 28; step += 1) {
      const t = step / 28, u = 1 - t;
      const point = axis => u ** 3 * start[axis] + 3 * u * u * t * control1[axis]
        + 3 * u * t * t * control2[axis] + t ** 3 * end[axis];
      const slope = axis => u * u * (control1[axis] - start[axis])
        + 2 * u * t * (control2[axis] - control1[axis]) + t * t * (end[axis] - control2[axis]);
      const x = point(0), y = point(1), dx = slope(0), dy = slope(1);
      const sectionProgress = (segment + t) / segments.length;
      const radius = width * (.5 + .12 * Math.sin(Math.PI * sectionProgress)) / Math.hypot(dx, dy);
      near.push([x - dy * radius, y + dx * radius]);
      far.push([x + dy * radius, y - dx * radius]);
    }
  }

  const coords = [...near, ...far.reverse()].map(pair => pair.map(value => value.toFixed(2)).join(' '));
  return 'path("M' + coords.join('L') + 'Z")';
}

export function fitEdgeRoute(section, box, feature) {
  if (!wideScreen.matches || !CSS.supports('clip-path', 'path("M0 0L1 1L0 1Z")')) return;
  const top = feature.top - box.top - section.clientTop + 1;
  const bottom = feature.bottom - box.top - section.clientTop + 1;
  const right = feature.right - box.left;
  const height = section.clientHeight + 1;
  const reach = Math.min(62, Math.max(37, box.width * .04));
  const game = section.id === 'games';

  for (const [pseudo, property, lane] of [
    ['::before', '--route-lead', 0],
    ['::after', '--route-follow', 1],
  ]) {
    // The CSS origin is shared with the adjacent sections, keeping their endpoints aligned.
    const style = getComputedStyle(section, pseudo);
    const width = Number.parseFloat(style.getPropertyValue('--thread-width'));
    const start = Number.parseFloat(style.transformOrigin) + width / 2;
    const side = right + 17 + lane * 12;
    const upper = [right - reach + lane * 15, top - 51 - lane * 10];
    const lower = [right + (game ? -23 : 10) + lane * 10, Math.min(height - 29, bottom + (game ? 30 : 17) + lane * 9)];
    const sideTop = top + 34, sideBottom = bottom - 28;
    const segments = [
      [[start, 0], [start, upper[1] * .39], [upper[0] - 16, upper[1] - 24], upper],
      [upper, [upper[0] + 20, upper[1] + 30], [side, top - 24], [side, sideTop]],
      [[side, sideTop], [side, sideTop + (sideBottom - sideTop) * .33],
        [side + 2, sideBottom - (sideBottom - sideTop) * .33], [side + 2, sideBottom]],
      [[side + 2, sideBottom], [side + 2, bottom + 13], [lower[0] + 5, lower[1] - 13], lower],
      [lower, [lower[0] - 5, lower[1] + 13], [start, height - 15], [start, height]],
    ];
    section.style.setProperty(property, outline(segments, width));
  }

  section.setAttribute('data-edge-route', '');
}
