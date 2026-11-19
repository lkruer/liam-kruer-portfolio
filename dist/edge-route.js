const wideScreen = matchMedia('(min-width: 921px)');

function outline(segments, width) {
  const near = [], far = [];
  for (const [segment, [start, control1, control2, end]] of segments.entries()) {
    for (let step = segment === 0 ? 0 : 1; step <= 36; step += 1) {
      const t = step / 36, u = 1 - t;
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

function crossingSweep(start, end, sag) {
  const distance = end[0] - start[0];
  const middle = [start[0] + distance * .52, (start[1] + end[1]) / 2 + sag];
  return [
    [start, [start[0] + distance * .17, start[1]], [middle[0] - distance * .16, middle[1]], middle],
    [middle, [middle[0] + distance * .16, middle[1]], [end[0] - distance * .17, end[1]], end],
  ];
}

function researchRoute(left, right, top, height, start, finish, inset, lane) {
  const bend = Math.min(92, (right - left) * .12);
  const crossStart = [right - bend, top - 39 + lane * 11];
  const crossEnd = [left + bend, crossStart[1] + 5];
  const side = [left - inset, top + 64];

  return [
    [[start, 0], [start, crossStart[1] * .48], [start, crossStart[1]], crossStart],
    ...crossingSweep(crossStart, crossEnd, 11),
    [crossEnd, [side[0], crossEnd[1]], [side[0], top - 7], side],
    [side, [side[0], side[1] + (height - side[1]) * .54], [finish, height * .89], [finish, height]],
  ];
}

function sundriftRoute(left, right, top, bottom, height, start, finish, inset, lane) {
  const bend = Math.min(98, (right - left) * .12);
  const side = [left - inset, top + 53];
  const sideEnd = [side[0], bottom - 78];
  const crossStart = [left + bend, bottom + (height - bottom) * .48 - lane * 11];
  const crossEnd = [right - bend, crossStart[1] + 7];

  return [
    [[start, 0], [start, top * .42], [side[0], top - 36], side],
    [side, [side[0], side[1] + (sideEnd[1] - side[1]) * .33],
      [sideEnd[0], sideEnd[1] - (sideEnd[1] - side[1]) * .33], sideEnd],
    [sideEnd, [sideEnd[0], bottom + 6], [sideEnd[0], crossStart[1]], crossStart],
    ...crossingSweep(crossStart, crossEnd, 15),
    [crossEnd, [finish, crossEnd[1]], [finish, height - 14], [finish, height]],
  ];
}

export function fitEdgeRoute(section, box, feature) {
  if (!wideScreen.matches || !CSS.supports('clip-path', 'path("M0 0L1 1L0 1Z")')) return;
  const top = feature.top - box.top - section.clientTop + 1;
  const bottom = feature.bottom - box.top - section.clientTop + 1;
  const left = feature.left - box.left;
  const right = feature.right - box.left;
  const height = section.clientHeight + 1;
  const game = section.id === 'games';

  // Measure the CSS right-hand seams used by Engineering and Videos, then reflect the pair.
  const ribbons = ['::before', '::after'].map(pseudo => {
    const style = getComputedStyle(section, pseudo);
    const width = Number.parseFloat(style.getPropertyValue('--thread-width'));
    const center = Number.parseFloat(style.transformOrigin) + width / 2;
    return { width, center };
  });

  ribbons.forEach(({ width, center }, lane) => {
    const leftSeam = box.width - ribbons[1 - lane].center;
    const inset = 27 - lane * 13;
    const segments = game
      ? sundriftRoute(left, right, top, bottom, height, leftSeam, center, inset, lane)
      : researchRoute(left, right, top, height, center, leftSeam, inset, lane);
    section.style.setProperty(lane === 0 ? '--route-lead' : '--route-follow', outline(segments, width));
  });

  section.setAttribute('data-edge-route', '');
}
