export function collatzSequence(seed, maxSteps = 3000) {
  if (!Number.isInteger(seed) || seed < 1 || seed > 999999) throw new RangeError('Choose a whole number from 1 to 999,999.');
  const values = [BigInt(seed)];
  while (values.at(-1) !== 1n && values.length <= maxSteps) {
    const n = values.at(-1);
    values.push(n % 2n === 0n ? n / 2n : 3n * n + 1n);
  }
  return values;
}

export function initMath() {
  const canvas = document.querySelector('#collatz-canvas');
  const ctx = canvas.getContext('2d');
  const input = document.querySelector('#collatz-seed');
  const error = document.querySelector('#collatz-error');
  const label = document.querySelector('#sequence-label');
  let values = collatzSequence(27), seed = 27, hover = -1, width = 500, height = 225;
  function plot() {
    const bounds = canvas.getBoundingClientRect(), dpr = Math.min(window.devicePixelRatio || 1, 2);
    width = bounds.width; height = bounds.height;
    if (!width || !height) return;
    canvas.width = Math.round(width * dpr); canvas.height = Math.round(height * dpr);
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0); ctx.clearRect(0, 0, width, height);
    const left = 45, top = 14, right = width - 14, bottom = height - 25;
    const peak = Math.max(...values.map(Number));
    const logMax = Math.max(Math.log10(peak), 1) * 1.05;
    const x = i => left + i / Math.max(1, values.length - 1) * (right - left);
    const y = v => bottom - Math.log10(Number(v)) / logMax * (bottom - top);
    ctx.font = '11px "IBM Plex Mono", monospace'; ctx.textBaseline = 'middle';
    for (let power = 0; power <= Math.ceil(logMax); power++) {
      const value = Math.pow(10, power), yy = y(value);
      if (yy < top - 1) continue;
      ctx.strokeStyle = 'rgba(42,161,225,.14)'; ctx.lineWidth = 1;
      ctx.beginPath(); ctx.moveTo(left, yy); ctx.lineTo(right, yy); ctx.stroke();
      ctx.fillStyle = '#a1bdd1'; ctx.textAlign = 'right';
      const tick = value >= 1000000 ? value / 1000000 + 'm' : value >= 1000 ? value / 1000 + 'k' : String(value);
      ctx.fillText(tick, left - 9, yy);
    }
    const points = values.map((v, i) => [x(i), y(v)]);
    const area = ctx.createLinearGradient(0, top, 0, bottom);
    area.addColorStop(0, 'rgba(29,221,255,.20)'); area.addColorStop(1, 'rgba(29,221,255,0)');
    ctx.beginPath(); ctx.moveTo(left, bottom); for (const p of points) ctx.lineTo(...p);
    ctx.lineTo(points.at(-1)[0], bottom); ctx.closePath(); ctx.fillStyle = area; ctx.fill();
    ctx.beginPath(); points.forEach((p, i) => i ? ctx.lineTo(...p) : ctx.moveTo(...p));
    ctx.strokeStyle = '#28e4ff'; ctx.lineWidth = 1.7; ctx.lineJoin = 'round'; ctx.stroke();
    ctx.fillStyle = '#28e4ff'; ctx.beginPath(); ctx.arc(...points.at(-1), 3, 0, Math.PI * 2); ctx.fill();
    ctx.fillStyle = '#a1bdd1'; ctx.textAlign = 'left'; ctx.fillText('0', left, height - 8);
    ctx.textAlign = 'right'; ctx.fillText((values.length - 1) + ' steps', right, height - 8);
    if (hover >= 0) {
      const point = points[hover]; ctx.strokeStyle = '#28e4ff80'; ctx.setLineDash([3, 4]);
      ctx.beginPath(); ctx.moveTo(point[0], top); ctx.lineTo(point[0], bottom); ctx.stroke(); ctx.setLineDash([]);
      ctx.fillStyle = '#fff0ff'; ctx.beginPath(); ctx.arc(...point, 4, 0, Math.PI * 2); ctx.fill();
      label.textContent = 'STEP ' + hover + ' · n = ' + values[hover].toLocaleString();
    }
  }
  function update(n) {
    try {
      const next = collatzSequence(n); seed = n; values = next; hover = -1; error.textContent = '';
      const peak = next.reduce((a, b) => a > b ? a : b), completed = next.at(-1) === 1n;
      document.querySelector('#step-stat').textContent = String(next.length - 1);
      document.querySelector('#peak-stat').textContent = peak.toLocaleString();
      document.querySelector('#end-stat').textContent = completed ? '1' : '…';
      if (!completed) error.textContent = 'Stopped at 3,000 steps. This limit does not imply divergence.';
      label.textContent = 'n₀ = ' + n.toLocaleString();
      canvas.setAttribute('aria-label', `Collatz sequence starting at ${n}: ${next.length - 1} steps, peaking at ${peak}, ${completed ? 'then reaching 1' : 'stopped at the step limit'}.`);
      document.querySelectorAll('[data-seed]').forEach(button => { const selected = Number(button.dataset.seed) === n; button.classList.toggle('selected', selected); button.setAttribute('aria-pressed', String(selected)); });
      plot();
    } catch (e) { error.textContent = e.message; }
  }
  document.querySelector('#collatz-form').addEventListener('submit', event => { event.preventDefault(); update(input.valueAsNumber); });
  document.querySelectorAll('[data-seed]').forEach(button => button.addEventListener('click', () => { input.value = button.dataset.seed; update(Number(button.dataset.seed)); }));
  canvas.addEventListener('pointermove', event => { const x = event.clientX - canvas.getBoundingClientRect().left; hover = Math.max(0, Math.min(values.length - 1, Math.round((x - 45) / (width - 59) * (values.length - 1)))); plot(); });
  canvas.addEventListener('pointerleave', () => { hover = -1; label.textContent = 'n₀ = ' + seed.toLocaleString(); plot(); });
  new ResizeObserver(plot).observe(canvas); update(27);
  document.fonts.ready.then(plot);
}
