// Add future released games here. The shelf and count update automatically.
// Use a dedicated project page or public play URL for each game's playUrl.
export const games = [
  {id:'sundrift',title:'SUNDRIFT',subtitle:'Night driving, until the sun comes up.',year:'2026',platform:'BROWSER',playUrl:'games/sundrift/index.html',sourceUrl:'https://github.com/lkruer/sundrift',download:'assets/work/sundrift-source.zip'}
];

// Editorial summaries of the public Sundrift README and NOTES, not invented diary entries.
export const articles = {
  world:{title:'A world that keeps going.',category:'FIELD NOTES / 001 — PROCEDURAL WORLDS',body:[
    ['p','Sundrift’s environment starts with one shared description of the ground. The road, scenery, and camera all query that same surface, so a change to the terrain doesn’t leave props floating above it.'],
    ['h3','One world, built in pieces.'],
    ['p','The mountain road grows as a sequence of switchbacks and bends. Each new piece is checked against the road already placed. If a candidate gets stuck, the generator backs up and tries again. Terrain chunks and repeated props are then added around that route.'],
    ['p','The city reuses the road generator differently: long sections become avenues, switchbacks wrap around blocks, and connecting bends become cross streets. A common structure produces two very different places.'],
    ['h3','The engineering idea.'],
    ['p','Shared rules make a large system easier to keep consistent. A believable world is as much about how its parts agree as about the detail in any individual object.']
  ],url:'https://github.com/lkruer/sundrift#how-the-world-is-made'},
  handling:{title:'Finding the feel of a drift.',category:'FIELD NOTES / 002 — INPUT & PHYSICS',body:[
    ['p','A driving game has to respond predictably while still feeling playful. Sundrift’s development record follows that balance through changes to steering, traction, counter-steering, and the way a slide holds its angle.'],
    ['h3','The input has to mean something.'],
    ['p','In the current design, holding a turn maintains the slide. Throttle changes its depth; opposite steering closes the angle; the handbrake throws it wider. The assistance is intended to support those inputs without taking control away from the player.'],
    ['p','The repository includes simulations for drift behavior, reversing, and J-turns, alongside browser checks using real keyboard and touch input. The model is tested both by its numbers and by what happens in play.'],
    ['h3','The engineering idea.'],
    ['p','A simulation’s usefulness depends on the experience it is meant to produce. Clear input, understandable feedback, and deliberate compromises matter alongside the equations.']
  ],url:'https://github.com/lkruer/sundrift#controls'},
  iteration:{title:'Making iteration visible.',category:'FIELD NOTES / 003 — BUILD, MEASURE, REFINE',body:[
    ['p','Sundrift’s public development notes record the requests, measurements, changes, and rejected ideas behind the game. The README also documents the use of AI-assisted coding and independent asset candidates.'],
    ['h3','Keep the decisions, too.'],
    ['p','The record includes abandoned steering aids, revisions to the retro display, changes to the opening time of day, and checks on both desktop and phone. It preserves why a choice changed, rather than only the final implementation.'],
    ['p','Tests cover terrain placement, frame timing, input, scoring, and the complete run from start to sunrise. Those checks turn a visual experiment into something that can be revisited and improved with evidence.'],
    ['h3','The engineering idea.'],
    ['p','Documenting a failed approach can be as useful as documenting a successful one. A good build log keeps the reasoning available to the next iteration.']
  ],url:'https://github.com/lkruer/sundrift/blob/main/NOTES.md'}
};
