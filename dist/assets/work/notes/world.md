# A world that keeps going.

FIELD NOTES / 001 — PROCEDURAL WORLDS

Sundrift’s environment starts with one shared description of the ground. The road, scenery, and camera all query that same surface, so a change to the terrain doesn’t leave props floating above it.

## One world, built in pieces.

The mountain road grows as a sequence of switchbacks and bends. Each new piece is checked against the road already placed. If a candidate gets stuck, the generator backs up and tries again. Terrain chunks and repeated props are then added around that route.

The city reuses the road generator differently: long sections become avenues, switchbacks wrap around blocks, and connecting bends become cross streets. A common structure produces two very different places.

## The engineering idea.

Shared rules make a large system easier to keep consistent. A believable world is as much about how its parts agree as about the detail in any individual object.

Source: https://github.com/lkruer/sundrift#how-the-world-is-made

An editorial summary of the public Sundrift development record.
