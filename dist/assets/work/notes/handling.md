# Finding the feel of a drift.

FIELD NOTES / 002 — INPUT & PHYSICS

A driving game has to respond predictably while still feeling playful. Sundrift’s development record follows that balance through changes to steering, traction, counter-steering, and the way a slide holds its angle.

## The input has to mean something.

In the current design, holding a turn maintains the slide. Throttle changes its depth; opposite steering closes the angle; the handbrake throws it wider. The assistance is intended to support those inputs without taking control away from the player.

The repository includes simulations for drift behavior, reversing, and J-turns, alongside browser checks using real keyboard and touch input. The model is tested both by its numbers and by what happens in play.

## The engineering idea.

A simulation’s usefulness depends on the experience it is meant to produce. Clear input, understandable feedback, and deliberate compromises matter alongside the equations.

Source: https://github.com/lkruer/sundrift#controls

An editorial summary of the public Sundrift development record.
