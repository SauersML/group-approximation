---
rg: 2
id: pattern-energy-token-corners-prove-surjectivity
kind: route
title: Detect finite support from charged patterns and fill energy levels with collision corners
target: finite-injective-pattern-energy-forces-surjectivity
requires:
  - relative-equality-piecewise-injections-are-surjective
artifacts:
  - research/artifacts/pattern-energy-collision-proof-2026-09-08.md
---

The attached proof derives a finite-radius cover of the support by
charged pattern centers from compactness and the unique zero-energy
configuration. Decorate each center with a finite input neighborhood;
these decorations make its token encoding injective even though the
energy density can vanish on nonvacuum patterns.

Replace the finitely many positive real pattern weights by positive
integer weights preserving all exact integer relations. Fill the
locally finite real energy levels by induction. Once all smaller
levels are attained, injectivity forbids a drop from the next level,
so conservation holds up through that level.

At a fixed level, support size is bounded. Choose one neighborhood
large enough that both the input energy patterns and output decorated
energy patterns see at most one component. Energy and token sets then
decompose over finite interacting components. On each component the
input and output token sets have equal cardinality. Its finite
translation stabilizer acts freely on both, so an equivariant token
bijection exists. There are only finitely many component types at
this level, giving finitely many coordinate displacement instructions.

The proof explicitly verifies that ordered token validity and the
resulting map are finite Boolean relative-equality programs. The map
is injective because the token encoding determines the output
configuration, finite injectivity determines the input, and the chosen
token matching determines the ordering. The required claim makes the
map onto. This fills the current energy sector and completes the
induction. Finite configurations are dense and the CA image is closed,
which gives full-shift surjectivity.

No Hall inequality for energy under truncation is assumed. Such an
inequality is unavailable for overlapping pattern energies. The proof
only uses equal-size free finite stabilizer sets and the bounded
component types at one fixed energy level.
