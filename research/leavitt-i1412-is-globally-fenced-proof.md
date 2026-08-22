---
rg: 2
id: leavitt-i1412-is-globally-fenced-proof
kind: route
title: Exhaust both carriers and every cyclic one-copy boundary
target: leavitt-i1412-is-globally-fenced
requires:
  - leavitt-i1412-carrier-screens-exhaustive
  - leavitt-i1412-transformed-eq1-screens-exhaustive
  - leavitt-d4-l14-i1412-paired-minimum-block-screen-is-fenced
---

The exact all-maximal carrier census proves that the earlier minimum-block
lists already contain every coarsening-maximal cancellation of Eq3 and Eq1.
After every Eq3 coordinate substitution, a separate all-maximal audit proves
the transformed Eq1 minimum screen remains exhaustive: all 223 transformed
inputs have 395 minimum schemes and exactly 395 maximal schemes.  Their
coordinate-preserving intersection therefore gives all 43 simultaneous
carrier states.

For each state, cyclically rotate the freely reduced boundary through every
syllable cut, normalize any endpoint cascade, append a formal `q^-1` in each
of the four target copies, and enumerate every coarsening-maximal noncrossing
forest.  This is equivalent to asking whether the boundary is conjugate into
one coefficient factor.  Independent audit confirms the raw 63-syllable
boundary, factor order, cyclic cuts, formal-target orientation, and retained
generator images.

MSI job `16680283` returned

```text
boundary_schemes_by_target={0:76,1:70,2:70,3:73}
boundary_states=195
nontrivial_q_images=18
free_nontrivial_q_images=0
cyclic_relator_killed_q_images=14
power_relator_killed_q_images=4
unresolved_q_images=0
```

The last four images are conjugates of `x6^6`; each residual presentation
contains `x6^2` and `x6^3`, so `x6=1`.  Therefore every formal target is
trivial, exhaustively fencing the class.
