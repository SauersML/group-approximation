---
rg: 2
id: fournier-facio-tracial-median-size-matching
kind: route
title: Transfer OpenAI's median size-matching step to regular tracial models through invariant mass
target: fournier-facio-has-no-purely-singular-free-near-representation
requires: []
---

**Dead.**  The proposed argument follows OpenAI Proposition 2.3 in a regular
tracial model `u:G -> U(M)` of the Fournier--Facio group.

1. Take the invariant mass `F(x) = ||E_A(x)||_2^2`, with
   `A = u(Gamma)' cap M`, as the size function.
2. Show it is almost conserved along both compressors.
3. Use property (T) of `G` as a Poincare inequality to force size matching
   between transported and original sectors.
4. Conclude that `J` acts inside one frame piece, and contradict simplicity
   of `S` by a centralizer rigidity.

Invalidated by `fournier-facio-invariant-mass-grows-along-compressor`.  `F` is
monotone along `Ad u(t_1)^*`, but it jumps from `0` to `1` on every unitary
`u(g)` with `g in pi(S)\{1}`.  So step 2 fails by unit amounts on the
elements that matter.  The permutation proof conserves mass because it sums
the component-size function over points.  A viable replacement must supply a
frame, a finite-level trace-scale object, that is almost monotone and almost
conserved.  The charged-basis fences already forbid taking that frame from a
normalized basis.  `transported-gap-masa-kills-leavitt-hs-models` (part A)
shows that a maximal abelian frame of `A` carried back into `A` by the
compressor already kills `[J,J]`.  So in a faithful model every such frame
leaves the `Gamma`-commutant, and the frame a size-matching step needs cannot
be a masa of `A`.
