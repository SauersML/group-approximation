---
rg: 2
id: linton-halo-conclusion-fails-at-shallow-derived-stages
kind: claim
title: Sofic one-relator groups whose Linton shell has no set-halo presentation at any stage up to a prescribed depth, but has one beyond it
distinct_from:
  linton-radical-has-equivariant-sofic-halo: that asserts a sofic halo presentation of "the" finite rational-derived shell; this shows the assertion is false at the least valid stage and at stages up to any prescribed depth, and true beyond that depth, for explicit sofic groups.
  permuted-free-product-linton-radical-gives-sofic-shell: that builds the halo once the shell permutes the free factors freely; this exhibits radicals of that shape whose shallower shells, where the permutation has a contracting stabilizer, have no halo presentation at all.
  berlai-perfect-linton-radicals-are-sofic: that proves soficity for an explicit family through residue-class chains; the groups here are already sofic, and the content is which stages admit a halo presentation.
  one-relator-soficity-localizes-at-rational-derived-stage: that produces a valid shell at some stage and shows soficity of the group is independent of the stage; this shows that the existence of a halo presentation does depend on the stage.
  linton-shell-sofic: that asks whether every Linton shell is sofic; every shell here is sofic, including those with no halo presentation.
artifacts:
  - research/artifacts/linton-halo-contraction-obstruction-2026-09-16.md
---

ESTABLISHED.  Convention: `[g,h] = g h g^-1 h^-1`.  A stage `n` is valid when
`G_Q^(n)/R` is free, where `R = G_Q^(omega)`, and then
`E_n = G_Q^(n) = R semidirect F0`.

**The stage-zero example.**  Let

    G0 = < a, s | s a s^-1 = [a, s^-1 a s] > .

- `G0` is the ascending HNN extension of `B = F(x,y)` along the injective,
  non-surjective endomorphism `x -> y`, `y -> [y,x]`, with `x = s^-1 a s` and
  `y = a`.
- Its Linton radical `R = <<a>>` is nontrivial, perfect and locally free, and
  `G0/R = Z`.
- Every stage is valid.
- At stage `0` (`F0 = Z`) the shell `G0` has no halo presentation, for any
  complement, sofic or not.
- At every stage `n >= 1` (`F0 = 1`) the conclusion of
  [[linton-radical-has-equivariant-sofic-halo]] holds.
- `G0` is sofic.

**A family failing up to depth `d`.**  Fix `d >= 0` and
`u in F(p,q)^(d) \ F(p,q)^(d+1)`, and let

    G_u = < a, p, q | u a u^-1 = [a, u^-1 a u] >  =  G0 *_(s = u) F(p,q) .

- The radical `R = <<a>>` is the internal free product of the conjugates
  `g R0 g^-1`, `gC` in `F/<u>`, with `R0 = ker(G0 -> Z)`.  It is perfect and
  locally free.
- `G_u/R = F(p,q)`, so every stage is valid.
- For `n <= d`, the shell `G_Q^(n)` has no halo presentation, for any
  complement.
- For `n >= d+1`, the shell `G_Q^(n)` with complement `F^(n)` has a halo
  presentation with sofic finite pieces.
- `G_u` is sofic.

Examples: `u = p` gives `G0 * Z`, failing only at stage 0.  `u = [p,q]` gives
a relator of length 29, failing at stages 0 and 1.

**Consequences for the target.**

- If "the finite rational-derived shell" means the least valid stage, or every
  valid stage, then [[linton-radical-has-equivariant-sofic-halo]] is false.
- Under the existential reading (some valid stage), these examples do not
  refute it.
- The least stage at which a halo presentation exists is not bounded by a
  universal constant.
- All the groups are sofic, so this is an obstruction to one method, not
  evidence against soficity.
- Soficity of `G` does not depend on the valid stage.  So the downstream
  routes of the target lose nothing if the shell is taken deeper.

Open: is there a one-relator group whose shell at *every* valid stage violates
[[halo-shell-invariant-conjugations-are-virtually-inner]] for some finitely
generated subgroup of `R`?
