---
rg: 2
id: wave2-audit-ghb7-cyclotomic-kazhdan-cover
kind: claim
title: GHB7 has a Kazhdan cover by a rank-six cyclotomic lattice with exact order-seven generator lifts
distinct_from:
  ghb7-finite-index-z-extension-center-survives: that asks for finite visibility of a central integral cover of a subgroup; this constructs an unconditional noncentral rank-six cover of GHB7 itself and leaves its finite visibility open.
  hrf-audit-stability-forces-prime-central-finite-residuals: that extracts central prime-kernel counterexamples from a stability assumption; this gives a specified cyclotomic-kernel cover and describes the two finite-visibility alternatives without asserting stability.
artifacts:
  - research/artifacts/hyperbolic-rf-wave2-audit-2026-09-20.md
---

Let `G=G_HB2(7)`, let `chi:G->C_7` send each of `a,b,c` to `1`, and put
`K=ker chi`. For every integral class `c in H^2(K;Z)` with nonzero rational
image there is an explicitly defined pullback-and-quotient extension

```
1 -> A -> E_c^cyc -> G -> 1,
A=Z^7/Z(1,1,1,1,1,1,1),
```

with these properties:

1. `G` acts on `A` through `chi`, by cyclically permuting coordinates.
2. `E_c^cyc` is finitely generated and has property (T).
3. Every lift of each of `a,b,c` has exact order seven.
4. If the integral central cover of `K` classified by `c` has central orders
   unbounded in finite quotients, then `E_c^cyc` supplies nonroundable
   asymptotic representations of `G` with exact seventh-power relators.
   Their remaining relators are mutually commuting block-scalar matrices;
   the generators cyclically permute seven blocks, so those relators need
   not commute with the generators.

The cover exists without any stability or residual-finiteness hypothesis.
One specified choice of `c` is the pullback of the integer cochain supported
on face zero of `K\Y`, with its seven faces labeled by `a^i K`. The artifact
checks that its rational image is nonzero via the Borel-to-orbit map.
The finite-visibility hypothesis in item 4 is still OPEN for the selected
class. The cover itself contains `Z^6` and is not the desired hyperbolic
counterexample. Complete construction and proof are in the artifact.

DERIVATION
wave2-audit-cyclotomic-kazhdan-cover-proof

The subsequent computation
[[wave3-canonical-k7-class-has-primitive-evaluation]] proves that the
specified face-zero choice evaluates onto Z integrally, not merely
nontrivially over Q. Its central generator belongs to the commutator
subgroup. This sharpens the construction's input but does not establish
the finite-visibility hypothesis in item 4.
