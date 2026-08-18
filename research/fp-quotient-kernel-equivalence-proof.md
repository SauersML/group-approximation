---
rg: 2
id: fp-quotient-kernel-equivalence-proof
kind: route
title: Adjoin the normal generators as relators, and read the converse off the formalized Tietze theorem
target: fp-quotient-iff-kernel-finitely-normally-generated
requires: []
artifacts:
  - GroupApproximation/Algebra/FinitePresentationKernel.lean
  - research/artifacts/boone-higman-audit-2026-08-17.md
---

**(<==)**  Write `Gamma = <X | R>` with `X` and `R` finite, and suppose
`N = <<n_1,…,n_k>>_Gamma`.  Choose words `u_i(X)` representing the `n_i`.
The group `<X | R, u_1,…,u_k>` is `Gamma` with the normal closure of the
`n_i` killed, which is `Gamma/N`, and the presentation is finite.

**(==>)**  Apply
`Algebra/FinitePresentationKernel.ker_isFinitelyNormallyGenerated` to the
quotient map `f : Gamma ->> Gamma/N`, whose source and target are both
finitely presented by hypothesis.  Its conclusion is that `f.ker = N` is
finitely normally generated.

## Status of the two halves

The forward half is machine-checked in this repository and needs nothing from
this region; it was formalized on 2026-08-16 for unrelated reasons and is
reused verbatim.  The reverse half is elementary and is not formalized —
there is no Lean statement here saying that adjoining relators presents the
quotient, and none is needed by any node, since every use in this region runs
in the direction the Lean theorem covers.

Anyone extending the region should note the asymmetry: a Lean-level statement
of the equivalence would require the (easy) reverse half as well, and that is
the one piece of `boone-higman-conjecture`'s pivot that this repository does
not yet own.
