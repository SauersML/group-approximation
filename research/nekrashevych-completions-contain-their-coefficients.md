---
rg: 2
id: nekrashevych-completions-contain-their-coefficients
kind: claim
title: The Leavitt completion of a finitely presented algebra along an injective unital recursion is finitely presented and contains the algebra
distinct_from:
  self-similar-hosts-contain-only-residually-finite-groups: that shows a group acting self-similarly on a rooted tree is residually finite, so self-similar group hosts miss every infinite simple input; this embeds an arbitrary algebra in its completion along any injective algebra recursion, with no residual finiteness constraint.
  full-group-units-embed-in-steinberg-algebras: that embeds topological full groups into the units of a Steinberg algebra; this embeds a whole coefficient algebra into a Cuntz--Pimsner type completion, and the unit group of the coefficients comes along.
artifacts:
  - research/artifacts/bh-steinberg-hosts-2026-09-12.md
---

**ESTABLISHED.** Let `K` be a field, `d >= 2`, `B` a unital `K`-algebra, and
`psi : B -> M_d(B)` a unital homomorphism. Put

```text
O_psi = ( B * L_K(1,d) ) / ( b = Σ_(i,j) s_i psi(b)_(ij) s_j*  for b in B ).
```

1. If `B` is finitely presented, so is `O_psi`: the relation needs imposing only
   on the generators of `B`.
2. If `psi` is injective, the canonical map `B -> O_psi` is injective.
3. Put `B_n = M_(d^n)(B)`, with transition maps given by applying `psi`
   entrywise, and `B_inf = lim B_n`. If `psi` is injective, `B_inf` embeds in
   `O_psi` as the degree-zero part of the gauge grading, and that grading is
   strong.

In particular `B^x <= O_psi^x`, and every group in the units of `B` sits in the
units of a finitely presented completion.

## Role on the Boone--Higman algebra route

- **A candidate host family.** The premise
  `simple-inputs-have-fp-elementary-leavitt-tensor-hosts` needs a finitely
  presented central simple algebra containing `S` in its units. Completions
  supply finitely presented overalgebras of any finitely presented `B` with
  `S <= B^x` (for instance `B = K[P]` for a Higman overgroup `P` of `S`).
- **What is missing is simplicity.** It is constrained by
  `saturated-invariant-ideals-block-completion-simplicity` and, for monomial
  recursions, killed on the coefficients by
  `simple-monomial-completions-kill-the-tree-action-kernel`.
- **Examples.**
  - `psi(b) = b I_d` gives `B ⊗ L_d`.
  - A wreath recursion of a group `P` gives the Nekrashevych algebra of `P`.

## Trust

- The proof is self-contained. It builds a skew Laurent model over the direct
  limit of the corner map `B_inf -> E_(11) B_inf E_(11)`.
- The construction is the corner skew Laurent ring of Ara--González-Barroso--
  Goodearl--Pardo (arXiv:math/0307320), a case of the algebraic Cuntz--Pimsner
  rings of Carlsen--Ortega (arXiv:0810.3254). The embedding statement is not
  quoted from either source.
- Not reviewed, and not in Lean.

DERIVATION
nekrashevych-completions-contain-their-coefficients-proof
