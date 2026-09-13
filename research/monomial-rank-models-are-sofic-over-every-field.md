---
rg: 2
id: monomial-rank-models-are-sofic-over-every-field
kind: claim
title: Over every field, monomial linear sofic approximations yield sofic approximations with the same separation
distinct_from:
  monomial-rank-models-are-hamming-models: that compares rank with Hamming distance when labels lie in the finite group F^x, so the regular label action is already a finite model; this treats arbitrary fields, including C, where labels form an infinite group, and removes the phases by a character and torsion rounding.
  block-monomial-hs-models-sofic-mod-amenable-soft-kernel: that is the Hilbert--Schmidt statement, where phases can separate an abelian normal subgroup; in the rank metric phase agreement is exact on columns and phases never obstruct.
  signed-monomial-tracial-images-are-sofic: that is the HS criterion for +-1 labels; this is the rank-metric criterion for arbitrary nonzero labels over any field.
artifacts:
  - research/artifacts/ex-q34-monomial-phases-2026-09-12.md
---

**ESTABLISHED.**  Let `K` be any field and `G` countable.  Suppose every finite
window of `G` has maps `phi : E -> GL_N(K)` that are asymptotically
multiplicative in normalized rank and separate elements by a fixed
`delta > 0`, and whose values lie within `o(N)` rank of the monomial matrices
`Mon_N(K)`.  Then `G` is sofic, with window separation `>= delta - o(1)`.

Proof outline (complete in the artifact):

1. **Rank is column-Hamming on monomials.**  For `A, B in Mon_N(K)`,
   `|Q|/2 <= rank(A - B) <= |Q|`, with `Q` the set of columns where
   `A e_i != B e_i`.  So relators hold *exactly*, phase included, on most
   columns, and test words move most columns in the separation set.
2. **Circle.**  The finitely many labels generate `Λ ≅ Z^a × Z/q` in `K^x`.  A
   generic character `psi : Λ -> U(1)`, faithful on the torsion, keeps every
   exact relator holonomy `1` and every relevant nontrivial holonomy `!= 1`.
3. **Torsion rounding.**  The exact relator constraints cut out a closed
   subgroup of a torus.  Its torsion points are dense, and the finitely many
   conditions `!= 1` are open.  So the phases can be taken in `mu_m`.
4. **Skew product.**  Acting on `[N] × Z/m` by `(x, j) |-> (sigma(x), j + a(x))`
   gives an exact finite almost-action.  Relators fail only on bad columns, and
   fixed points of test words lie over columns fixed by the monomial model.

Consequences.  A nonsofic group has no monomial rank model over any field.
Every permutation-type or phase-type monomial construction toward linear
soficity of the binary Leavitt units, over `F_2`, `F_3`, `C` or any other
field, reduces to soficity and is excluded by `openai-leavitt-unit-nonsofic`.
The Hilbert--Schmidt analogue is open and is recorded as
`monomially-hyperlinear-groups-are-sofic`.  What fails there is exactly step
1, because HS sees only the size of a phase disagreement.

## Attempts

Established; see `monomial-rank-models-are-sofic-over-every-field-proof`.
