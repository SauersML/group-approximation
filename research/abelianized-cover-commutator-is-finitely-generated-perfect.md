---
rg: 2
id: abelianized-cover-commutator-is-finitely-generated-perfect
kind: claim
title: The commutator subgroup of the abelianized relation cover is finitely generated, torsion-free and perfect
distinct_from:
  free-abelianized-cover-fd-radical-is-commutator: that computes the exact finite-dimensional radical of the cover E and identifies it with [E,E]; this is about the group [E,E] itself, proving it finitely generated with an explicit bound, perfect, and with no finite-dimensional theory at all.
  free-abelianized-cover-is-torsion-free: that proves the cover E is torsion-free; this passes to its commutator subgroup and adds finite generation and perfectness, which the cover itself does not have.
  full-mf-radical-has-fp-cover-same-generators: that is the finite-presentation reduction of the strong input, used here as a preliminary; this is the cover built over the reduced input.
  defect-saturation-full-mf-radical: that already gives a two-generated finitely presented torsion-free group with full MF radical, using property (T); this is property-(T)-free but proves only collapse of exact finite-dimensional representations, which is strictly weaker.
artifacts:
  - research/artifacts/torsion-free-cover-perfect-and-congruence-obstructions-2026-09-08.md
---

**ESTABLISHED.**  Let `G` be a nontrivial group all of whose homomorphisms
to MF groups are trivial, reduced by
`full-mf-radical-has-fp-cover-same-generators` to a finite presentation

```text
G = F/R = <x_1,...,x_r | r_1,...,r_s>,
E = F/[R,R],    A = R/[R,R],    T = E'.                            (TP1)
```

Then `T` is nontrivial and:

1. **torsion-free**, being a subgroup of the torsion-free `E`;
2. **perfect**, `T = T'`;
3. **finitely generated**, with

```text
d(T) <= r + s + r^2;                                              (TP2)
```
4. every homomorphism `T -> U(d)`, for every finite `d`, is **trivial**; that
   is, `Rad_fd(T) = T`.

Item 2 holds for the commutator subgroup of any abelian-kernel extension of
a perfect group, and `G` is perfect because a nontrivial finitely generated
abelianization would have a nontrivial finite cyclic quotient.

**This is not non-MF.**  Item 4 concerns exact finite-dimensional unitary
representations only.  The inference from items 1--4 to non-MF is refuted by
`perfect-torsion-free-mf-group-has-no-fd-representations`, which exhibits a
group with every one of these properties except finite generation and which
is MF.  The isolated open implication remains
`free-abelianized-cover-reflects-mf`.

DERIVATION
abelianized-cover-commutator-perfect-proof
