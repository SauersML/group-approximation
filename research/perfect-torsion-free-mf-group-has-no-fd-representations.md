---
rg: 2
id: perfect-torsion-free-mf-group-has-no-fd-representations
kind: claim
title: A perfect torsion-free MF group can have no finite-dimensional representations at all
distinct_from:
  rational-heisenberg-fd-radical-is-commutator-and-mf: that group has finite-dimensional radical exactly its commutator subgroup, so its finite-dimensional theory is abelian but nonzero, and it is not perfect; this one is perfect, so the collapse is total and Rad_fd is the whole group, which is the profile the perfect cover produces.
  abelianized-cover-commutator-is-finitely-generated-perfect: that produces a finitely generated group with these properties from a strong input, and its MF status is open; this is an explicit MF group with the same properties except finite generation, so it refutes the inference from them to non-MF.
  exact-fd-invisibility-has-no-general-hs-robustification: that refutes a uniform quantitative robustification of exact invisibility at one mark; this refutes the qualitative inference from total collapse, with perfectness and torsion-freeness added.
  torsion-free-central-cover-forces-abelian-finite-subgroups: that is an obstruction to central covers of groups with nonabelian finite subgroups; this is a positive example and concerns no cover at all.
artifacts:
  - research/artifacts/torsion-free-cover-perfect-and-congruence-obstructions-2026-09-08.md
---

**ESTABLISHED.**  Index rows and columns by the **ordered set `Q`** and let

```text
M = { I + A : A finitely supported, A_(ij) = 0 unless i < j },     (TM1)
```
a countable group under matrix multiplication, with
`x_(ij)(a) = I + aE_(ij)` for `i < j`.  Then

```text
M is torsion-free,     M = [M,M],
Rad_fd(M) = M,         M is operator MF.                          (TM2)
```

So every exact finite-dimensional unitary representation of `M` is trivial,
and `M` is nevertheless MF.

**What this refutes.**  The inference

```text
K countable, torsion-free, perfect, Rad_fd(K) = K  ==>  K is not MF
```
is false.  That is exactly the profile of
`abelianized-cover-commutator-is-finitely-generated-perfect`, so computing
the cover's commutator subgroup and observing that it has no
finite-dimensional theory cannot by itself settle
`free-abelianized-cover-reflects-mf`.  This strengthens
`rational-heisenberg-fd-radical-is-commutator-and-mf`, whose group is not
perfect and whose collapse is therefore only to an abelian image.

**`M` is not finitely generated**: any finite subset is supported on a finite
set of indices, and products and inverses stay there, while `M` has
transvections on arbitrarily many indices.  So it does not decide the MF
status of the finitely generated cover, and finite generation is precisely
what separates the two.

DERIVATION
perfect-torsion-free-mf-unitriangular-proof
