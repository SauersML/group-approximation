---
rg: 2
id: division-ring-embedding-colimit-tester-proof
kind: route
title: Take an ultralimit of integer-valued rank functions along the colimit and apply the universal tester
target: division-ring-embedding-torsion-free-one-group-tester
requires:
  - two-generator-fp-torsion-free-master-tester
---

Fix a field `K`.  Let `D_K` be the class of groups `G` for which `K[G]` embeds
in a division ring.

**Sources.**  Jaikin-Zapirain--Lopez-Alvarez, *The strong Atiyah and Lueck
approximation conjectures for one-relator groups*, arXiv:1810.12135, Section
2.4, read from the PDF: a Sylvester matrix rank function on a ring `R` is a
function on matrices over `R` satisfying (SMat1)--(SMat4); "We denote by P(R)
the set of Sylvester matrix rank functions on R, which is a compact convex
subset of the space of functions on matrices over R"; and "If rk takes only
integer values, then by a result of P. Malcolmson [28] there exists a division
algebra D such that (D, rk_D, phi) is a regular envelope of rk", meaning
`rk(A) = rk_D(phi(A))` with `phi: R -> D` a ring homomorphism.  For such `phi`,
`phi(x) = 0` iff `rk(x) = 0`, since the dimension rank on a division ring
vanishes only on `0`.  Hence a **faithful** integer-valued Sylvester matrix
rank function on `R` gives an embedding of `R` in a division ring.

**Subgroups.**  `K[H] <= K[G]` for `H <= G`, so `D_K` is closed under
subgroups.

**Directed colimits.**  Let `G = colim_(i in I) G_i` with arbitrary structure
maps and every `K[G_i]` embedded in a division ring `D_i`.  Write `rk_i` for the
rank function on `K[G_i]` pulled back from `D_i`; it is integer-valued and
faithful.  The group-algebra functor commutes with directed colimits, so
`K[G] = colim_i K[G_i]` as rings.  Fix an ultrafilter `U` on `I` containing
every cone `{j : j >= i}`.  For a matrix `A` over `K[G]`, choose a lift `A_i`
over some `K[G_i]`, let `A_j` be its image for `j >= i`, and put

```text
rk(A) = lim_U rk_j(A_j).
```

Two lifts of `A` have the same image in `K[G_j]` for all large `j`, so `rk` is
well defined.  Each axiom (SMat1)--(SMat4) involves finitely many matrices and
holds at every large stage, so it holds for `rk`.  The values of `rk_j` on a
fixed `n x m` matrix lie in `{0,...,min(n,m)}`, so `rk` is integer-valued.
If `x != 0` in `K[G]`, its lift has nonzero image in every `K[G_j]`, since a
zero image would make `x = 0`, so `rk_j(x_j) = 1` and `rk(x) = 1`.  Thus `rk`
is faithful and `K[G]` embeds in a division ring.  So `D_K` is closed under
directed colimits.

**Tester.**  Item 6 of [[two-generator-fp-torsion-free-master-tester]]: for
every class closed under subgroups and directed colimits with arbitrary
structure maps, `E` lies in the class iff every torsion-free group does.
Applied to `D_K`, this gives the claim.  The corollary in the target uses only
Linnell's division-closure theorem and this equivalence.  QED
