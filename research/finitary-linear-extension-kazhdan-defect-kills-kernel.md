---
rg: 2
id: finitary-linear-extension-kazhdan-defect-kills-kernel
kind: claim
title: A binary finitary linear extension with a compressed Kazhdan subgroup has its whole kernel in the MF radical
distinct_from:
  kazhdan-criterion-is-inert-on-finitary-permutation-extensions: that proves the normal-Kazhdan criterion cannot fire anywhere inside a finitary PERMUTATION extension of an MF group; this is the companion positive statement in which the same criterion does fire, the difference being that a binary transvection is an involution and a finitary permutation is not.
  locally-finite-centralizer-derived-subgroup-is-mf-invisible: that criterion needs a locally finite centralizer and two commuting compressed conjugates and kills only a derived subgroup, with no Kazhdan subgroup anywhere; this consumes the Kazhdan criterion instead, needs one compressed conjugate, and kills the entire finitary linear kernel.
  dyadic-perturbation-group-mf-radical-is-finitary-alternating: that computes the radical of one concrete finitary permutation group as the finitary alternating group; this is a criterion over an arbitrary base action whose kernel is a finitary linear group over F_2, and the two are proved by different theorems for the reason recorded on the inertness claim.
artifacts:
  - research/artifacts/finitary-linear-vs-permutation-kazhdan-criterion-2026-09-08.md
---

**ESTABLISHED.**  Let a countable group `V` act on a countably infinite set
`X`, adjoin two points `a, b` fixed by `V`, and put

```text
Y = X u {a,b},   W = F_2^(Y),   K = GL_fin(W),   G = K x| V,          (FL1)
```

where `V` acts by conjugation through the permutation matrices of its action
on `Y`, and *finitary* means equal to the identity outside a finite square
block of the displayed basis.  Suppose there are `L <= V` with property (T),
`u in V`, `x in X` and `ell in L` with

```text
u L u^-1 <= L,        L x = {x},        ell u x != u x.               (FL2)
```

Then every homomorphism from `G` to an MF group kills `K`; in particular `G`
is not MF, and if `V` is MF then

```text
Rad_MF(G) = K.                                                        (FL3)
```

**The mechanism, which is the point.**  With `T_(pq) = I + E_(pq)` put

```text
c = T_(xb),   y = T_(a,ux),   z = T_(ab),   H = <L, u, c, y>,
```

so that `c` centralizes `L`, `[u c u^-1, ell] = T_(ux,b) T_(ell u x, b)^-1`,
and its commutator with `y` is `z`.  Then `<z>` is a **finite central**
subgroup of `H` lying in `D_H(L)`, so `normal-kazhdan-defect-non-mf` applies
to `H` and kills `z`; the normal closure of `z` in `G` contains every
transvection and so is all of `K`.

The finite Kazhdan subgroup is normal in `H`, **not** in `G`.  Every previous
use of that criterion in this archive supplied a subgroup normal in the group
being killed, and the criterion does not require it: apply it in a subgroup,
then take the normal closure.  Under the mild hypothesis that every
nonidentity element of `V` moves infinitely many points of `X`, `G` has no
nontrivial finite normal subgroup at all, so no ambient-normal form of this
argument exists.

**Characteristic two is what makes it work.**  The defect element is a
unipotent transvection, hence an involution, hence generates a finite central
subgroup of `H`.  A finitary permutation cannot play that role, and
`kazhdan-criterion-is-inert-on-finitary-permutation-extensions` proves that
nothing else can either: in `Sym_fin(X) x| V` with `V` MF, no subgroup
whatsoever contains a nontrivial normal Kazhdan subgroup of a compression
defect.  The two claims together say the choice of criterion in this family is
forced by the kernel, not by convenience.

**Instances.**  `(FL2)` is satisfied by the dyadic base already established
here: `V = Z[1/2]^3 x| (SL_3(Z) x Z)` acting on the dyadic lattice cosets, with
`L = Z^3 x| SL_3(Z)` -- property (T) by `affine-semidirect-sl3-source-has-property-t` --
`x = Z^3`, `u` the doubling, `ell` the translation by `e_1`, the witness being
`2 Z^3 != e_1 + 2 Z^3`.  That base's residual finiteness, transitivity and
finite generation are established for the permutation example
`dyadic-perturbation-group-is-sofic`, and the soficity argument transfers with
`GL(F_2^O) x| N_0` in place of `Sym(O) x| N_0`; no soficity claim for `(FL1)`
is made here.

Nothing above bears on `binary-jacobson-mf-radical-dichotomy`, whose kernel is
the same kind of finitary linear group but which is reached from a ring rather
than an action.
