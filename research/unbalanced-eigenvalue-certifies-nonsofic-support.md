---
rg: 2
id: unbalanced-eigenvalue-certifies-nonsofic-support
kind: claim
title: An integral self-adjoint matrix with a non-integral or Galois-unbalanced eigenvalue has a nonsofic support subgroup
distinct_from:
  heavy-eigenvalue-gives-determinant-counterexample: that turns an eigenvalue heavier than n over its degree into a determinant violation; this certifies only nonsoficity, from the weaker defect of non-integrality or unequal conjugate multiplicities
  galois-invariance-forces-totally-real-atoms: that derives balanced totally real atoms from invariance of kernel dimensions; this is the contrapositive of Thom's sofic theorem, localized to the support subgroup
  determinant-violation-needs-nonsofic-support-subgroup: that localizes determinant violations; this localizes eigenvalue defects that need not violate the determinant bound
---

**ESTABLISHED** by `unbalanced-eigenvalue-nonsofic-support-proof`.

Let `G` be any group, `A in M_n(Z[G])` self-adjoint, and `H` the subgroup generated
by the group elements in the support of `A`. Suppose some eigenvalue `lambda` of
`r_A` has one of these defects:
- `lambda` is not an algebraic integer;
- some Galois conjugate of `lambda` is not real;
- some conjugate `sigma lambda` has
  `dim ker(r_A - sigma lambda) != dim ker(r_A - lambda)`.

Then `H` is not sofic.

**The ladder of spectral monsters.** For a self-adjoint integral matrix over any
group:

| defect of an eigenvalue `lambda` | certifies | graph node |
|---|---|---|
| any of the three above | nonsofic support | this claim |
| multiplicity above `n / deg(lambda)`, e.g. transcendental | determinant violation | `heavy-eigenvalue-gives-determinant-counterexample` |

Neither defect can occur when `||A|| <= 2`
(`norm-two-integral-matrices-reduce-to-virtually-cyclic-groups`).
