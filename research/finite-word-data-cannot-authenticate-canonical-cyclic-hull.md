---
rg: 2
id: finite-word-data-cannot-authenticate-canonical-cyclic-hull
kind: claim
title: Fixed word data cannot authenticate a canonical cyclic reducing hull in normalized HS norm
distinct_from:
  canonical-reached-hulls-tensor-amplify-fully: That proves the exact behavior under spectator tensoring; this proves discontinuity under an HS-microscopic change of a hull generator.
  isotropic-mixing-has-only-logistic-carrier-growth: That limits quantitative growth under genuine mixing; this rules out naming the minimal hull by finitely many bounded-radius orbit words.
  btb-three-line-tree-retains-multiplicity-return-gauge: That aligns edge gauges inside an already chosen carrier; this shows that the path-specific carrier itself cannot be recovered from fixed local word data.
  cyclic-hull-antiphase-has-propagation-or-radius-firewall: That gives the centralizer phase-propagation dichotomy and a rank-one dihedral radius obstruction; this gives an HS-microscopic splice at the canonical positive seed density, with hull trace jumping from `1/8` to `1`.
---

**ESTABLISHED CYCLIC-HULL NO-GO.**  Fix a word radius `L`.  For every large
`d` divisible by eight, let `m=d/8`, let `p_d` project onto the first `m`
standard basis vectors of `C^d`, and put

```text
B_d=I-2p_d.                                             (FCH1)
```

Let `u_d` be the permutation unitary of the single cycle
`(0 1 ... d-1)`.  Let `v_d` be the permutation unitary which is the disjoint
union of the cycles `(0 ... m-1)` and `(m ... d-1)`.  Then

```text
||u_d-v_d||_(2,d)=2/sqrt(d),                            (FCH2)
Hull_(u_d)(p_d)=I,          Hull_(v_d)(p_d)=p_d.        (FCH3)
```

The norm formula follows because the two permutations differ on exactly two
input basis vectors, with squared Euclidean difference two on each.  The hull
formula follows because `v_d` preserves both blocks, whereas the orbit under
the full cycle of any nonzero coordinate subspace contains every coordinate.

Moreover, every word of length at most `L` in `u_d,u_d^*,B_d` sends
`Ran(p_d)` into the `L`-neighborhood of its interval support.  Consequently

```text
tau(join_(|w|<=L) w p_d w^*) <= 1/8+2L/d,              (FCH4)
```

although the true reducing hull is `I`.  Replacing `u_d` by `v_d` changes
each fixed word `w` by at most
`2 (# occurrences of u in w)/sqrt(d)` in normalized HS norm, by telescoping.
Hence every fixed finite relator-defect menu and every fixed finite word-moment
window takes asymptotically the same values on the two tuples, while their
canonical hull traces differ by `7/8`.

Thus neither finitely many cyclic-orbit generators nor finitely many normal
conjugates of the seed projection can serve as a dimension-uniform proxy for
the minimal reducing hull.  The same obstruction applies to a proposed
successive-hull two-cell if its only input about the parent hull is membership
in a fixed bounded list of word translates: an HS-microscopic bridge can turn
the seed block into the full cyclic hull without being visible to those rows.

This does not rule out path-specific `(CBR3)`.  It sharply identifies what an
actual construction must add: a dimension-uniform isoperimetric/spectral row
or a payload-conditioned typed floor which forbids the microscopic bridge.
Such a row is substantive analytic rigidity, not a formal consequence of
finite generation or of taking the canonical minimal hull.

DERIVATION
cyclic-block-splice-makes-hull-hs-discontinuous
