---
rg: 2
id: atlas-first-common-rhs-return-star-has-rank-two
kind: claim
title: The first complete Atlas common-RHS return star has quotient rank two and a rectangular escape
invalidates:
  - atlas-common-rhs-star-authenticates-prefix-reservoir
distinct_from:
  atlas-first-composable-mixed-pair-has-zero-quotient-rank: that keeps separate product nuisances and obtains rank zero; this is the first literal return family sharing one RHS occurrence and therefore has a nonzero rank increment.
  atlas-mixed-minor-needs-nuisance-quotient-rank: that requires rank increment three for the three desired path columns; this computes increment two on the complete first common-RHS star.
  mixed-steinberg-loops-admit-morita-rectangular-model: that gives the general categorical model; this identifies the first return star in canonical packet order and computes its exact nuisance matrix.
artifacts:
  - experiments/atlas_first_nonscalar_mixed_row_audit.py
---

**ESTABLISHED EXACT RETURN-STAR AUDIT.** Group the mixed-direction,
nonconstant St3 rows by the signature of their right-hand side

```text
(target root i,k; coefficient product r s).           (FRS1)
```

The first signature to recur in canonical order is `(1,2;e e)`. Its complete
rank-five intermediate-index star consists of zero-based full-family entries

```text
3260: st3_132_ee,       3335: st3_142_ee,
3408: st3_152_ee.                                      (FRS2)
```

Thus the packet entries are `3261,3336,3409`. Their syllable lengths are
`85,85,39`, and their Atlas `X`-lengths are `271,295,130`. The attached MSI
audit reconstructs the complete ordering and verifies these values.

Write the three composable path products as `P_3,P_4,P_5` and the common
RHS occurrence `x_12(ee)` as `R`. The three projected equations have exact
coefficient form

```text
P_3-R=0,       P_4-R=0,       P_5-R=0.                (FRS3)
```

Keeping `R` as the mandatory nuisance column gives

```text
C=I_3,       D=(-1,-1,-1)^T.                          (FRS4)
```

Consequently

```text
rank[C D]=3,       rank(D)=1,
rank[C D]-rank(D)=2.                                  (FRS5)
```

The first two rows already give a genuine one-dimensional return by
eliminating `R`; completing the star gives exactly the two independent path
differences. It does not give the rank-three quotient required to control
all three desired monomials in `atlas-mixed-minor-needs-nuisance-quotient-rank`.
Deleting the common `R` column is precisely the forbidden nuisance deletion.

The missing common mode is realized by an exact rectangular model. Let
`V_1,V_2` be arbitrary, choose a nonzero map `R:V_2->V_1`, and for each
`j=3,4,5` choose an arbitrary factorization

```text
V_2 --B_j--> V_j --A_j--> V_1,       A_j B_j=R.       (FRS6)
```

The intermediate spaces `V_3,V_4,V_5` may have distinct dimensions: enlarge
each by any spectator summand on which `A_j` and `B_j` vanish. Elementary
block multiplication then satisfies all three rows `(FRS2)` exactly. The
three paths agree, but no intermediate reservoir is identified with another
or with the source/target reservoir. Passing to the finite left regular
representation gives an exact unitary model.

Thus the first actual return family has positive nuisance-quotient rank, but
only on the two antisymmetric path differences. The common product mode is a
rectangular escape. The next viable family must identify the common RHS `R`
itself with an independently authenticated chart occurrence, rather than add
another factorization through a fresh intermediate object.

DERIVATION
atlas-first-common-rhs-return-star-rank-proof
