---
rg: 2
id: dyadic-pauli-payload-capacity-proof
kind: route
title: Flip every dyadic sign atom and apply the regular three-row capacity fence
target: dyadic-pauli-payload-flags-supply-strict-target-capacity
requires:
  - maximal-forbidden-atom-has-a-named-positive-half
  - rectangular-three-row-cell-forces-double-target-capacity
---

Because the different Pauli pairs commute, the projections

```text
C product_(j=1)^n (1+sigma_j Z_j)/2,
sigma in {+1,-1}^n,                                   (DPP1)
```

are pairwise orthogonal and sum to `C`.  Relation `(DPF1)` and `CJ=-C`
show that conjugation by `X_j` flips exactly the `j`th sign in `(DPP1)`.
Trace invariance therefore gives the same trace to all `2^n` atoms.  Their
sum is `C`, proving

```text
tau(D_n)=2^(-n)tau(C).                                 (DPP2)
```

The case of the first sign alone similarly gives `tau(E)=tau(C)/2`, while
`F_n=C-D_n` gives the remaining formula in `(DPF3)`.  If `Q` commutes with
the packet and context, insert `Q` in every projection; all conjugations
preserve `Q`, so the same proof applies verbatim.

The lower bound `(DPF5)` is `(MFA1)` from
`maximal-forbidden-atom-has-a-named-positive-half`, followed by the exact
first-sign split.  A fixed finite packet has a dimension-independent HS
stability modulus, and trace changes by at most the normalized `2`-norm of
the corrected projection difference.  This proves the robust statement.

For the fence, the fixed formulas in `(DPF2)` and every operation listed in
the claim are available in the left regular finite factor.  If the three
rows `(DPF7)` held there, the exact case of
`rectangular-three-row-cell-forces-double-target-capacity` would give

```text
tau(F_n)>=2tau(E),
```

contrary to `(DPF3)` and `kappa_n>0` whenever `C!=0`.  Faithfulness of the
regular trace gives `tau(C)>0` for a nonzero injected packet projection.
