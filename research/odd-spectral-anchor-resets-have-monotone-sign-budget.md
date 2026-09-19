---
rg: 2
id: odd-spectral-anchor-resets-have-monotone-sign-budget
kind: claim
title: Odd spectral anchor resets have an exact monotone negative-sign budget
distinct_from:
  spectral-cut-anchor-reset-pays-boundary-in-one-row: that estimates one nonreducing reset; this proves repeated overlapping cuts cannot recreate anchor-negative spectral mass.
  single-spike-split-or-charge-has-fourth-root-modulus: that bounds one boundary-heavy cut's mass; this supplies its cross-iteration monotone budget.
  central-adaptive-peeling-or-noncentral-stopping: that must combine all anchors and scales; this eliminates literal recycling for a fixed anchor.
---

ESTABLISHED.  Let `A,B` be reflections,

```text
 Y=(B-ABA)/2,       R=Y^2,       e_-=(1-A)/2,
```

and let `p=1_[s,1](R)` for `s>0`.  Then `p` commutes with `A`, and

```text
 tau(pe_-)=tau(p)/2.                                    (MSB1)
```

Indeed `AYA=-Y`, while `Y` commutes with `R`.  On `p`, `Yp` is invertible.
Its polar part `U_p=Yp(Rp)^(-1/2)` is a unitary on `p` satisfying
`AU_p=-U_pA`.  It exchanges the two anchor-sign eigenspaces inside `p`.

Reset the anchor by `A'=p+(1-p)A`.  Then

```text
 e_-'=(1-p)e_-,
 ||A-A'||_2^2=4tau(pe_-)=2tau(p).                       (MSB2)
```

For any iterative sequence of positive odd-square spectral cuts for the
current anchor,

```text
 sum_n tau(p_n)<=2tau(e_(0,-))<=2,
 sum_n ||A_(n+1)-A_n||_2^2<=4tau(e_(0,-))<=4.           (MSB3)
```

The cuts need not commute with earlier cuts.  Their negative pieces are
trace-disjoint because the negative projection decreases monotonically.
Thus boundary leakage may create new odd commutators, but it cannot recycle
the anchor's negative-sign mass.

For a balanced tuple, divide the reset ledger by `L`.  Together with the
fourth-root small-mass alternative, one boundary-heavy cut per anchor per
geometric energy stage has vanishing averaged cost.  This does NOT imply
coverage.  `monotone-anchor-sign-budget-does-not-give-stagewise-coverage`
puts `N` central, zero-boundary Pauli spikes under one anchor.  The sign
budget is saturated exactly, but fewer than `N` resets leave an odd part of
operator norm one.  Thus a terminal argument must batch a weighted family
of cuts or invoke balanced parity to exclude the disjoint-spike profile;
trace monotonicity alone controls cost, not coverage rate.
