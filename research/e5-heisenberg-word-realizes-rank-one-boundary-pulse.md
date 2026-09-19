---
rg: 2
id: e5-heisenberg-word-realizes-rank-one-boundary-pulse
kind: claim
title: Four elementary E5 roots realize the paired rank-one pulse on a fresh Fourier boundary
artifacts:
  - experiments/e5_heisenberg_rank_one_boundary_pulse.py
distinct_from:
  one-sided-paired-frame-has-a-single-smith-rank-clock: that computes an abstract three-coordinate Smith comparison; this retains the honest full four-root center inside an elementary matrix group and obtains the missing relation spectrally on a relative character corner.
  normal-closure-of-moving-kernels-kills-the-hard-form: that imposes moving kernel lines as global relations; this imposes only the two stationary commuting relations and keeps every cross commutator as an independent root word.
  free-root-first-detection-eigenvectors-localize-exactly: that localizes a character of known valuation; this constructs the explicit group word whose relative hard character has that valuation and evaluates to one Pauli pair there.
---

Let `R=F_2[x]` and work in `E_5(R)`.  In the `(2,1,2)` block upper
Heisenberg subgroup put

```text
p_0=e_02(1), p_1=e_12(1), q_0=e_23(1), q_1=e_24(1).       (EHP1)
```

The two `p` roots commute, the two `q` roots commute, and

```text
[p_i,q_j]=e_(i,3+j)(1),                                  (EHP2)
```

so the four cross commutators are independent additive root coordinates.
Define the four-root word

```text
D=e_01(x)e_43(x)e_10(x)e_34(x)
  =diag(S,1,S^-1),
S=[[1+x^2,x],[x,1]].                                     (EHP3)
```

Conjugation by `D^-1` acts by `S^-1` on both the `p` and `q` coordinate
pairs.  Thus this one explicit elementary word realizes the polynomial
transporter required by the paired frame, while the coefficient packet may
remain fixed in a commuting factor.

The stationary minus hard sector has identical source and coefficient
cross form

```text
H=e_02^*+e_03^*+e_12^*,                                  (EHP4)
```

and hence zero relative form at level zero.  Transport only the source copy
and write

```text
Delta_n=H o wedge^2(T^-n)+H.                              (EHP5)
```

For every `n>=1`, `Delta_n` has a unique coefficient in its highest degree:

```text
deg Delta_n=4n-2,
[x^(4n-2)] Delta_n=e_13^*.                               (EHP6)
```

Consequently, if a relative additive character is trivial on every word of
degree below `4n-2` and is nontrivial on `x^(4n-2)`, its evaluated form is
exactly `e_13^*`, of alternating rank two.  The new boundary therefore
carries precisely one Pauli qubit.  This is an honest group-word realization
of the rank-one bottleneck; no polynomial kernel is imposed as a relation.
