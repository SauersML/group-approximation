---
rg: 2
id: asymmetric-head-reflection-return-erases-deep-flags
kind: claim
title: Exact conjugate-head returns erase every accumulated star flag except one half
artifacts:
  - research/asymmetric-head-reflection-return-proof.md
distinct_from:
  four-cell-marked-star-has-an-eighth-head-flag: that constructs the literal one-eighth cumulative head source and checks the shortest positive Coxeter palindrome; this uses actual inverse heads to obtain genuine conjugacy of the return holonomy and computes the resulting loss of all deep flags.
  marked-star-asymmetric-heads-have-half-quarter-sources: that computes the uncancelled half and quarter cumulative sources; this proves that canceling their cumulative holonomy by the natural conjugate return restores only a half source.
  support-return-selector-occurrence-fence: that audits the existing partial-Whitehead support-return words on transported same-center charts; this audits the new distinct-center asymmetric-head reflection returns directly on the positive marked-star carrier.
  binary-leavitt-two-shared-gauge-selector-compiler: that requires conjugate gauges while retaining source fractions one half and one quarter; this supplies exact conjugacy but proves that both returned source fractions are one half.
---

Let `E_m` be a positive marked-star carrier with `m+1` anchored Pauli cells,
and let `H_1,...,H_m` be the consecutive asymmetric heads.  The cases
`m=2,3` are the quarter and eighth packets already constructed; the
five-center overlap bound also permits `m=4` inside rank twenty.

The monotone word

```text
M_m=H_mH_(m-1)...H_1                                  (AHR1)
```

has source atom

```text
E_m product_(j=2)^(m+1)(1+Z_j)/2,                    (AHR2)
```

of relative rank `2^(-m)`.  The most direct way to cancel its accumulated
holonomy is to return by actual inverse heads and retain one conjugated
head:

```text
R_m=H_m...H_2 H_1 H_2^(-1)...H_m^(-1).               (AHR3)
```

This gives the strongest possible algebraic gauge lock: `R_m` is literally
conjugate to `H_1` in the group, so every occurrence factor of `R_m` is the
transported occurrence factor of `H_1`, with no appeal to a Coxeter model or
to compression exactification.

Nevertheless its compression to the original marked star has only one
Pauli condition.  Put

```text
Xi_m=Z_2Z_3...Z_(m+1),       epsilon_m=(-1)^(m+1).
```

Then, for `S_m=E_mR_mE_m`,

```text
S_m^*S_m=S_mS_m^*=E_m(1+epsilon_m Xi_m)/2.            (AHR4)
```

Thus both source and range have relative rank `1/2`, independently of
`m`.  In particular, for two heads the exact conjugate return keeps
`Z_2Z_3=-1`, while for three heads it keeps `Z_2Z_3Z_4=+1`.  It does not
retain the quarter or eighth cumulative atom.

Using the heads themselves instead of their inverses does not help.  The
Coxeter-shaped positive palindrome

```text
P_m=H_m...H_2H_1H_2...H_m                             (AHR5)
```

has source and range projections

```text
(E_mP_mE_m)^*(E_mP_mE_m)=E_m(1-Z_2)/2,
(E_mP_mE_m)(E_mP_mE_m)^*=E_m(1+epsilon_m Xi_m)/2.     (AHR6)
```

It is again half-to-half.  Formally replacing the head occurrences by
simple Coxeter involutions would make `(AHR5)` a reflection word, but the
actual heads are not involutions:

```text
H_i^2=x_(k_(i+1),k_i)(b_(i+1)a_i)!=1,
H_i^4=1.                                               (AHR7)
```

Equation `(AHR7)` is the forward prefix root.  Hence no valid proof may
cancel the repeated head letters as if they were the outer-corrected
Whitehead involutions.

Therefore the natural actual return that genuinely conjugates one reservoir
occurrence loses exactly the extra flags that produced `1/4` and `1/8`.
A successful comparison must be nonreflectional: it must cancel the
cumulative occurrence factor through an odd identity-outer word while
retaining at least two independent `Z` conditions.  Neither inverse
conjugation nor the positive Coxeter palindrome can do this.

No Property `(T)`, Kazhdan input, canonical trace, local heavy computation,
or literature theorem is used.

DERIVATION
asymmetric-head-reflection-return-proof
