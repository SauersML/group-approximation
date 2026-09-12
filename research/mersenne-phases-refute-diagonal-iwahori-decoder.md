---
rg: 2
id: mersenne-phases-refute-diagonal-iwahori-decoder
kind: claim
title: Mersenne interval phases refute the diagonal Iwahori decoder
distinct_from:
  linear-cocycle-dimension-forces-phase-countersequence: that proves the phase countersequence under a linear cocycle-dimension hypothesis; this discharges the hypothesis and records the operator consequence.
  binary-iwahori-h1-vanishes-at-odd-levels: that computes the exact codewords; this constructs cochains with vanishing syndrome and constant distance from that code.
  diagonal-exact-inversion-is-two-cubic-parity-code: that identifies the diagonal code and its norm formulas; this supplies an asymptotic family violating its proposed Hamming modulus.
---

**ESTABLISHED; DIAGONAL-SECTOR FIREWALL ONLY.** Put

```text
m_n=4^n-1,
Q_n=SL_2(Z/m_n Z)/{+-I},
R_n=lambda_Qn(r),
T_n=lambda_Qn(t).
```

For every sufficiently large `n`, there are left-`N_n`-invariant functions

```text
c_n:Q_n -> F_2
```

such that, for `X_n=M_((-1)^c_n) lambda_Qn(x)`,

```text
X_n^2=1,
X_n R_n X_n=R_n^(-1),
R_n T_n R_n^(-1)=T_n^4,                                (MDD1)
```

while the two cubic defects satisfy

```text
||(X_n T_n)^3-1||_2^2
 +||(X_n T_n^2 R_n)^3-1||_2^2 < 24/n.                  (MDD2)
```

Here `||.||_2` is normalized Hilbert--Schmidt norm.

Let `C_(N_n)` be the exact diagonal endpoint code: the
left-`N_n`-invariant functions satisfying both cubic parity rows. Then

```text
inf_(c' in C_(N_n))
 ||X_n-M_((-1)^c') lambda_Qn(x)||_2 >=1/640.             (MDD3)
```

Equivalently,

```text
(|supp h_a(c_n)|+|supp h_b(c_n)|)/|Q_n| <2/n,
dist_(N_n\Q_n)(c_n,C_(N_n))>=1/1638400.                (MDD4)
```

Thus no dimension-free modulus tending to zero can decode the two cubic
syndromes inside the diagonal exact-inversion gauge sector. The low-link
mode is now a genuine global binary countersequence, not merely a local
spectral warning.

This does **not** show that `(X_n,R_n,T_n)` stays far from every exact
representation after changing the core, using nondiagonal gauges, or
adding `o(|Q_n|)` dimensions. It refutes the diagonal Hamming-decoder
route only. Flexible Hilbert--Schmidt stability and the non-hyperlinearity
root remain open.

DERIVATION
mersenne-diagonal-decoder-countersequence-proof
