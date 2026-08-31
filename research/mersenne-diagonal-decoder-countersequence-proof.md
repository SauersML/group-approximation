---
rg: 2
id: mersenne-diagonal-decoder-countersequence-proof
kind: route
title: Discharge the phase entropy hypothesis and translate edge distance to operator distance
target: mersenne-phases-refute-diagonal-iwahori-decoder
requires:
  - binary-iwahori-h1-vanishes-at-odd-levels
  - linear-cocycle-dimension-forces-phase-countersequence
  - diagonal-exact-inversion-is-two-cubic-parity-code
---

Let `K_n=K_(H,m_n)` and write

```text
V_n=|P_n\Q_n|,
E_n=|N_n\Q_n|=m_n V_n/2.
```

The odd-level binary cohomology theorem gives

```text
Z^1(K_n;F_2)=B^1(K_n;F_2),
dim Z^1(K_n;F_2)=V_n-1.                                (MDP1)
```

Consequently the hypothesis `k_n<=C V_n` of the sequential phase-entropy
theorem holds at every level with `C=1`. That theorem supplies a constant

```text
delta=delta_1>0
```

and translated half-interval phases whose global edge cochain `c_n`
obeys

```text
|supp(delta_1 c_n)|/|Q_n|<2/n,
dist_E(c_n,Z^1(K_n;F_2))>=delta.                        (MDP2)
```

Identify an edge cochain with the left-`N_n`-invariant group function

```text
c_n(g)=c_n(N_n g).
```

The two components of the cellular curl are exactly `h_a(c_n)` and
`h_b(c_n)`. The face set is the disjoint union of the `A_n`- and
`B_n`-cosets, including the distinct central-sign duplicate rows.
Therefore (MDP2) says precisely

```text
(|supp h_a(c_n)|+|supp h_b(c_n)|)/|Q_n|<2/n.            (MDP3)
```

There is no normalization loss in the distance. Every differing edge bit
represents exactly `|N_n|` differing group coordinates, while

```text
|Q_n|=|N_n| E_n.
```

Hence

```text
dist_Q(c_n,C_(N_n))
 =dist_E(c_n,Z^1(K_n;F_2))
 >=delta.                                                (MDP4)
```

Because `c_n` is left-`N_n`-invariant, the involution and inversion
rows in (MDD1) are exact. The fourth-power row belongs to the unchanged
regular congruence core. The exact cubic identities for diagonal gauges
give

```text
||(X_n T_n)^3-1||_2^2
 =12 |supp h_a(c_n)|/|Q_n|,

||(X_n T_n^2 R_n)^3-1||_2^2
 =12 |supp h_b(c_n)|/|Q_n|.                             (MDP5)
```

Summing (MDP5) and applying (MDP3) proves (MDD2).

Finally the exact diagonal correction formula is

```text
inf_(c' in C_(N_n))
 ||M_((-1)^c_n)lambda(x)-M_((-1)^c')lambda(x)||_2
 =2 sqrt(dist_Q(c_n,C_(N_n))).                          (MDP6)
```

Equations (MDP4) and (MDP6) prove (MDD3). Since the right side stays
positive while (MDD2) tends to zero, a diagonal Hamming modulus cannot
exist. Nothing in this argument lower-bounds distance to nondiagonal
endpoints or to flexible padded endpoints, which is the stated firewall.
