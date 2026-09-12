---
rg: 2
id: atlas-19243-centrality-forces-s3-distance
kind: claim
title: The 19243 centrality consequence keeps atlas microstates a fixed HS distance from its S3-aligned manifold
distinct_from:
  atlas-19243-s3-relative-normal-form: that identifies the interior word and gives an exact S4 model when used alone; this uses its equivariance to obtain a quantitative lower bound once the canonical centrality consequence is imposed.
  atlas-two-s3-covariance-collapse: that seeks an upper bound forcing two covariance defects to zero; this is a lower-distance theorem showing that any full-packet microstate must live on a genuinely nonclassical boundary branch.
  raw-swap-forces-s3-reynolds-deficit-one-over-320: that lower bound uses separation of the marked raw source word and a different raw S3 packet; this lower bound comes directly from the atlas relator packet through collision-19243 centrality.
artifacts:
  - experiments/atlas_19243_s3_gap.py
---

**ESTABLISHED.**  Use the notation of
`atlas-19243-s3-relative-normal-form`.  Let

```text
K_19243=<r,s> ~= S_3
```

be the fixed aligned subgroup and let `C_K` denote the unitary commutant of
its regular `A_8` representation (with arbitrary external multiplicity).
Let `q(U)` be collision word `19243` evaluated at relative chart unitary `U`,
and let

```text
c(U)=[rho(p1_12),q(U)]
```

be the centrality word from
`atlas-19243-centrality-is-bar-s-consequence`.

Then for every relative unitary `U`,

```text
dist_2(U,C_K)
 >= max(0, (sqrt(2)-||c(U)-1||_2)/16).              (19243-DIST)
```

Consequently, if

```text
delta(U)=max_(s in bar_S)||pi_U(s)-1||_2,
```

then for the fixed normal-closure constant `L_19243`,

```text
dist_2(U,C_K)
 >= max(0, (sqrt(2)-L_19243 delta(U))/16).           (19243-PACKET)
```

In particular every canonical regular-atlas microstate sequence has

```text
liminf dist_2(U_n,C_K) >= sqrt(2)/16 > 0.            (19243-FAR)
```

## Proof idea

For every `V in C_K`, put `c_V=V^*rho(b)V`.  Since `V` commutes with `r,s`,
the reduced 19243 polynomial satisfies

```text
F(c_V)=V^*F(rho(b))V=V^*rho(b)V=c_V.
```

Conjugating back gives the stronger exact statement

```text
q(V)=rho(b),                                          (19243-CONST)
```

independent of `V`.  The exact finite calculation in the replay script checks
`F(rho(b))=rho(b)` and

```text
[p1_12,b] != 1 in A_8.
```

Hence regular character gives

```text
||c(V)-1||_2=sqrt(2)                                 (19243-GAP)
```

for every multiplicity.

For arbitrary relative unitaries `U,V`, each conjugated second-chart syllable
changes by at most `2||U-V||_2`.  Collision 19243 has four such syllables, so

```text
||q(U)-q(V)||_2 <= 8||U-V||_2.
```

The commutator word uses `q` and `q^*` once each, giving

```text
||c(U)-c(V)||_2 <= 16||U-V||_2.
```

Reverse triangle against `(19243-GAP)`, then infimize over `V in C_K`, to
obtain `(19243-DIST)`.  Finally
`atlas-19243-centrality-is-bar-s-consequence` supplies
`||c(U)-1||_2 <= L_19243 delta(U)`.

## Research consequence

The exact boundary tangent theorem says the classical fold is infinitesimally
rigid modulo an `H`-commutant.  This claim shows that the full atlas packet
cannot approach even the smaller `K_19243` commutant.  Therefore any
hypothetical hyperlinear sequence must stay on a **macroscopically remote
nonlinear boundary branch**.  Local inverse-function arguments around the
classical fold can never by themselves produce the missing microstates or the
missing contradiction; the remaining theorem is genuinely global branch
exclusion.
