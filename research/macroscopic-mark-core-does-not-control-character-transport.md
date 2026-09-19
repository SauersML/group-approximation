---
rg: 2
id: macroscopic-mark-core-does-not-control-character-transport
kind: claim
title: A full positive-density marked core can retain maximal character leakage
artifacts:
  - research/macroscopic-mark-character-leakage-proof.md
distinct_from:
  sparse-marked-lamp-corner-has-unit-relative-leakage: that keeps the visible mark at constant rank inside growing matrices and obtains maximal leakage only after corner normalization; this removes the spectator, gives the mark trace 2/3, and makes total ambient leakage equal to one.
  pointwise-lamp-covariance-has-half-mass-leak: that has a two-atom lift with half-mass leakage but does not keep the fixed two-lamp mark active; this keeps a fixed mark macroscopically visible and covers the entire carrier by two conjugate marked cuts.
  torsion-normal-generator-has-full-support-corona-core: that proves a surviving torsion normal generator can be reblocked to positive density using finitely many conjugate supports; this proves that positive density and finite conjugate support coverage alone do not transport the coordinate character PVM.
  defect-controlled-lamp-character-transport: that asks for leakage bounded by a fixed relator defect after a globally compatible lift is selected; this gives zero eventual defect on every fixed covariance relation and leakage one for the displayed coordinate lift.
---

**ESTABLISHED.**  There is a pointwise operator-norm asymptotic
representation of the lamplighter

```text
Gamma=(direct_sum_(F(a,b)) C_2) semidirect F(a,b)       (MMC1)
```

on the fixed three-dimensional carrier `C^3` with the following properties.
For the fixed two-lamp word

```text
w=m_e m_a                                                (MMC2)
```

the active projection

```text
p_n=(1-rho_n(w))/2
```

has

```text
rank(p_n)=2,              tr_3(p_n)=2/3.                (MMC3)
```

Moreover one actor conjugate already covers the whole carrier:

```text
p_n join U_n(a)p_nU_n(a)^*=1_(C^3).                     (MMC4)
```

Thus this model has exactly the positive-density and finite-conjugate support
coverage furnished abstractly by active-core reblocking; there is no sparse
spectator left.

Nevertheless `rho_n` is an exact representation of the **entire** lamp group
at every coordinate, every fixed lamp covariance identity is exact for all
large `n`, and the coordinate joint character PVM has

```text
L_s(rho_n,U_n(s))=1                                     (MMC5)
```

for every `s in {a,a^(-1),b,b^(-1)}` and every `n`.  Restricted to the two
atoms under `p_n`, its leakage is `2/3`, so its marked-corner-normalized
leakage is also one.

There is also a growing-dimensional variant which is pointwise faithfully
Hilbert--Schmidt separated.  Direct-sum three quarters of the preceding
moving-label model with one quarter of a separating finite-quotient regular
model of `Gamma`.  Then, for every `1!=g in Gamma`,

```text
liminf_n ||sigma_n(g)-1||_2 >= 1/sqrt(2),               (MMC6)
```

the fixed mark still has normalized active rank at least `1/2`, and the total
character leakage of every actor generator is at least `3/4`.  Thus adding
the faithful Hilbert--Schmidt shadow supplied on a simple surviving branch
also does not by itself choose a compatible coordinate PVM.

Consequently the torsion-normal-generator/macroscopic MF reduction removes
the sparse-rank obstruction but does **not**, by itself, remove the moving
character-label obstruction.  A literal binary-Leavitt collapse still needs
a relation which selects one globally actor-compatible coordinate lift or
authenticates transport on the selected PVM.  Positive trace of the mark,
even together with coverage of the carrier by finitely many conjugate marked
cuts, does not supply that relation.

This is a fence on the reduction, not a countermodel to the literal Leavitt
Steinberg group: the lamplighter mark does not normally generate the actor.
The additional normal-generation identities of `Delta` may be used, but a
proof must consume their occurrence semantics rather than only the rank
bounds they imply.

DERIVATION
macroscopic-mark-character-leakage-proof
