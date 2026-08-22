---
rg: 2
id: positive-range-block-extraction-recreates-maslov-microstate
kind: claim
title: Positive range-block mass extracts another central-regular Maslov microstate
distinct_from:
  deligne-maslov-sector-traces-are-central-regular: that classifies traces of already existing representations; this proves that any positive-mass central family of coordinate range blocks itself produces such a representation after polar correction.
  maslov-diverging-positive-lifts-have-vanishing-high-degree-mass: that seeks to eliminate supercritical blocks; this shows why character rigidity does not eliminate a positive-mass family of them.
---

Let `Theta:A_eta->prod_omega M_(d_n)` be a homomorphism from one fixed full
central-character fibre of the Deligne triple cover, and let
`phi_n:S_alpha->M_(d_n)` be unital positive lifts of its canonical generator
system.  Put `B_n=C^*(phi_n(S_alpha))`.  If `z_n` is any central projection
of `B_n` with

```text
lim_omega tr_(d_n)(z_n)=rho>0,                            (PBE1)
```

then the compressed generator tuple on `z_n C^(d_n)`, after an `o(1)`
normalized-HS polar correction, defines a homomorphism

```text
Theta_z:A_eta -> prod_omega M_(rank z_n).                 (PBE2)
```

Its trace is again the unique central-regular trace `tau_eta`.

In particular, taking `z_n` to be the union of irreducible range blocks of
degree `r_(n,j)>k_n` does **not** turn a positive mass of supercritical
blocks into a forbidden exact finite-dimensional Maslov-sector
representation.  It merely recreates the hypothetical central-regular
Maslov microstate on that mass.  The inequality `r_(n,j)>k_n` supplies no
coordinate exactification: Smith's lemma applies in the opposite regime
`r_(n,j)<=k_n`.  Thus finite-dimensional central invisibility and character
rigidity, without a new dimension-independent stability/correction theorem,
cannot prove `(MH1)` blockwise.
