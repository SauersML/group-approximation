---
rg: 2
id: kt-remainder-corner-induced-characters-proof
kind: route
title: Lavi--Levit classification, then exclude finite index and central support by the corner definitions
target: kt-remainder-corner-characters-are-infinite-index-induced
requires:
  - finite-dimensional-gamma-part-of-a-model-is-compression-blind
  - tempered-gamma-part-of-a-model-is-compressor-invariant
  - model-characters-of-compressed-pairs-are-compression-invariant
---

**Components.**  `chi_g` is a tracial state of `C^*(Gamma)`, and tracial
states form a Choquet simplex, so its decomposition into extremal
characters `chi_omega` is unique.  By Lavi--Levit (`r > sr(R_+)`), each
`chi_omega = Ind_(N_omega)^Gamma sigma_omega` with `sigma_omega` finite
dimensional, `N_omega` normal, and `chi_omega = 0` off `N_omega`.

**Finite index is excluded.**  If `[Gamma : N_omega] < infinity` then
`chi_omega` is the normalized character of the finite-dimensional
representation `Ind sigma_omega`, so it is one of the countably many
finite-dimensional characters of `Gamma` (each finite-dimensional unitary
representation of `Gamma` has finite image: a virtually torsion-free image
kills a finite-index part of every root subgroup, hence contains
`E_r(R_+, I)` for a cofinite ideal, and the quotient by it is a virtually
abelian group with property (T), hence finite).  Countably many atoms of
`mu` on finite-dimensional characters would produce finite-dimensional
central summands of `pi(Gamma)'' g`, i.e. finite-dimensional
`L_Gamma`-invariant subspaces of `g L^2(N)`, contradicting `g e = 0`.  So
`mu`-a.e. `N_omega` has infinite index.

**Central support is excluded.**  If `N_omega` is central then
`chi_omega` vanishes off the finite center, so it is one of the finitely
many characters `chi_Z`, whose GNS representation is a corner of the
regular representation, hence tempered; an atom of `mu` there would give a
tempered `L_Gamma`-invariant subspace of `g L^2(N)`, contradicting
`g f = 0`.  Hence `mu`-a.e. `N_omega` is non-central, and by Vaserstein's
sandwich theorem (`r >= 3`) it contains `E_r(R_+, I_omega)` for a nonzero
ideal `I_omega`; infinite index forces `I_omega` to have infinite
colength (a cofinite `I` makes `E_r(R_+, I)` of finite index, by property
(T) as above).

**Weak mixing.**  Suppose `F` is a finite-dimensional `Gamma`-invariant
subspace of `Ind_N^Gamma sigma`, `[Gamma : N] = infinity`.  Pick a unit
vector `xi in F` and approximate it within `epsilon` by `xi_0` supported on
finitely many `N`-cosets `C_0`; then `|<h xi, xi>| <= 2 epsilon` for every
`h` outside the finite union `C = C_0 C_0^(-1) N` of `N`-cosets.  But the
representation on `F` is finite dimensional, with image dense in a compact
group `K`; the `epsilon`-returns `{h : ||h xi - xi|| < epsilon}` contain the
preimage of a neighbourhood of `1` in `K`, which meets infinitely many
`N`-cosets (the image of `N` is dense in an open subgroup `K_N`, the
finite-index subgroup `rho^(-1)(K_N)` contains infinitely many `N`-cosets,
and each of them meets the preimage of any neighbourhood of `1`).  For
small `epsilon` this is a contradiction.  So no such `F` exists.

**Non-temperedness.**  If `Ind_N^Gamma sigma` were weakly contained in
`lambda_Gamma`, restriction to `N` would give `sigma` weakly contained in a
multiple of `lambda_N`, forcing `N` amenable; but `N` contains
`E_r(R_+, I)` with `I != 0`, which contains a non-abelian free group
(`tempered-gamma-part-compressor-invariant-proof`).

**Compression invariance** of `chi_g` is (1) of
`model-characters-of-compressed-pairs-are-compression-invariant` applied to
the corner model `pi(.) g`, which is a model of the pair because `g`
commutes with `pi(Gamma)` and with every compressor.
