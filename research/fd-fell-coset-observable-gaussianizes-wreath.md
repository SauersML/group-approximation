---
rg: 2
id: fd-fell-coset-observable-gaussianizes-wreath
kind: claim
title: Finite-dimensional Fell models of one coset coefficient make the binary coset wreath hyperlinear
distinct_from:
  mihailova-coset-wreath-sofic-action-boundary: that uses finite permutation charts for the entire set action and GKP permanence; this uses only one positive-definite coset coefficient and Gaussianizes it, with no invariant branch or finite set-action chart.
  orbitwise-relator-classicalization-separates-mihailova-kernel: that assumes exact relator triviality on a finite observable orbit and forces subgroup separability; here N fixes the finite-dimensional vector only asymptotically, which is enough for HS microstates but need not yield any finite-index subgroup containing N.
  mihailova-actor-liftable-ce-forces-q-hyperlinear: that extracts finite-dimensional coefficients from a pre-existing Connes embedding; this runs in the constructive direction, turning such coefficients into a Connes embedding of the coset wreath.
---

Let `N<L` and put

```text
W_N=(direct_sum_(L/N) C_2) rtimes L.                   (FDC1)
```

Assume `L` is hyperlinear and there are finite-dimensional real orthogonal
representations `rho_j:L->O(V_j)` with unit vectors `xi_j` such that

```text
<rho_j(g)xi_j,xi_j> -> 1_(g in N)       (g in L).      (FDC2)
```

If each `rho_j(L)` is finite, then `W_N` is hyperlinear.  Equivalently, the
cyclic quasi-regular coefficient of `L curvearrowright L/N` being a Fell
limit of finite-image finite-dimensional coefficients is a sufficient
observable for canonical Hilbert--Schmidt models of the wreath.

For `L=SL_3(Z)`, finite image is automatic for every finite-dimensional
orthogonal representation by higher-rank superrigidity.  Thus `(FDC2)` is a
strictly smaller constructive target than a sofic action chart: it remembers
only the Gram matrices of finitely many cosets, and asks for no finite branch
on which `N` acts exactly.

This condition genuinely does not encode subgroup separability.  If
`E=F_m` surjects onto a finitely generated infinite simple amenable group
`Q` and `N=ker(E->Q)`, permutation microstates of the sofic group `Q` assign finite
permutations freely to the generators of `E`.  They give exact finite-image
representations of `E` whose cyclic coefficients converge to `1_N`.  Yet
`N` is not separable in `E`, since separability of the normal subgroup would
make `Q` residually finite.  Hence no invariant defect-free branch is hidden
in `(FDC2)`.

For the isolated Mihailova subgroup `N<F_m<SL_3(Z)`, whether `(FDC2)` holds
for representations of the **ambient** `SL_3(Z)` remains open.  Finite normal
generation of `N` inside `F_m` supplies no induction theorem preserving
finite dimensionality, and the sparse-orbit counterpacket supplies only
free-actor permutations, not ambient lattice representations.  This is the
strictly weaker finite-observable boundary left after action soficity.
