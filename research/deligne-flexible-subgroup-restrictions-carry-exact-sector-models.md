---
rg: 2
id: deligne-flexible-subgroup-restrictions-carry-exact-sector-models
kind: claim
title: On every Deligne-flexible subgroup the nontrivial Maslov sector has exact matrix models with the canonical trace
distinct_from:
  deligne-maslov-sector-traces-are-central-regular: that classifies traces on the whole sector of Sp_4(Z); this builds exact finite models, with that limiting trace, on subgroups A whose covering class dies virtually.
  deligne-sector-siegel-spectrum-is-full-torus: that computes the spectrum of one Siegel element in every sector representation; this realises the entire restricted datum on any flexible subgroup, one element being the cyclic case.
  finite-subgroup-near-regular-has-large-regular-core: that exactifies near-regular microstates of one finite group; this produces exact twisted models of infinite subgroups from finite quotients of their covers.
---

**ESTABLISHED.** Let `Gamma=Sp_4(Z)`, let `1->C_3=<z>->E_3->Gamma->1` be Deligne's triple cover with class
`alpha in H^2(Gamma;Z/3)`, and fix `omega != 1` with `omega^3=1`. For `A <= Gamma` let `A~` be its preimage in `E_3`.
Call `A` **Deligne-flexible** if `alpha|_(A')=0` in `H^2(A';Z/3)` for some finite-index `A' <= A`. Otherwise call it
**Deligne-rigid**.

- **(F1) Criterion.** `A` is flexible iff `A~` is residually finite, iff `z` survives in some finite quotient of `A~`.
- **(F2) Exact models.** If `A` is flexible, then there are genuine unitary representations
  `rho_k : A~ -> U(D_k)` with `rho_k(z)=omega` and `tr rho_k(g) -> tau_omega(g)` for every `g in A~`. Here
  `tau_omega(z^j)=omega^j` and `tau_omega(g)=0` for `g notin <z>`: the restriction to `A~` of the central-regular
  sector trace. Amplifying and summing, every finite family `A_1,...,A_r` of flexible subgroups carries such models
  in one common dimension.
- **(F3) Examples.** Every finite, virtually free, virtually polycyclic (hence every amenable) subgroup of `Gamma` is
  flexible, and so is every subgroup that is virtually a closed surface group. So is every subgroup of
  `SL_2(Z) x SL_2(Z)`, of the Siegel parabolic, or of the Klingen parabolic (route addendum, via
  `deligne-multiplier-trivial-on-sl2xsl2-and-parabolics`).
- **(F4) Obstruction to local arguments.** Let `phi_n` be a hypothetical operator-norm model of the `omega`-sector.
  Its restriction to `A~` is an operator-norm asymptotic representation with `z -> omega` and trace limit `tau_omega`
  (`deligne-maslov-sector-traces-are-central-regular`). Suppose a property of such restricted sequences is derived
  from these facts together with finite-dimensionality: integrality of dimensions, eigenvalue multiplicities,
  determinants, invariant or eigen-vectors, or corners. Then `(rho_k)` also has that property. So no property of this
  kind, for one flexible subgroup or a finite family of them, can contradict existence. A proof that the sector is
  empty must use relations of `E_3` that generate a Deligne-rigid subgroup. The finite-index subgroups are rigid,
  because `Res_fin(E_3)=C_3` (`deligne-triple-cover-finite-residual-is-center`) lies in every finite-index subgroup
  of `E_3`, and hence in `Res_fin(A~)` whenever `[Gamma:A]` is finite.
- **Proof.** See `deligne-flexible-subgroup-exact-sector-models-proof`.

## Remarks
- **Consistent with recorded deaths.**
  - `deligne-sector-siegel-spectrum-is-full-torus` is the case `A = Z`.
  - The eigenline, invariant-vector and Kazhdan-corner certificates on `deligne-nontrivial-maslov-opnorm-sectors-are-empty`
    died at induction. (F4) shows this is forced whenever their certificate lives on a flexible subgroup.
- **Goodness.** A Serre-good group `A` (at the prime 3, degree 2) is flexible: `alpha|_A` is inflated from a finite
  quotient of `A^`, and it dies on the kernel.
  - Deligne's theorem is exactly the failure of 3-goodness of `Sp_4(Z)` in degree 2.
- **New prerequisite.** It is open whether some infinite-index subgroup of `Gamma` is Deligne-rigid. See
  `sp4-deligne-rigid-infinite-index-subgroup-exists`.
