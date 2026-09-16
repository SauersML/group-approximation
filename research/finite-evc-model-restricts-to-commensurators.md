---
rg: 2
id: finite-evc-model-restricts-to-commensurators
kind: claim
title: A finite model for E_VC G restricts to a finite model for the commensurator family of every infinite virtually cyclic subgroup
distinct_from:
  finite-evc-model-implies-fp-and-bvc: that claim derives finite presentation, type F_infinity and BVC for G itself; this claim builds, inside the given model, finite models for the Lück–Weiermann families of all commensurators N_G[C], and derives type F_infinity and finite E_FIN models for those subgroups
  groups-with-finite-evc-model-are-virtually-cyclic: that is the Juan-Pineda–Leary conjecture; this claim is an unconditional necessary condition on groups with a finite model
artifacts:
  - research/artifacts/finite-evc-commensurator-restriction-2026-09-16.md
---

**Statement.**

Let `X` be a `G`-CW model for `E_VC G` with finitely many orbits of cells, and let `C <= G` be
infinite virtually cyclic. Write `V ~ W` iff `V ∩ W` is infinite. Put:

- `N = N_G[C] = {g : gCg^{-1} ~ C}`, the commensurator;
- `G[C]`, the family of finite subgroups of `N` together with the infinite virtually cyclic
  `K <= N` with `K ~ C` (Lück–Weiermann, arXiv:math/0702646, Section 2).

Then `Y_C = {x in X : G_x ∩ C is infinite}` is an `N`-invariant subcomplex. It has at most as
many `N`-orbits of cells as `X` has `G`-orbits of cells, and it is a model for
`E_{G[C]}(N)`.

**Consequences.**

- `N` has type `F_infinity`.
- `N` admits a finite model for `E_FIN N`.
- The modular homomorphism `Δ_C : N -> Q_{>0}^×`, `g ↦ [gCg^{-1} : E]/[C : E]` for `E` of
  finite index in `gCg^{-1} ∩ C`, is either trivial or `N` surjects onto `Z`.

**Use.** This is a necessary condition on any witness for
`some-non-vc-group-has-a-finite-evc-model`, one for every commensurability class. It is also
the forward half of `finite-evc-iff-finite-efin-and-commensurator-models`.
