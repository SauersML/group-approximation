---
rg: 2
id: monster-bc-detector-lives-on-a-proper-orbit-ideal
kind: claim
title: The only known monster Baum--Connes coefficient failure is a surjectivity failure carried on a space with a proper open orbit, detected in the K-theory of the resulting compacts, which a dual-module coefficient cannot supply
distinct_from:
  monster-bc-failure-at-measured-coefficient-is-the-module-crux: that poses the open question whether the failure occurs at a measured module coefficient; this is the established structural reason it is hard -- the known detector is a proper-orbit rank that module duals lack.
  module-dual-actions-have-no-wandering-open-sets: that proves dual-module actions have no proper open orbit; this imports, from Finn-Sell/HLS/Willett--Yu, that the known monster detector is exactly such a proper-orbit invariant, so the two combine into a no-detector statement for the module route.
  module-defect-needs-non-k-exact-host: that prunes a-T-menable base groups; this describes, inside the surviving monster hosts, which coefficients are known to fail and which are known to be fine.
---

**ESTABLISHED (citation)** by `monster-bc-detector-lives-on-a-proper-orbit-ideal-citation`. Read
from Finn-Sell, *On the Baum--Connes conjecture for Gromov monster groups*, arXiv:1401.6841v2,
which recasts Higson--Lafforgue--Skandalis (HLS02) and Willett--Yu (WY12) groupoid-theoretically.

Let `Γ` be a Gromov monster: it coarsely contains a large-girth bounded-degree expander
`X ֒-> Γ`. Let `βX` be the Stone--Cech compactification, `∂βX = βX \ X` the corona, and
`Ω_(βX)`, `Ω_(∂βX)` the enveloping `Γ`-spaces of the partial translation action (Finn-Sell
Thms 3.6, 4.3).

**(1) Where the failure lives, and its sign.** *Finn-Sell Theorem 3.7.* The Baum--Connes assembly
map for `Γ` with coefficients in `C_0(Ω_(βX))` **fails to be a surjection but is an injection**.
So the known monster failure is a **surjectivity** failure, at the specific coefficient
`C_0(Ω_(βX))`.

**(2) The detector is a proper-orbit rank.** *Finn-Sell Theorem 3.8* gives the (HLS) ladder: with
`Ω_X = (X × Γ)/~`, the sequence

```text
0 -> C_0(Ω_X) ⋊_r Γ -> C_0(Ω_(βX)) ⋊_r Γ -> C_0(Ω_(∂βX)) ⋊_r Γ -> 0
```

is not exact at the middle, and the ideal `C_0(Ω_X) ⋊_r Γ ≅ C*_r(X × X) ≅ K` is the **compact
operators** of the proper pair groupoid `X × X`. The non-exactness is read in

```text
K_0(K) = Z -> K_0(C*_r G(X)) -> K_0(C*_r G(X)|_(∂βX)),
```

i.e. the defect is the ghost class in `K_0(K) = Z`, the **rank at infinity** along the proper
orbit. This is the detector.

**(3) Boundary coefficients are fine.** *Finn-Sell Corollary 4.4.* Because a large-girth expander
is a-T-menable at infinity (Prop 4.2, FSW14) the boundary groupoid `Ω_(∂βX) ⋊ Γ` is a-T-menable
(Thm 4.3), so by Tu the assembly map for `Γ` is an **isomorphism** with coefficients in **any**
`(Ω_(∂βX) ⋊ Γ)`-C*-algebra. The corona coefficients carry no failure.

**Consequence for the module route
(`some-nonexact-group-has-a-k-inexact-module-triple`).**
- The single known coefficient failure of a monster is glued to a **proper open orbit** `X × X`,
  whose crossed product is the compacts, and is detected by the integer rank
  `K_0(K) = Z`. A dual-module coefficient `C(V^)` has **no proper open orbit** and its ideal is
  never the compacts (`module-dual-actions-have-no-wandering-open-sets`; the faithful Haar trace
  charges every projection of `C(V^) ⋊_r Γ`). So the HLS/Finn-Sell detector is structurally
  unavailable there.
- `C(V^)` is **neither** the failing coefficient `C_0(Ω_(βX))` **nor** an `Ω_(∂βX)`-algebra, so
  Finn-Sell settles the module case in neither direction. The route therefore needs a coefficient
  failure produced by a mechanism **absent from HLS/WY/Finn-Sell**: a non-proper-orbit,
  non-tracial K-theory detector on a compact measured system. That missing detector is exactly the
  gap named in `monster-bc-failure-at-measured-coefficient-is-the-module-crux`.

**Model test.** For an exact (or a-T-menable) `Γ` there is no coarsely embedded expander, the
ladder degenerates, `K_0(K) -> ...` is exact, and no defect exists -- consistent with
`module-defect-needs-non-k-exact-host`.
