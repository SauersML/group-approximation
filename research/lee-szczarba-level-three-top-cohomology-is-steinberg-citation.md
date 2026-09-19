---
rg: 2
id: lee-szczarba-level-three-top-cohomology-is-steinberg-citation
kind: route
title: Import the duality, vanishing and top-degree statements for Γ_n(p) from Miller--Patzt--Putman, Introduction and Theorem A
target: lee-szczarba-level-three-top-cohomology-is-steinberg
requires: []
---

Literature import. The source is J. Miller, P. Patzt, A. Putman, *On the top dimensional
cohomology groups of congruence subgroups of SL_n(Z)*, arXiv:1909.02661v3 (revised 7 Jun 2020).
The PDF was fetched from arxiv.org on 2026-09-18 (swarm-0917-w11) and text-extracted.
Quotes are verbatim up to the extraction of formulas, which is rendered in plain text.

Abstract (item 1):

> Let Γn(p) be the level-p principal congruence subgroup of SLn(Z). Borel–Serre proved
> that the cohomology of Γn(p) vanishes above degree binom(n,2).

Page 2 (item 2):

> Borel–Serre [BoSe73] proved that Γn(p) is a rational duality group of dimension
> binom(n,2), which implies that H^{binom(n,2)−i}(Γn(p); Q) ≅ H_i(Γn(p); D⊗Q) for all i
> for a Γn(p)-module D called the dualizing module. This holds integrally if p ≥ 3. In
> particular, H^{binom(n,2)}(Γn(p); Q) ≅ H_0(Γn(p); D⊗Q) ≅ (D⊗Q)_{Γn(p)}, where the
> subscript indicates that we are taking coinvariants.

Pages 2--3:

> The Steinberg module for SLn(F), denoted Stn(F), is H~_{n−2}(Tn(F)). [...] and
> Borel–Serre proved that the dualizing module D for Γn(p) is Stn(Q).

Page 3 (items 4 and 5):

> the Solomon–Tits theorem [So68, Br98] also says that Stn(Fp) is a free Z-module of rank
> p^{binom(n,2)}

> For p ≤ 3, it turns out that Tn(Q)/Γn(p) ≅ Tn(Fp), so the map (1.3) is really the map to
> Stn(Fp) we discussed above.

Page 4, Theorem A (item 3):

> Theorem A. For a prime p and n ≥ 2, the map (Stn(Q))_{Γn(p)} −→ H~_{n−2}(Tn(Q)/Γn(p))
> (1.4) induced by (1.3) is a surjection. However, it is an injection if and only if p ≤ 5.

Page 3, on the history of the case used here:

> Lee–Szczarba [LeSz76] proved that this map is an isomorphism for p = 3.

The case `n = p = 3` in the claim is a direct substitution: `binom(3,2) = 3`, `3^3 = 27`.
The proofs in the source are not reproduced.
