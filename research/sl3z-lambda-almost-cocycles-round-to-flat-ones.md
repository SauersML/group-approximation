---
rg: 2
id: sl3z-lambda-almost-cocycles-round-to-flat-ones
kind: claim
title: Bounded Λ-labellings of finite SL3(Z)-sets with few non-flat relator cells are close, with small norm budget, to flat labellings
distinct_from:
  sl3z-cocompact-quotient-not-weakly-contained-in-finite-actions: that is the dynamical exclusion with marks in SL3(R)/Λ; this is a marks-free rounding statement about Λ-valued 1-cochains on Schreier complexes, which implies the exclusion
  sl3z-is-stable-in-finite-actions: that asks for weak containment of limits of almost-actions of SL3(Z); here the action on V is honest and only the Λ-labels are repaired
---

**OPEN.** Let `Γ = SL_3(Z)` with generators `S = {e_ij^(±1)}` and a finite presentation `⟨S | R⟩`. Let `Λ` be
a finitely generated subgroup of `SL_3(R)`, and write `||·||` for the operator norm. For a finite
`Γ`-set `V` and a labelling `λ : V × S → Λ`, a *relator cell* is a pair `(v, r)` with `r = s_m···s_1 ∈ R`.
It is *flat* if `λ(v_0,s_1)λ(v_1,s_2)···λ(v_(m−1),s_m) = 1`, where `v_0 = v` and `v_i = s_i v_(i−1)`. The
labelling is *flat* if every cell is flat.

**Claim (DTR).** For every finite `Σ ⊂ Λ` there is `f_Σ : (0,1] → [0,∞)` with `f_Σ(δ) → 0` as `δ → 0` such
that the following holds. Let `V` be a transitive finite `Γ`-set and `λ : V × S → Σ` a labelling with at
most `δ|V|` non-flat cells. Then there is a flat `λ' : V × S → Λ` with

```text
#{(v,s) : λ'(v,s) != λ(v,s)}  +  Σ_(λ'(v,s) != λ(v,s)) log( ||λ'(v,s)|| · ||λ'(v,s)^(−1)|| )   <=   f_Σ(δ) |V|.
```

**Why it matters.** For `Λ` satisfying (R) of `sl3z-cocompact-quotient-uniformly-far-from-finite-actions`,
DTR implies `sl3z-cocompact-quotient-not-weakly-contained-in-finite-actions`, by route
`sl3z-cocompact-exclusion-from-almost-cocycle-rounding`. Flat labellings have finite holonomy there
(Bass--Milnor--Serre), so DTR says: *a near-flat bounded labelling is near one with finite holonomy*. It
is the defect-tolerant superrigidity named in that node's Attempts, stated without marks and with the
weakest budget norm drift can use. The changed labels may be large, but only on average.

**What it is about.** Flat labellings are `Λ`-covers of the presentation complex of `V`. DTR is a
nonabelian, infinite-coefficient cosystolic-expansion statement for the Schreier 2-complexes of
`SL_3(Z)`, with a non-effective rate.

**Warning, not an argument.** `SL_3(Z)` has exponential Dehn function (Epstein--Thurston; recalled, not
imported), coming from the exponentially distorted unipotent subgroup under `SL_2(Z)`. In the universal
cover some loops of length `ℓ` need area `e^(cℓ)`. Any rounding along such loops is therefore far from
local. Whether this defeats DTR is not known.

## Attempts

* **Loeb limit and measurable superrigidity.** A counterexample sequence gives, on the ultraproduct `Z`
  of the `V_k`, a genuine cocycle `w : Γ × Z → Λ` on an ergodic (Kazhdan) Loeb space. For a group acting
  freely on a tree in place of `Λ`, Adams--Spatzier (recalled, not imported) makes `w` a coboundary, and
  internal approximation of the gauge rounds the labellings. So the tree analogue of DTR holds, with
  bounded changed labels. For `Λ <= SL_3(R)`, Zimmer's measurable superrigidity (recalled) allows `w` to be
  cohomologous in `SL_3(R)` to the identity homomorphism, and then `z ↦ φ(z)Λ` is an equivariant map
  `Z → SL_3(R)/Λ`. **Dies at:** the limit object is consistent exactly when weak containment holds, so a
  measurable limit argument cannot prove DTR. The finiteness of each `V_k` must be used before the limit,
  as norm drift uses it in `sl3z-cocompact-quotient-uniformly-far-from-finite-actions`.
* **Zooming (Ioana).** Localizing the cocycle to fibres of a nonstandard level lands on single points of
  `V_k`. There the cocycle identity fails exactly at the defects, which returns the problem unchanged
  (`sl3z-cocompact-not-factor-of-bernoulli-times-profinite`).
* **Fixed-point properties.** `Λ` acts properly on the symmetric space of `SL_3(R)`, and `Γ` acts there with
  no fixed point. So no property (T) or FH-type argument with CAT(0) coefficients can force finite
  holonomy: the obstruction has to be arithmetic (Bass--Milnor--Serre) or dynamical (norm drift).
* **Abelian flux tubes (ex3-sl3z-flux-tube).** The idea: let the labels wind at unit speed along the
  `e_13`-orbits, which are exponentially distorted under `SL_2(Z)` and cubically under the Heisenberg subgroup.
  The flux would be compensated by vortex cells inside the large fillings, heuristically at density → 0.
  By LP duality, the `ℓ¹` distance to coboundaries is `sup ⟨λ, z⟩` over real 1-cycles with `||z||_∞ <= 1`, so
  flux through `e_13`-cycles would force a cost of order `|V|`. **Dies at:**
  `sl3z-abelian-lambda-labellings-round-to-flat-ones`. When all labels lie in a torsion-free abelian subgroup,
  (T) rounds them to a coboundary within budget, so the vortex count admits no construction. A refutation of
  DTR has to use non-commuting labels, e.g. a flux tube braiding two non-commuting R-regular elements of `Λ`.
* **Short-loop torsion holonomy (ex3-sl3z-flux-tube).** If `e_12` fixes `v`, then a flat `λ'` into a torsion-free
  cocompact `Λ` has `λ'(v, e_12) = 1`, because the holonomy has finite image. So labels `λ_0 != 1` on such loops cost one
  change each. **Dies at:** growing transitive `SL_3(Z)`-sets. There every `g != 1` has a vanishing fraction of fixed
  points: a limiting invariant random subgroup is finite-index or trivial (Bekka's character rigidity, recalled),
  and by the congruence subgroup property a finite-index stabilizer on a positive fraction forces some `Γ(m)` to act
  trivially, which bounds `|V|`. Holonomy obstructions must therefore live on long loops.
* **Almost-equivariant double covers (ex3-sl3z-flux-tube).** For finite `Λ`, try labellings induced by an
  almost-equivariant 2-to-1 map `p : W → V` from an honest transitive `Γ`-set `W`. **Dies at:** (T). The graph of
  `p` is an almost-invariant vector of `ℓ²(W × V)`, so it is close to an invariant correspondence, which is the graph of an
  honest 2-to-1 equivariant map. A finite-coefficient counterexample must come from almost-actions on `V × Λ`
  that are far from every honest `Γ`-set. That is the `Z/2`-cosystolic question, and it stays open.
