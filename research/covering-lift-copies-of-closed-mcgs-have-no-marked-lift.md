---
rg: 2
id: covering-lift-copies-of-closed-mcgs-have-no-marked-lift
kind: claim
title: For genus at least three a covering-lift copy of a finite-index subgroup of a closed-surface mapping class group, in particular any same-genus copy, has no lift to the once-marked mapping class group
distinct_from:
  closed-mcgs-have-no-covering-lift-to-marked-covers: that assumes each marked class has a representative covering a representative of the guest element, relative to the marked points; this assumes only that the forgotten class does, so the marked class may be any of its point-pushing translates, and it also covers genus three.
  genus-three-mcg-has-no-covering-lift-to-marked-covers: that is the genus-three case with covering representatives relative to the marked points; this drops that requirement in every genus at least three.
  outer-covering-lifts-are-virtual-sections: that is the general equivalence between covering lifts and virtual sections; this applies its algebraic form after correcting each marked class along the track of an isotopy.
---

**ESTABLISHED (genus 3 depends on the unreviewed genus-three non-splitting).**
Let `Σ` be a closed orientable surface of genus `g ≥ 3` and `L ≤ Mod(Σ)` a
finite-index subgroup. Write `p: Mod(X, ∗) → Mod(X)` for forgetting a marked
point `∗`.

**(a) Covering lifts have no marked lift.** Let `π: Σ̃ → Σ` be a finite
unbranched covering by a connected surface, and `∗ ∈ Σ̃`. There is no
homomorphism `ρ_1: L → Mod(Σ̃, ∗)` with the following property: for every
`f ∈ L`, the class `p(ρ_1(f)) ∈ Mod(Σ̃)` has a representative `F` covering some
representative `f′` of `f`, that is `π∘F = f′∘π`.

`ρ_1` is not assumed injective. Only the forgotten class is assumed to be a
covering lift. The marked class `ρ_1(f)` need not have a covering representative
fixing `∗`.

**(b) Same genus.** No injective homomorphism `ρ_0: L → Mod(S_g)` has a lift
`ρ_1: L → Mod(S_g, ∗)` with `p∘ρ_1 = ρ_0`.

**Conjugated covering lifts are included.** Suppose `ρ_0(f) = φ κ(f) φ^-1`,
where `κ(f)` has a representative `F̂` covering a representative `f′` of `f` for
a covering `π̂: Σ̂ → Σ`, and `φ` is the class of a homeomorphism `Φ: Σ̂ → Σ̃`.
Then `Φ F̂ Φ^-1` represents `ρ_0(f)` and covers `f′` for the covering
`π̂∘Φ^-1`. So (a) applies.

**Consequences.**
- (a) implies `closed-mcgs-have-no-covering-lift-to-marked-covers` and
  `genus-three-mcg-has-no-covering-lift-to-marked-covers`. Pass to the
  finite-index subgroup fixing one marked point `p̃ ∈ P`, then forget the other
  marked points.
- **For the target hole.** In the dichotomy `closed-mcg-punctured-host-forgetful-dichotomy`,
  shape A cannot occur with `h = g`, nor with `ρ′_0` a covering lift up to
  conjugation. What survives of shape A is an injection into `Mod(S_h)` with
  `h > g` that is not conjugate to a covering lift, together with a marked lift.

**Scope.**
- **Unbranched covers only.** Branched covers are not treated.
- **Genus 3.** The genus-3 case uses
  `birman-sequence-genus-three-does-not-virtually-split`, which is not
  independently reviewed.
- **Injections not of covering type.** Aramayona--Leininger--Souto
  (arXiv:0811.0841v1, abstract) construct injections between mapping class
  groups of different closed surfaces. Whether they are covering lifts in the
  sense of (a), and whether they have marked lifts, was not examined.

The derivation is `covering-lift-copies-no-marked-lift-proof`.
