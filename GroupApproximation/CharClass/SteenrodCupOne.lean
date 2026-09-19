import GroupApproximation.CharClass.SteenrodCoboundary
import GroupApproximation.CharClass.SteenrodCupEdge
import GroupApproximation.CharClass.CohomologyAssoc

/-!
# The cup-1 coboundary formula and graded commutativity of the cup product

This is the fleet's blocker: `cc-cohom-api`'s `CohomologyBasic.lean` records that
graded commutativity `a ⌣ b = cohCast _ (b ⌣ a)` cannot be produced from the
Alexander–Whitney cup product alone, and asks for it either from the
acyclic-models Cartan machinery (`cc-cartan`) or from a cup-1 argument. This file
supplies the cup-1 argument, so nothing downstream needs to wait on
acyclic models.

## The formula

`SteenrodCoboundary.lean`'s `cochainCupI_coboundary`, read at `i = 0`, **is**
Steenrod's cup-1 coboundary formula (every term at a literal degree, no cast):

```text
δ(α ⌣₁ β) = δα ⌣₁ β + α ⌣₁ δβ + α ⌣₀ β + β ⌣₀ α        (⌣₁ := cochainCupI 1, ⌣₀ = ⌣)
```

For cocycles `α, β` (`δα = δβ = 0`) the first two terms vanish
(`cochainCupI_coboundary_cocycle`), leaving `α ⌣ β + β ⌣ α` as a coboundary. Since
`cochainCupI`'s output degree is a free parameter (`SteenrodCut.lean`'s design),
this cancellation is available at *every* literal degree simultaneously with
`cochainCup`'s own degree bookkeeping, which is what lets the descent to
cohomology (`cup_comm`) avoid ever proving an equality of cochains that isn't
literally true.

## Degree-0 boundary case

The cup-1 argument needs one degree of room (`n + 1 = p + q` for the cup-1's
output degree `n`), so it says nothing when `p = q = 0`. There
`cochainCupI_zero_zero_comm` gives commutativity directly: the only `1`-cut of a
`0`-simplex uses the whole (one-point) vertex set for *both* families
(`cutIndex_self`, `cutU_univ`, `cutV_univ` of `SteenrodCupEdge.lean`), so the cup
product is literally `α(σ) * β(σ)`, commutative because `ZMod 2` is a
`CommRing`.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial SimplexCategory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation
namespace CharClass

noncomputable section

/-! ## 1. Additivity of `cocycleClass` -/

/-- **`cocycleClass` is additive.** Not recorded in the vendored tree; proved
here by injectivity of `iCycles` (a mono) reducing to the additivity of
`iCycles.hom` composed with the already-proven computation rule
`iCycles_cyclesMk`. -/
theorem cocycleClass_add (X : TopCat.{0}) (n : ℕ)
    (φ ψ : singularCochainGroup (ZMod 2) X n)
    (hφ : cochainCoboundary (ZMod 2) X n φ = 0) (hψ : cochainCoboundary (ZMod 2) X n ψ = 0)
    (hφψ : cochainCoboundary (ZMod 2) X n (φ + ψ) = 0) :
    cocycleClass X n (φ + ψ) hφψ = cocycleClass X n φ hφ + cocycleClass X n ψ hψ := by
  unfold cocycleClass
  rw [← map_add]
  refine congrArg (fun c => ((cochainCxZMod2 X).homologyπ n).hom c) ?_
  apply (ModuleCat.mono_iff_injective ((cochainCxZMod2 X).iCycles n)).1 inferInstance
  simp only [map_add, iCycles_cyclesMk]
  rfl

/-! ## 2. The cup-1 coboundary formula, specialized to cocycles -/

/-- **`cochainCupI 0 a b n` is a cocycle at every literal degree `n`**, for any
cocycle inputs — not just at `n = a + b`. This is the Leibniz case
(`cochainCupI_coboundary_zero`) of `SteenrodCoboundary.lean` with the two
derivative terms killed by `cochainCupI_zero_left` / `cochainCupI_zero_right`. -/
theorem cochainCupI_zero_cocycle {X : TopCat.{0}} (a b n : ℕ)
    (α : singularCochainGroup (ZMod 2) X a) (hα : cochainCoboundary (ZMod 2) X a α = 0)
    (β : singularCochainGroup (ZMod 2) X b) (hβ : cochainCoboundary (ZMod 2) X b β = 0) :
    cochainCoboundary (ZMod 2) X n (cochainCupI 0 a b n α β) = 0 := by
  rw [cochainCupI_coboundary_zero, hα, hβ, cochainCupI_zero_left, cochainCupI_zero_right, add_zero]

/-- **Steenrod's cup-1 coboundary formula for cocycles**, at every literal degree
`n` simultaneously: `δ(α ⌣₁ β) = α ⌣ β + β ⌣ α`, with both low terms written as
`cochainCupI 0 · · (n+1)` (no cast — `cochainCupI_zero` identifies either of them
with the Alexander–Whitney `cochainCup` once its own degree is literally
`a + b`). -/
theorem cochainCupI_coboundary_cocycle {X : TopCat.{0}} (p q n : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p) (hφ : cochainCoboundary (ZMod 2) X p φ = 0)
    (ψ : singularCochainGroup (ZMod 2) X q) (hψ : cochainCoboundary (ZMod 2) X q ψ = 0) :
    cochainCoboundary (ZMod 2) X n (cochainCupI 1 p q n φ ψ)
      = cochainCupI 0 p q (n + 1) φ ψ + cochainCupI 0 q p (n + 1) ψ φ := by
  have h := cochainCupI_coboundary 0 p q n φ ψ
  rw [hφ, hψ, cochainCupI_zero_left, cochainCupI_zero_right] at h
  simp only [zero_add] at h
  exact h

/-! ## 3. Relabelling a literal-degree `cochainCupI` cast -/

/-- **A cast `cochainCup` is a `cochainCupI 0 · · ·` at the target degree.** Since
`cochainCupI`'s output degree is a free parameter, casting `cochainCup a b φ ψ`
along any proof that its degree `a + b` equals `n` is the *same term* as
`cochainCupI 0 a b n φ ψ` — proved by `subst`, reducing both sides to the
degree-`a+b` literal case (`cochainCast_rfl`, `cochainCupI_zero`). -/
theorem cochainCast_cochainCupI_zero {X : TopCat.{0}} (a b n : ℕ) (h : a + b = n)
    (φ : singularCochainGroup (ZMod 2) X a) (ψ : singularCochainGroup (ZMod 2) X b) :
    cochainCast h (cochainCup a b φ ψ) = cochainCupI 0 a b n φ ψ := by
  subst h
  rw [cochainCast_rfl]
  exact (cochainCupI_zero a b φ ψ).symm

/-! ## 4. Degree-equality casts of cohomology classes are proof-irrelevant -/

namespace Steenrod

/-- Two casts of the same class along (possibly different) proofs of the same
degree equation agree, by proof irrelevance of the equation.  Lane-local: the
`cohCast` calculus proper belongs to `cc-cohom-api`. -/
theorem cohCast_congr_proof {X : TopCat.{0}} {m m' : ℕ} (h h' : m = m') (a : Hmod2 X m) :
    cohCast h a = cohCast h' a := by
  rw [Subsingleton.elim h h']

/-- Casting out along `h` and back along a *different* route `h'` to the same
target as a third proof `h''` agrees with casting directly along `h''`. -/
theorem cohCast_trans_congr {X : TopCat.{0}} {m k m' : ℕ} (h : m = k) (h' : k = m')
    (h'' : m = m') (a : Hmod2 X m) :
    cohCast h' (cohCast h a) = cohCast h'' a := by
  rw [cohCast_cohCast]

end Steenrod

/-! ## 5. Characteristic two -/

/-- **In a mod-2 cohomology group, `x + y = 0` forces `x = y`.** -/
theorem eq_of_add_eq_zero_hmod2 {X : TopCat.{0}} {m : ℕ} (x y : Hmod2 X m) (h : x + y = 0) :
    x = y := by
  have h2 : x + x = 0 := by
    have h20 : (2 : ZMod 2) = 0 := by decide
    rw [← two_smul (ZMod 2) x, h20, zero_smul]
  calc x = x + 0 := (add_zero x).symm
    _ = x + (x + y) := by rw [h]
    _ = (x + x) + y := by rw [add_assoc]
    _ = 0 + y := by rw [h2]
    _ = y := zero_add y

/-! ## 6. The degree-0 boundary case -/

/-- **The bidegree-`(0,0)` cup product is commutative on the nose.** The only
`1`-cut of a `0`-simplex is the whole vertex set, used for *both* alternating
families, so both orders of `cochainCupI 0 0 0 0` evaluate to the same product
of two `ZMod 2` values in opposite order — equal since `ZMod 2` is commutative. -/
theorem cochainCupI_zero_zero_comm {X : TopCat.{0}}
    (φ ψ : singularCochainGroup (ZMod 2) X 0) :
    cochainCupI 0 0 0 0 φ ψ = cochainCupI 0 0 0 0 ψ φ := by
  apply cochain_ext
  intro τ
  rw [cochainCupI_eval, cochainCupI_eval, cutIndex_self, Finset.sum_singleton,
    Finset.sum_singleton, cutU_univ, cutV_univ]
  exact mul_comm _ _

/-! ## 7. Graded commutativity -/

/-- **Graded commutativity of the mod-2 cup product.** The fleet's blocker: with
this, `⨁ n, Hmod2 X n` can carry a genuine (graded-)commutative ring structure
without waiting on the acyclic-models Cartan formula. -/
theorem cup_comm {X : TopCat.{0}} {p q : ℕ} (a : Hmod2 X p) (b : Hmod2 X q) :
    cup a b = cohCast (Nat.add_comm q p) (cup b a) := by
  rcases Nat.eq_zero_or_pos (p + q) with h0 | hpos
  · -- Degenerate case: p = q = 0.
    have hp : p = 0 := by omega
    have hq : q = 0 := by omega
    subst hp
    subst hq
    obtain ⟨φ, hφ, rfl⟩ := exists_cocycle a
    obtain ⟨ψ, hψ, rfl⟩ := exists_cocycle b
    have hcomm : cochainCup 0 0 φ ψ = cochainCup 0 0 ψ φ := by
      rw [← cochainCupI_zero 0 0 φ ψ, ← cochainCupI_zero 0 0 ψ φ]
      exact cochainCupI_zero_zero_comm φ ψ
    rw [cup_mk, cup_mk, Steenrod.cohCast_congr_proof (Nat.add_comm 0 0) rfl, cohCast_rfl]
    exact cocycleClass_congr X 0 hcomm _ _
  · -- General case: p + q ≥ 1, via cup-1.
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have hn' : q + p = n + 1 := (Nat.add_comm q p).trans hn
    obtain ⟨φ, hφ, rfl⟩ := exists_cocycle a
    obtain ⟨ψ, hψ, rfl⟩ := exists_cocycle b
    have hδμ : cochainCoboundary (ZMod 2) X n (cochainCupI 1 p q n φ ψ)
        = cochainCupI 0 p q (n + 1) φ ψ + cochainCupI 0 q p (n + 1) ψ φ :=
      cochainCupI_coboundary_cocycle p q n φ hφ ψ hψ
    have h1' : cochainCoboundary (ZMod 2) X (n + 1) (cochainCupI 0 p q (n + 1) φ ψ) = 0 :=
      cochainCupI_zero_cocycle p q (n + 1) φ hφ ψ hψ
    have h2' : cochainCoboundary (ZMod 2) X (n + 1) (cochainCupI 0 q p (n + 1) ψ φ) = 0 :=
      cochainCupI_zero_cocycle q p (n + 1) ψ hψ φ hφ
    have hsum : cochainCoboundary (ZMod 2) X (n + 1)
        (cochainCupI 0 p q (n + 1) φ ψ + cochainCupI 0 q p (n + 1) ψ φ) = 0 := by
      rw [← hδμ]
      exact cochainCoboundary_cochainCoboundary X n (cochainCupI 1 p q n φ ψ)
    have hzero : cocycleClass X (n + 1)
        (cochainCupI 0 p q (n + 1) φ ψ + cochainCupI 0 q p (n + 1) ψ φ) hsum = 0 := by
      have step1 := cocycleClass_coboundary_zero X n (cochainCupI 1 p q n φ ψ)
        (cochainCoboundary_cochainCoboundary X n (cochainCupI 1 p q n φ ψ))
      rwa [cocycleClass_congr X (n + 1) hδμ
        (cochainCoboundary_cochainCoboundary X n (cochainCupI 1 p q n φ ψ)) hsum] at step1
    have hadd := cocycleClass_add X (n + 1) (cochainCupI 0 p q (n + 1) φ ψ)
      (cochainCupI 0 q p (n + 1) ψ φ) h1' h2' hsum
    rw [hadd] at hzero
    have e1 : cochainCast hn (cochainCup p q φ ψ) = cochainCupI 0 p q (n + 1) φ ψ :=
      cochainCast_cochainCupI_zero p q (n + 1) hn φ ψ
    have e2 : cochainCast hn' (cochainCup q p ψ φ) = cochainCupI 0 q p (n + 1) ψ φ :=
      cochainCast_cochainCupI_zero q p (n + 1) hn' ψ φ
    have hpq : cochainCoboundary (ZMod 2) X (p + q) (cochainCup p q φ ψ) = 0 :=
      cochainCupZMod2_respects_cocycles p q φ ψ hφ hψ
    have hqp : cochainCoboundary (ZMod 2) X (q + p) (cochainCup q p ψ φ) = 0 :=
      cochainCupZMod2_respects_cocycles q p ψ φ hψ hφ
    have hcast1 : cochainCoboundary (ZMod 2) X (n + 1) (cochainCast hn (cochainCup p q φ ψ))
        = 0 := by
      rw [e1]; exact h1'
    have hcast2 : cochainCoboundary (ZMod 2) X (n + 1) (cochainCast hn' (cochainCup q p ψ φ))
        = 0 := by
      rw [e2]; exact h2'
    have hzero' : cohCast hn (cup (cocycleClass X p φ hφ) (cocycleClass X q ψ hψ))
        + cohCast hn' (cup (cocycleClass X q ψ hψ) (cocycleClass X p φ hφ)) = 0 := by
      rw [cup_mk, cup_mk, cohCast_cocycleClass hn (cochainCup p q φ ψ) hpq hcast1,
        cohCast_cocycleClass hn' (cochainCup q p ψ φ) hqp hcast2,
        cocycleClass_congr X (n + 1) e1 hcast1 h1',
        cocycleClass_congr X (n + 1) e2 hcast2 h2']
      exact hzero
    have hfin : cup (cocycleClass X p φ hφ) (cocycleClass X q ψ hψ)
        + cohCast (Nat.add_comm q p)
            (cup (cocycleClass X q ψ hψ) (cocycleClass X p φ hφ)) = 0 := by
      have hcong := congrArg (cohCast hn.symm) hzero'
      rw [cohCast_add, cohCast_zero, cohCast_symm_cohCast hn,
        Steenrod.cohCast_trans_congr hn' hn.symm (Nat.add_comm q p)] at hcong
      exact hcong
    exact eq_of_add_eq_zero_hmod2 _ _ hfin

end

end CharClass
end GroupApproximation
