import GroupApproximation.CharClass.LIXKGenChern
import GroupApproximation.CharClass.CohomologyLHRingDataOf
import GroupApproximation.CharClass.LerayHirschChartClassGenK
import GroupApproximation.CharClass.LerayHirschChartBundleGen
import GroupApproximation.Meta.AxiomGuard

/-!
# The Chern classes on the rank-`n` LIX base over a field, degreewise

Lane `lx-stepcK-local` (LIX strongest swarm, 2026-09-12; the one definition consumed by both halves
of `Gen.lemmaTwoFor_powers_of_stepC_realModP`: the top class of Step C and `γfun` of Step D).

`CharClass/LIXKGenChern.lean` defines the mod-2 classes `KGen.lixChern n dd` through the compact
Leray–Hirsch theorem.  Over a field `K` the classes are the even-part Leray–Hirsch data's
`LerayHirschDataEvenOf.chern`, with the dual tautological class `ξ = e(O(1)) = −e(O(−1))`
(`LH.tautEulerDualK`), so that the roots are the classical Chern roots and `γ_k = e_k(y)`.

**The branch condition is the Leray–Hirsch statement itself.**  `LerayHirschGraded` is a `Prop`,
so the value does not depend on which proof is chosen, and the definition neither imports nor
waits for the compact Leray–Hirsch theorem over `K`; that theorem only discharges the branch.  The
rank is pinned to `lixRank n dd`, the rank of every mapping torus; families of another rank get
the value `0`, which no consumer reads.

Consumers write
`γfun j W k := TotalHOf.of K _ (2 * k) (lixChernDegOf K n (lixDD n j) hgen W k)` and
`topClass j W := lixChernDegOf K n (lixDD n j) hgen W (lixRank n (lixDD n j))`,
so the link between the two is `rfl`.

## Main declarations

* `KGen.lixChernDegOf K n dd hgen` — **the degreewise Chern classes over `K` at rank `n`**, total.
* `KGen.lixChernDegOf_eq_of_graded` — the branch is taken, for any Leray–Hirsch proof.
* `KGen.lixChernDegOf_mappingTorus` — the same at a mapping torus.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace CharClass
namespace KGen

open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.CharClass.LH

noncomputable section

variable {ℓ : ℕ}

open scoped Classical in
/-- **The degreewise Chern classes at rank `n`, over a field `K`.**  For a projection family `P`
on `N = S¹ × S^{2n+1} × ∏ⱼ ℂP^{dⱼ}` whose projectivisation satisfies Leray–Hirsch over `K` at rank
`lixRank n dd` with the dual tautological class of the generator `hgen`, the `k`-th Chern class of
the even-part Leray–Hirsch data, read in degree `2k`; `0` otherwise. -/
def lixChernDegOf (K : Type) [Field K] (n : ℕ) (dd : Fin ℓ → ℕ)
    (hgen : Hmod K (CPtop (1 + tautCardOf (Gen.VIdx n dd ⊕ Gen.VIdx n dd))) 2) :
    LixFamily n dd → ∀ k : ℕ, Hmod K (lixN n dd) (2 * k) :=
  fun P k =>
    if h : ∃ (hc : Continuous P) (hp : ∀ p, IsStarProjection (P p)),
        LerayHirschGraded (projMapOf (⟨P, hc, hp⟩ : Bundle (↥sphereOne × Gen.baseM n dd) (Gen.VIdx n dd ⊕ Gen.VIdx n dd)))
          (LH.tautEulerDualK K hgen (⟨P, hc, hp⟩ : Bundle (↥sphereOne × Gen.baseM n dd) (Gen.VIdx n dd ⊕ Gen.VIdx n dd))) (lixRank n dd)
    then TotalHOf.component K (lixN n dd) (2 * k)
      ((LerayHirschDataEvenOf.of_graded h.choose_spec.choose_spec).chern k :
        TotalHOf K (lixN n dd))
    else 0

open scoped Classical in
/-- **The branch is taken** for every Leray–Hirsch proof `L`, and the value is the even-part
Leray–Hirsch data's Chern class of `L`. -/
theorem lixChernDegOf_eq_of_graded (K : Type) [Field K] (n : ℕ) (dd : Fin ℓ → ℕ)
    (hgen : Hmod K (CPtop (1 + tautCardOf (Gen.VIdx n dd ⊕ Gen.VIdx n dd))) 2)
    (P : LixFamily n dd) (hc : Continuous P) (hp : ∀ p, IsStarProjection (P p))
    (L : LerayHirschGraded (projMapOf (⟨P, hc, hp⟩ : Bundle (↥sphereOne × Gen.baseM n dd) (Gen.VIdx n dd ⊕ Gen.VIdx n dd)))
      (LH.tautEulerDualK K hgen (⟨P, hc, hp⟩ : Bundle (↥sphereOne × Gen.baseM n dd) (Gen.VIdx n dd ⊕ Gen.VIdx n dd))) (lixRank n dd)) (k : ℕ) :
    lixChernDegOf K n dd hgen P k
      = TotalHOf.component K (lixN n dd) (2 * k)
          ((LerayHirschDataEvenOf.of_graded L).chern k : TotalHOf K (lixN n dd)) := by
  have hex : ∃ (hc : Continuous P) (hp : ∀ p, IsStarProjection (P p)),
      LerayHirschGraded (projMapOf (⟨P, hc, hp⟩ : Bundle (↥sphereOne × Gen.baseM n dd) (Gen.VIdx n dd ⊕ Gen.VIdx n dd)))
        (LH.tautEulerDualK K hgen (⟨P, hc, hp⟩ : Bundle (↥sphereOne × Gen.baseM n dd) (Gen.VIdx n dd ⊕ Gen.VIdx n dd))) (lixRank n dd) :=
    ⟨hc, hp, L⟩
  exact dif_pos hex

/-- **The branch is taken at a mapping torus**, for every Leray–Hirsch proof at its bundle. -/
theorem lixChernDegOf_mappingTorus (K : Type) [Field K] (n : ℕ) (dd : Fin ℓ → ℕ)
    (hgen : Hmod K (CPtop (1 + tautCardOf (Gen.VIdx n dd ⊕ Gen.VIdx n dd))) 2)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (L : LerayHirschGraded (projMapOf (lixBundle n G hGc hGu))
      (LH.tautEulerDualK K hgen (lixBundle n G hGc hGu)) (lixRank n dd)) (k : ℕ) :
    lixChernDegOf K n dd hgen (mappingTorus (Gen.Vmat n) G circHoriz circHeight) k
      = TotalHOf.component K (lixN n dd) (2 * k)
          ((LerayHirschDataEvenOf.of_graded L).chern k : TotalHOf K (lixN n dd)) :=
  lixChernDegOf_eq_of_graded K n dd hgen _ (continuous_mappingTorus_lix n hGc)
    (isStarProjection_mappingTorus_lix n hGu) L k

end

/-! Audited on every build. -/

#audit_axioms KGen.lixChernDegOf_eq_of_graded
#audit_axioms KGen.lixChernDegOf_mappingTorus

end KGen
end CharClass
end GroupApproximation
