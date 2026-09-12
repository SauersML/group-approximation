import GroupApproximation.CharClass.LIXKGenOfFibreThom
import GroupApproximation.CharClass.LerayHirschCompactClosedOf
import GroupApproximation.Meta.AxiomGuard

/-!
# The Leray–Hirsch inputs of the local computation over a field, discharged

Lane `lx-stepcK-local` (LIX strongest swarm, 2026-09-12).

`CharClass/LIXKGenOfFibreThom.lean` proves the local computation `KGenLocalNonzeroOf` over a field
for a class with unit top Thom coordinate, over three Leray–Hirsch inputs: Leray–Hirsch upstairs,
over the projectivised sum `P(W ⊕ 1)` of the mapping torus, Leray–Hirsch over the singleton at each
zero, and the compatibility of their generators.  Lane `lx-lhK-b`'s compact Leray–Hirsch over a
field (`LH.lerayHirschGraded_compactDualOf`) holds over every compact nonempty base, so each input
is a theorem; the generators' compatibility is naturality of the dual tautological class
(`LH.tautEulerDual_comapOf`), because the inclusion of a restricted projectivisation is a base
change (`projInclOn_eq_projComap`).

What remains of the local computation is the statement about `u` itself: its top coordinate at the
Leray–Hirsch statement `lixLHplusDualOf` is the unit.

## Main declarations

* `KGen.lixLHplusDualOf` — Leray–Hirsch upstairs over `K`.
* `KGen.lixLHptDualOf`, `KGen.lixPtDual_hξ` — over the singleton at each zero, and compatibility.
* `KGen.kGenLocalNonzeroOf_of_top_closed` — **the local computation over `K` from `htop` alone.**
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace KGen

open scoped Matrix
open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.CharClass.LH
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

variable {ℓ : ℕ}

instance instCompactSpaceLixKPtSet (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) :
    CompactSpace ↥(lixKPtSet n k dd i) :=
  isCompact_iff_compactSpace.mp isCompact_singleton

/-- **Leray–Hirsch upstairs over a field**, for the projectivised sum of the mapping torus, with the
dual tautological class of any nonzero generator. -/
theorem lixLHplusDualOf (K : Type) [Field K] (n : ℕ) {dd : Fin ℓ → ℕ}
    (hgen : Hmod K (CPtop (1 + tautCardOf ((Gen.VIdx n dd ⊕ Gen.VIdx n dd) ⊕ Unit))) 2)
    (hgen0 : hgen ≠ 0)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    LerayHirschGraded (projMapOf (lixBundle n G hGc hGu).plusOne)
      (LH.tautEulerDualK K hgen (lixBundle n G hGc hGu).plusOne) (lixRank n dd + 1) :=
  LH.lerayHirschGraded_compactDualOf K (lixBundle n G hGc hGu).plusOne (lixRank n dd + 1)
    (fun x => by rw [Bundle.rank_plusOne, rank_lixBundle]) (Nat.succ_le_succ (Nat.zero_le _))
    hgen hgen0

/-- **Leray–Hirsch over the singleton at the `i`-th zero, over a field.** -/
theorem lixLHptDualOf (K : Type) [Field K] (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    (hgen : Hmod K (CPtop (1 + tautCardOf ((Gen.VIdx n dd ⊕ Gen.VIdx n dd) ⊕ Unit))) 2)
    (hgen0 : hgen ≠ 0)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    LerayHirschGraded
      (projMapOf ((lixBundle n G hGc hGu).restrictTo (lixKPtSet n k dd i)).plusOne)
      (LH.tautEulerDualK K hgen ((lixBundle n G hGc hGu).restrictTo (lixKPtSet n k dd i)).plusOne)
      (lixRank n dd + 1) :=
  LH.lerayHirschGraded_compactDualOf K
    ((lixBundle n G hGc hGu).restrictTo (lixKPtSet n k dd i)).plusOne (lixRank n dd + 1)
    (fun x => by
      rw [Bundle.rank_plusOne]
      exact rank_lixBundle n G hGc hGu (x : ↥sphereOne × Gen.baseM n dd) ▸ rfl)
    (Nat.succ_le_succ (Nat.zero_le _)) hgen hgen0

/-- **The generators are compatible**: the dual tautological class of the restricted projectivised
sum is the pullback of the dual tautological class. -/
theorem lixPtDual_hξ (K : Type) [Field K] (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    (hgen : Hmod K (CPtop (1 + tautCardOf ((Gen.VIdx n dd ⊕ Gen.VIdx n dd) ⊕ Unit))) 2)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    pull (cmap (Bundle.projInclOn (lixBundle n G hGc hGu).plusOne (lixKPtSet n k dd i))) 2
        (LH.tautEulerDualK K hgen (lixBundle n G hGc hGu).plusOne)
      = LH.tautEulerDualK K hgen ((lixBundle n G hGc hGu).restrictTo (lixKPtSet n k dd i)).plusOne :=
  LH.tautEulerDual_comapOf K hgen
    (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(lixKPtSet n k dd i), ↥sphereOne × Gen.baseM n dd))
    (lixBundle n G hGc hGu).plusOne

/-- **The local computation over a field at rank `n`, from the top coordinate alone.**  Every
Leray–Hirsch input is discharged; the only hypothesis is that the top Thom coordinate of `u`, at
`lixLHplusDualOf`, is the unit of `H^0`. -/
theorem kGenLocalNonzeroOf_of_top_closed (K : Type) [Field K] (n k : ℕ) {dd : Fin ℓ → ℕ}
    (hgen : Hmod K (CPtop (1 + tautCardOf ((Gen.VIdx n dd ⊕ Gen.VIdx n dd) ⊕ Unit))) 2)
    (hgen0 : hgen ≠ 0)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0)
    (u : relCohomology K (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu)
      (2 * lixRank n dd))
    (h : (0 : ℕ) = 2 * lixRank n dd - 2 * ((Fin.last (lixRank n dd) : Fin (lixRank n dd + 1)) : ℕ))
    (htop : ThomChernDeg.thomJmTotalOf K (lixBundle n G hGc hGu)
        (lixLHplusDualOf K n hgen hgen0 hGc hGu) u (Fin.last (lixRank n dd))
      = cohCast h (one (K := K) (lixN n dd))) :
    KGenLocalNonzeroOf K n k hGc hGu hGe u :=
  kGenLocalNonzeroOf_of_top K n k hGc hGu hGe
    (fun i => LH.tautEulerDualK K hgen ((lixBundle n G hGc hGu).restrictTo (lixKPtSet n k dd i)).plusOne)
    (fun i => lixPtDual_hξ K n k dd i hgen hGc hGu)
    (lixLHplusDualOf K n hgen hgen0 hGc hGu)
    (fun i => lixLHptDualOf K n k dd i hgen hgen0 hGc hGu) u h htop

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.lixLHplusDualOf
#audit_axioms KGen.lixLHptDualOf
#audit_axioms KGen.lixPtDual_hξ
#audit_axioms KGen.kGenLocalNonzeroOf_of_top_closed

end GroupApproximation.CharClass
