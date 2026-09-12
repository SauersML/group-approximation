import GroupApproximation.CharClass.OddPTopPower
import GroupApproximation.CharClass.OddPTotalProducer

/-!
# The top power in the cohomology ring: `UnitZeroOddP` and `TopTwoOddP`

Two of the named inputs of `OddPTotal.totalReducedPowersOddP` (lx-pzero's producer), from the
cochain-level top power `oddDClass_zero` of `OddPTopPower.lean`:

* `unitZeroOddP` — `[D₀ 1] = 1` in `H^0`;
* `topTwoOddP` — `[D₀ h] = h^p` on every degree-two class, as elements of `TotalHOf (ZMod p) X`.

The bridge is the class-level cup power `cupPowK x r ∈ H^{q r}` (left-nested, like the cochain power
`cupPowQ`), for which `(of q x)^r = of (q r) (cupPowK x r)` holds by `of_mul` with no cast, and the
degree identification `p q − 0 = q p` of `oddDClass_zero`, which `of` absorbs (`of_cocycleClassK_cast`).
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

namespace TopPow

section Ring

variable (K : Type) [CommRing K] (X : TopCat.{0})

/-- **The class-level cup power** `x^{⌣r} ∈ H^{q r}(X; K)`, left-nested. -/
def cupPowK {q : ℕ} (x : Hmod K X q) : (r : ℕ) → Hmod K X (q * r)
  | 0 => one (K := K) X
  | r + 1 => cup (cupPowK x r) x

/-- **Powers in the cohomology ring are cup powers.** -/
theorem of_pow {q : ℕ} (x : Hmod K X q) (r : ℕ) :
    TotalHOf.of K X q x ^ r = TotalHOf.of K X (q * r) (cupPowK K X x r) := by
  induction r with
  | zero =>
    rw [pow_zero]
    exact (TotalHOf.of_one K X).symm
  | succ r ih =>
    rw [pow_succ, ih, ← TotalHOf.of_mul]
    rfl

/-- The cup power of a class is the class of the cochain cup power. -/
theorem cupPowK_mk {q : ℕ} (u : singularCochainGroup K X q) (hu : cochainCoboundary K X q u = 0) :
    ∀ r : ℕ, cupPowK K X (cocycleClassK K X q u hu) r
      = cocycleClassK K X (q * r) (cupPowQ K X u r) (cupPowQ_cocycle K X u hu r)
  | 0 => rfl
  | r + 1 => by
    show cup (cupPowK K X (cocycleClassK K X q u hu) r) (cocycleClassK K X q u hu) = _
    rw [cupPowK_mk u hu r]
    exact cup_mkOf _ _ u hu

/-- `of` does not see a degree cast of the representing cocycle. -/
theorem of_cocycleClassK_cast {m m' : ℕ} (h : m = m') (φ : singularCochainGroup K X m)
    (hφ : cochainCoboundary K X m φ = 0) (hφ' : cochainCoboundary K X m' (cochainCast h φ) = 0) :
    TotalHOf.of K X m' (cocycleClassK K X m' (cochainCast h φ) hφ')
      = TotalHOf.of K X m (cocycleClassK K X m φ hφ) := by
  subst h
  have hid : cochainCast (rfl : m = m) φ = φ := by
    unfold cochainCast
    rw [eqToHom_refl, Category.id_comp]
  rw [cocycleClassK_congr K X m hid hφ' hφ]

end Ring

/-! ## The two producers -/

section Producers

variable (p : ℕ) [Fact p.Prime] (hp : Odd p)

/-- **`[D₀ h] = h^p` on degree-two classes**, the field `top_two` of the reduced powers. -/
theorem topTwoOddP : OddPTotal.TopTwoOddP p hp := by
  intro X h
  obtain ⟨u, hu, rfl⟩ := cocycleClassK_surjective (ZMod p) X 2 h
  rw [OddPTotal.oddDAdd_apply p hp X 2 0 (Nat.zero_le _), oddDClass_zero p hp u hu,
    of_cocycleClassK_cast (ZMod p) X (topPow_deg p 2) _ (cupPowQ_cocycle (ZMod p) X u hu p),
    of_pow, cupPowK_mk]

/-- **`[D₀ 1] = 1`**, the field `unit_zero` of the reduced powers. -/
theorem unitZeroOddP : OddPTotal.UnitZeroOddP p hp := by
  intro X
  have hone : one (K := ZMod p) X
      = cocycleClassK (ZMod p) X 0 cochainOne (cochainCoboundary_cochainOneK (ZMod p) X) := rfl
  rw [OddPTotal.oddDAdd_apply p hp X 0 0 (Nat.zero_le _), hone,
    oddDClass_zero p hp cochainOne (cochainCoboundary_cochainOneK (ZMod p) X),
    of_cocycleClassK_cast (ZMod p) X (topPow_deg p 0) _
      (cupPowQ_cocycle (ZMod p) X cochainOne (cochainCoboundary_cochainOneK (ZMod p) X) p),
    ← cupPowK_mk, ← of_pow, ← hone, TotalHOf.of_one, one_pow]

#audit_axioms topTwoOddP
#audit_axioms unitZeroOddP

end Producers

end TopPow

end

end GroupApproximation.CharClass
