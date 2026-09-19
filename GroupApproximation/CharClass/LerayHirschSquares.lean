import GroupApproximation.CharClass.LerayHirschColumn
import GroupApproximation.CharClass.ProjectiveSpaceRing

/-!
# The Leray–Hirsch ladder: its two rows and the squares between them

File 2 of the three that prove Leray–Hirsch (`LerayHirschColumn`, this file,
`LerayHirschInduction`).  The column built in `LerayHirschColumn` carries five
componentwise maps; here they are shown to be *exact* where the five lemma needs
it, and the Leray–Hirsch combination is shown to commute with all of them.

## The rows

`colExactW`, `colExactX` and `colExactSum` are the three exactness statements of
the shifted-sum column, in the same `iff/∃` element form as `MVSequence`'s own
three.  Each is the base sequence applied in every summand, with one boundary
index handled separately: in `colExactX` the summand with `2i = n+1` has source
`0` and target `H^0(X)`, so exactness there is exactly `MVFacts.exactZero`.

## The squares

All four restriction squares are one lemma, `lhSum_pull`: for a commuting square
of spaces the Leray–Hirsch combination commutes with pullback, and the four
restrictions of a Mayer–Vietoris sequence are pullbacks (`MVPulls`).  The
connecting square, `lhSum_delta`, is `MVFacts.delta_cup` together with
naturality of the connecting map along the projection (`MVLadder.delta_nat`).

## Main declarations

* `MVPulls` — the four restrictions of a Mayer–Vietoris sequence, as pullbacks.
* `MVLadder` — a map of covered spaces: the projection, the three restricted
  projections, the four commuting squares of spaces, and `delta_nat`.
* `lhTerm`, `lhSum`, `colPull` — the Leray–Hirsch combination as a homomorphism
  out of `lhDomain`, and pullback on the column.
* `lhSum_pull`, `lhSum_resU`, `lhSum_resV`, `lhSum_resWU`, `lhSum_resWV` — the
  four restriction squares.
* `lhSum_delta` — the connecting square.
* `colExactW`, `colExactX`, `colExactSum` — the column is exact.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory

noncomputable section

variable {X U V W P UP VP WP Y Q : TopCat.{0}}

/-! ## 0. Transport, sums, and characteristic two -/

/-- A pullback commutes with a transport of degrees. -/
theorem pull_cohCast {A B : TopCat.{0}} (f : A ⟶ B) {m m' : ℕ} (h : m = m')
    (a : Hmod2 B m) : pull f m' (cohCast h a) = cohCast h (pull f m a) := by
  subst h; rfl

/-- A pullback commutes with a finite sum. -/
theorem pull_sum {A B : TopCat.{0}} (f : A ⟶ B) (n : ℕ) {ι : Type} (s : Finset ι)
    (F : ι → Hmod2 B n) : pull f n (∑ i ∈ s, F i) = ∑ i ∈ s, pull f n (F i) := by
  have h := map_sum (pullLinear f n) F s
  simpa only [pullLinear_apply] using h

/-- Mod-2 cohomology has characteristic two. -/
theorem add_self (A : TopCat.{0}) (n : ℕ) (a : Hmod2 A n) : a + a = 0 := by
  rw [← two_smul (ZMod 2) a, show (2 : ZMod 2) = 0 from by decide, zero_smul]

/-- In characteristic two a sum vanishes exactly when the summands agree. -/
theorem add_eq_zero_iff_eq {A : TopCat.{0}} {n : ℕ} (a b : Hmod2 A n) :
    a + b = 0 ↔ a = b := by
  have hb : -b = b := neg_eq_iff_add_eq_zero.2 (add_self A n b)
  rw [add_eq_zero_iff_eq_neg, hb]

/-! ## 1. Componentwise laws for `lhDomain` -/

@[simp] theorem lhDomain_zero_apply {r n : ℕ} (i : Fin r) :
    ((0 : lhDomain X r n) : (j : Fin r) → Hmod2 X (n - 2 * (j : ℕ))) i = 0 := rfl

@[simp] theorem lhDomain_add_apply {r n : ℕ} (c d : lhDomain X r n) (i : Fin r) :
    ((c + d : lhDomain X r n) : (j : Fin r) → Hmod2 X (n - 2 * (j : ℕ))) i
      = (c : (j : Fin r) → Hmod2 X (n - 2 * (j : ℕ))) i
        + (d : (j : Fin r) → Hmod2 X (n - 2 * (j : ℕ))) i := rfl

theorem lhDomain_apply_eq {r n : ℕ} {c d : lhDomain X r n} (h : c = d) (i : Fin r) :
    (c : (j : Fin r) → Hmod2 X (n - 2 * (j : ℕ))) i
      = (d : (j : Fin r) → Hmod2 X (n - 2 * (j : ℕ))) i := by rw [h]

/-- **Componentwise choice into the column.**  A property that can be satisfied in
every summand that is present, and by `0` in every summand that is absent, is
satisfied by an element of `lhDomain`.  This is how each exactness statement of
the column is assembled from the base sequence. -/
theorem lhDomain_choice {r n : ℕ} (Qp : (i : Fin r) → Hmod2 X (n - 2 * (i : ℕ)) → Prop)
    (h0 : ∀ i : Fin r, n < 2 * (i : ℕ) → Qp i 0)
    (hex : ∀ i : Fin r, 2 * (i : ℕ) ≤ n → ∃ a, Qp i a) :
    ∃ c : lhDomain X r n,
      ∀ i : Fin r, Qp i ((c : (j : Fin r) → Hmod2 X (n - 2 * (j : ℕ))) i) := by
  have key : ∀ i : Fin r, ∃ a : Hmod2 X (n - 2 * (i : ℕ)),
      (n < 2 * (i : ℕ) → a = 0) ∧ Qp i a := by
    intro i
    by_cases hi : n < 2 * (i : ℕ)
    · exact ⟨0, fun _ => rfl, h0 i hi⟩
    · obtain ⟨a, ha⟩ := hex i (by omega)
      exact ⟨a, fun hc => absurd hc hi, ha⟩
  choose a ha1 ha2 using key
  exact ⟨⟨a, ha1⟩, ha2⟩

/-! ## 2. Mayer–Vietoris restrictions are pullbacks -/

/-- **The four restrictions of a Mayer–Vietoris sequence, as pullbacks.**  This is
the geometry that `MVSequence` deliberately forgets, and it is what makes the
restrictions multiplicative.  `cc-thom`'s `mvResU_eq_pull` family instantiates
it in one line each. -/
structure MVPulls (mv : MVSequence X U V W) where
  /-- The inclusion of the first open set. -/
  iU : U ⟶ X
  /-- The inclusion of the second open set. -/
  iV : V ⟶ X
  /-- The inclusion of the intersection into the first open set. -/
  jU : W ⟶ U
  /-- The inclusion of the intersection into the second open set. -/
  jV : W ⟶ V
  /-- Restriction to the first open set is a pullback. -/
  resU_eq : ∀ (n : ℕ) (x : Hmod2 X n), mv.resU n x = pull iU n x
  /-- Restriction to the second open set is a pullback. -/
  resV_eq : ∀ (n : ℕ) (x : Hmod2 X n), mv.resV n x = pull iV n x
  /-- Restriction from the first open set to the intersection is a pullback. -/
  resWU_eq : ∀ (n : ℕ) (x : Hmod2 U n), mv.resWU n x = pull jU n x
  /-- Restriction from the second open set to the intersection is a pullback. -/
  resWV_eq : ∀ (n : ℕ) (x : Hmod2 V n), mv.resWV n x = pull jV n x

/-- The two restrictions to the intersection agree on classes from the ambient
space.  This needs no hypothesis: it is the backward direction of `exact_sum`. -/
theorem resW_compat (mv : MVSequence X U V W) (n : ℕ) (x : Hmod2 X n) :
    mv.resWU n (mv.resU n x) = mv.resWV n (mv.resV n x) :=
  (mv.exact_sum n _ _).mpr ⟨x, rfl, rfl⟩

/-- Restriction to the first open set commutes with a transport of degrees. -/
theorem resU_cohCast (mv : MVSequence X U V W) {m m' : ℕ} (h : m = m') (a : Hmod2 X m) :
    mv.resU m' (cohCast h a) = cohCast h (mv.resU m a) := by subst h; rfl

/-- Restriction to the second open set commutes with a transport of degrees. -/
theorem resV_cohCast (mv : MVSequence X U V W) {m m' : ℕ} (h : m = m') (a : Hmod2 X m) :
    mv.resV m' (cohCast h a) = cohCast h (mv.resV m a) := by subst h; rfl

/-- The connecting map commutes with a transport of degrees. -/
theorem delta_cohCast (mv : MVSequence X U V W) {m m' : ℕ} (h : m = m') (a : Hmod2 W m) :
    mv.δ m' (cohCast h a) = cohCast (by omega) (mv.δ m a) := by subst h; rfl

/-- **A map of covered spaces.**  The projection of the bundle, its three
restrictions, the four squares of spaces they make, and naturality of the
connecting map.  The four restriction squares of *cohomology* follow from the
squares of spaces by functoriality; the connecting one does not, so it is a
field. -/
structure MVLadder {mvX : MVSequence X U V W} {mvP : MVSequence P UP VP WP}
    (pX : MVPulls mvX) (pP : MVPulls mvP) where
  /-- The projection. -/
  π : P ⟶ X
  /-- The projection over the first open set. -/
  πU : UP ⟶ U
  /-- The projection over the second open set. -/
  πV : VP ⟶ V
  /-- The projection over the intersection. -/
  πW : WP ⟶ W
  /-- The square over the first open set. -/
  sqU : pP.iU ≫ π = πU ≫ pX.iU
  /-- The square over the second open set. -/
  sqV : pP.iV ≫ π = πV ≫ pX.iV
  /-- The square of the first inclusion of the intersection. -/
  sqWU : pP.jU ≫ πU = πW ≫ pX.jU
  /-- The square of the second inclusion of the intersection. -/
  sqWV : pP.jV ≫ πV = πW ≫ pX.jV
  /-- **Naturality of the connecting map** along the projection. -/
  delta_nat : ∀ (n : ℕ) (a : Hmod2 W n),
    mvP.δ n (pull πW n a) = pull π (n + 1) (mvX.δ n a)

/-! ## 3. The Leray–Hirsch combination as a homomorphism -/

/-- One summand of the Leray–Hirsch combination, `π^*(a) ⌣ ξ^i`, with the summands
that the degree does not admit set to zero. -/
def lhTerm (π : P ⟶ X) (ξ : Hmod2 P 2) (n i : ℕ) (a : Hmod2 X (n - 2 * i)) : Hmod2 P n :=
  if h : 2 * i ≤ n then
    cohCast (Nat.sub_add_cancel h) (cup (pull π (n - 2 * i) a) (cupPowE ξ i))
  else 0

theorem lhTerm_of_le (π : P ⟶ X) (ξ : Hmod2 P 2) {n i : ℕ} (h : 2 * i ≤ n)
    (a : Hmod2 X (n - 2 * i)) :
    lhTerm π ξ n i a
      = cohCast (Nat.sub_add_cancel h) (cup (pull π (n - 2 * i) a) (cupPowE ξ i)) :=
  dif_pos h

theorem lhTerm_of_gt (π : P ⟶ X) (ξ : Hmod2 P 2) {n i : ℕ} (h : ¬ 2 * i ≤ n)
    (a : Hmod2 X (n - 2 * i)) : lhTerm π ξ n i a = 0 :=
  dif_neg h

@[simp] theorem lhTerm_zero (π : P ⟶ X) (ξ : Hmod2 P 2) (n i : ℕ) :
    lhTerm π ξ n i 0 = 0 := by
  by_cases h : 2 * i ≤ n
  · rw [lhTerm_of_le π ξ h, pull_zero, zero_cup, cohCast_zero]
  · rw [lhTerm_of_gt π ξ h]

theorem lhTerm_add (π : P ⟶ X) (ξ : Hmod2 P 2) (n i : ℕ) (a b : Hmod2 X (n - 2 * i)) :
    lhTerm π ξ n i (a + b) = lhTerm π ξ n i a + lhTerm π ξ n i b := by
  by_cases h : 2 * i ≤ n
  · rw [lhTerm_of_le π ξ h, lhTerm_of_le π ξ h, lhTerm_of_le π ξ h, pull_add,
      cup_add_left, cohCast_add]
  · rw [lhTerm_of_gt π ξ h, lhTerm_of_gt π ξ h, lhTerm_of_gt π ξ h, add_zero]

/-- The Leray–Hirsch combination on the ambient family, before the subgroup is
imposed.  Splitting the definition this way keeps additivity free of the
subtype coercion. -/
def lhSumPi (π : P ⟶ X) (ξ : Hmod2 P 2) (r n : ℕ) :
    ((i : Fin r) → Hmod2 X (n - 2 * (i : ℕ))) →+ Hmod2 P n where
  toFun c := ∑ i : Fin r, lhTerm π ξ n (i : ℕ) (c i)
  map_zero' := Finset.sum_eq_zero fun i _ => lhTerm_zero π ξ n (i : ℕ)
  map_add' a b := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => lhTerm_add π ξ n (i : ℕ) (a i) (b i)

/-- **The Leray–Hirsch combination**, `(a_i) ↦ ∑_i π^*(a_i) ⌣ ξ^i`, as a
homomorphism out of the column's degree-`n` term. -/
def lhSum (π : P ⟶ X) (ξ : Hmod2 P 2) (r n : ℕ) : lhDomain X r n →+ Hmod2 P n :=
  (lhSumPi π ξ r n).comp (lhDomain X r n).subtype

theorem lhSum_apply (π : P ⟶ X) (ξ : Hmod2 P 2) (r n : ℕ) (c : lhDomain X r n) :
    lhSum π ξ r n c = ∑ i : Fin r,
      lhTerm π ξ n (i : ℕ) ((c : (j : Fin r) → Hmod2 X (n - 2 * (j : ℕ))) i) := rfl

/-- Pullback on the ambient family, componentwise. -/
def colPullPi (f : Y ⟶ X) (r n : ℕ) :
    ((i : Fin r) → Hmod2 X (n - 2 * (i : ℕ))) →+
      ((i : Fin r) → Hmod2 Y (n - 2 * (i : ℕ))) where
  toFun c := fun i => pull f (n - 2 * (i : ℕ)) (c i)
  map_zero' := funext fun i => pull_zero f (n - 2 * (i : ℕ))
  map_add' a b := funext fun i => pull_add f (n - 2 * (i : ℕ)) (a i) (b i)

/-- Pullback on the column. -/
def colPull (f : Y ⟶ X) (r n : ℕ) : lhDomain X r n →+ lhDomain Y r n :=
  AddMonoidHom.codRestrict ((colPullPi f r n).comp (lhDomain X r n).subtype)
    (lhDomain Y r n) (by
      intro c i hi
      show pull f (n - 2 * (i : ℕ))
        ((c : (j : Fin r) → Hmod2 X (n - 2 * (j : ℕ))) i) = 0
      rw [lhDomain_vanish c i hi, pull_zero])

@[simp] theorem colPull_apply (f : Y ⟶ X) (r n : ℕ) (c : lhDomain X r n) (i : Fin r) :
    ((colPull f r n c : (j : Fin r) → Hmod2 Y (n - 2 * (j : ℕ))) i)
      = pull f (n - 2 * (i : ℕ))
          ((c : (j : Fin r) → Hmod2 X (n - 2 * (j : ℕ))) i) := rfl

/-! ## 4. The four restriction squares -/

/-- **The restriction square, once.**  For a commuting square of spaces the
Leray–Hirsch combination commutes with pullback. -/
theorem lhTerm_pull (f : Y ⟶ X) (g : Q ⟶ P) (πP : P ⟶ X) (πQ : Q ⟶ Y)
    (hsq : g ≫ πP = πQ ≫ f) (ξ : Hmod2 P 2) (n i : ℕ) (a : Hmod2 X (n - 2 * i)) :
    pull g n (lhTerm πP ξ n i a)
      = lhTerm πQ (pull g 2 ξ) n i (pull f (n - 2 * i) a) := by
  by_cases h : 2 * i ≤ n
  · rw [lhTerm_of_le πP ξ h, lhTerm_of_le πQ (pull g 2 ξ) h, pull_cohCast, pull_cup,
      ← pull_comp, hsq, pull_comp, pull_cupPowE]
  · rw [lhTerm_of_gt πP ξ h, lhTerm_of_gt πQ (pull g 2 ξ) h, pull_zero]

theorem lhSum_pull (f : Y ⟶ X) (g : Q ⟶ P) (πP : P ⟶ X) (πQ : Q ⟶ Y)
    (hsq : g ≫ πP = πQ ≫ f) (ξ : Hmod2 P 2) (r n : ℕ) (c : lhDomain X r n) :
    pull g n (lhSum πP ξ r n c)
      = lhSum πQ (pull g 2 ξ) r n (colPull f r n c) := by
  rw [lhSum_apply, lhSum_apply, pull_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [lhTerm_pull f g πP πQ hsq, colPull_apply]

theorem colResU_eq_colPull {mv : MVSequence X U V W} (p : MVPulls mv) (r n : ℕ)
    (c : lhDomain X r n) : colResU mv r n c = colPull p.iU r n c :=
  lhDomain_ext fun i => by rw [colResU_apply, colPull_apply, p.resU_eq]

theorem colResV_eq_colPull {mv : MVSequence X U V W} (p : MVPulls mv) (r n : ℕ)
    (c : lhDomain X r n) : colResV mv r n c = colPull p.iV r n c :=
  lhDomain_ext fun i => by rw [colResV_apply, colPull_apply, p.resV_eq]

theorem colResWU_eq_colPull {mv : MVSequence X U V W} (p : MVPulls mv) (r n : ℕ)
    (c : lhDomain U r n) : colResWU mv r n c = colPull p.jU r n c :=
  lhDomain_ext fun i => by rw [colResWU_apply, colPull_apply, p.resWU_eq]

theorem colResWV_eq_colPull {mv : MVSequence X U V W} (p : MVPulls mv) (r n : ℕ)
    (c : lhDomain V r n) : colResWV mv r n c = colPull p.jV r n c :=
  lhDomain_ext fun i => by rw [colResWV_apply, colPull_apply, p.resWV_eq]

variable {mvX : MVSequence X U V W} {mvP : MVSequence P UP VP WP}

/-- **The square over the first open set.** -/
theorem lhSum_resU (pX : MVPulls mvX) (pP : MVPulls mvP) (L : MVLadder pX pP)
    (ξ : Hmod2 P 2) (r n : ℕ) (c : lhDomain X r n) :
    mvP.resU n (lhSum L.π ξ r n c)
      = lhSum L.πU (mvP.resU 2 ξ) r n (colResU mvX r n c) := by
  rw [pP.resU_eq, lhSum_pull pX.iU pP.iU L.π L.πU L.sqU, pP.resU_eq,
    colResU_eq_colPull pX]

/-- **The square over the second open set.** -/
theorem lhSum_resV (pX : MVPulls mvX) (pP : MVPulls mvP) (L : MVLadder pX pP)
    (ξ : Hmod2 P 2) (r n : ℕ) (c : lhDomain X r n) :
    mvP.resV n (lhSum L.π ξ r n c)
      = lhSum L.πV (mvP.resV 2 ξ) r n (colResV mvX r n c) := by
  rw [pP.resV_eq, lhSum_pull pX.iV pP.iV L.π L.πV L.sqV, pP.resV_eq,
    colResV_eq_colPull pX]

/-- **The square of the first inclusion of the intersection.** -/
theorem lhSum_resWU (pX : MVPulls mvX) (pP : MVPulls mvP) (L : MVLadder pX pP)
    (ξU : Hmod2 UP 2) (r n : ℕ) (c : lhDomain U r n) :
    mvP.resWU n (lhSum L.πU ξU r n c)
      = lhSum L.πW (mvP.resWU 2 ξU) r n (colResWU mvX r n c) := by
  rw [pP.resWU_eq, lhSum_pull pX.jU pP.jU L.πU L.πW L.sqWU, pP.resWU_eq,
    colResWU_eq_colPull pX]

/-- **The square of the second inclusion of the intersection.** -/
theorem lhSum_resWV (pX : MVPulls mvX) (pP : MVPulls mvP) (L : MVLadder pX pP)
    (ξV : Hmod2 VP 2) (r n : ℕ) (c : lhDomain V r n) :
    mvP.resWV n (lhSum L.πV ξV r n c)
      = lhSum L.πW (mvP.resWV 2 ξV) r n (colResWV mvX r n c) := by
  rw [pP.resWV_eq, lhSum_pull pX.jV pP.jV L.πV L.πW L.sqWV, pP.resWV_eq,
    colResWV_eq_colPull pX]

/-! ## 5. The connecting square -/

/-- One summand of the column's connecting map. -/
def deltaTerm (mv : MVSequence X U V W) (n i : ℕ) (a : Hmod2 W (n - 2 * i)) :
    Hmod2 X (n + 1 - 2 * i) :=
  if h : 2 * i ≤ n then cohCast (by omega) (mv.δ (n - 2 * i) a) else 0

theorem deltaTerm_of_le (mv : MVSequence X U V W) {n i : ℕ} (h : 2 * i ≤ n)
    (a : Hmod2 W (n - 2 * i)) :
    deltaTerm mv n i a = cohCast (by omega) (mv.δ (n - 2 * i) a) :=
  dif_pos h

theorem deltaTerm_of_gt (mv : MVSequence X U V W) {n i : ℕ} (h : ¬ 2 * i ≤ n)
    (a : Hmod2 W (n - 2 * i)) : deltaTerm mv n i a = 0 :=
  dif_neg h

theorem colDelta_apply' (mv : MVSequence X U V W) (r n : ℕ) (c : lhDomain W r n)
    (i : Fin r) :
    ((colDelta mv r n c : (j : Fin r) → Hmod2 X (n + 1 - 2 * (j : ℕ))) i)
      = deltaTerm mv n (i : ℕ)
          ((c : (j : Fin r) → Hmod2 W (n - 2 * (j : ℕ))) i) := rfl

/-- **The connecting square, one summand.**  `MVFacts.delta_cup` moves the power of
`ξ` across the connecting map; `MVLadder.delta_nat` moves the projection across
it. -/
theorem lhTerm_delta (pP : MVPulls mvP) (hP : MVFacts mvP) (π : P ⟶ X) (πW : WP ⟶ W)
    (hdel : ∀ (m : ℕ) (a : Hmod2 W m),
      mvP.δ m (pull πW m a) = pull π (m + 1) (mvX.δ m a))
    (ξ : Hmod2 P 2) (n i : ℕ) (a : Hmod2 W (n - 2 * i)) :
    mvP.δ n (lhTerm πW (pull (pP.jU ≫ pP.iU) 2 ξ) n i a)
      = lhTerm π ξ (n + 1) i (deltaTerm mvX n i a) := by
  by_cases h : 2 * i ≤ n
  · have hle : 2 * i ≤ n + 1 := by omega
    -- The power of `ξ` on the intersection is restricted from the total space.
    have hxi : cupPowE (pull (pP.jU ≫ pP.iU) 2 ξ) i
        = mvP.resWU (2 * i) (mvP.resU (2 * i) (cupPowE ξ i)) := by
      rw [pP.resWU_eq, pP.resU_eq, ← pull_comp, pull_cupPowE]
    rw [lhTerm_of_le πW _ h, hxi, delta_cohCast, hP.delta_cup (n - 2 * i) (2 * i), hdel,
      lhTerm_of_le π ξ hle, deltaTerm_of_le mvX h, pull_cohCast, cup_cohCast_left,
      cohCast_cohCast, cohCast_cohCast]
  · rw [lhTerm_of_gt πW _ h, deltaTerm_of_gt mvX h, lhTerm_zero, map_zero]

/-- **The connecting square.** -/
theorem lhSum_delta (pX : MVPulls mvX) (pP : MVPulls mvP) (L : MVLadder pX pP)
    (hP : MVFacts mvP) (ξ : Hmod2 P 2) (r n : ℕ) (c : lhDomain W r n) :
    mvP.δ n (lhSum L.πW (pull (pP.jU ≫ pP.iU) 2 ξ) r n c)
      = lhSum L.π ξ r (n + 1) (colDelta mvX r n c) := by
  rw [lhSum_apply, lhSum_apply, map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [colDelta_apply', lhTerm_delta pP hP L.π L.πW L.delta_nat ξ n (i : ℕ)]

/-! ## 6. The column is exact -/

/-- **Exactness of the column at the intersection.** -/
theorem colExactW (mv : MVSequence X U V W) (r n : ℕ) (c : lhDomain W r n) :
    colDelta mv r n c = 0 ↔ ∃ (a : lhDomain U r n) (b : lhDomain V r n),
      colResWU mv r n a + colResWV mv r n b = c := by
  constructor
  · intro h
    have key : ∀ i : Fin r, ∃ ab : Hmod2 U (n - 2 * (i : ℕ)) × Hmod2 V (n - 2 * (i : ℕ)),
        (n < 2 * (i : ℕ) → ab.1 = 0 ∧ ab.2 = 0) ∧
        mv.resWU (n - 2 * (i : ℕ)) ab.1 + mv.resWV (n - 2 * (i : ℕ)) ab.2
          = (c : (j : Fin r) → Hmod2 W (n - 2 * (j : ℕ))) i := by
      intro i
      by_cases hi : n < 2 * (i : ℕ)
      · refine ⟨(0, 0), fun _ => ⟨rfl, rfl⟩, ?_⟩
        rw [map_zero, map_zero, add_zero, lhDomain_vanish c i hi]
      · have hd : mv.δ (n - 2 * (i : ℕ))
            ((c : (j : Fin r) → Hmod2 W (n - 2 * (j : ℕ))) i) = 0 := by
          have h' := lhDomain_apply_eq h i
          rw [colDelta_apply', lhDomain_zero_apply,
            deltaTerm_of_le mv (by omega)] at h'
          exact (cohCast_eq_zero_iff _ _).mp h'
        obtain ⟨a, b, hab⟩ := (mv.exact_W _ _).mp hd
        exact ⟨(a, b), fun hc => absurd hc hi, hab⟩
    choose ab hab1 hab2 using key
    refine ⟨⟨fun i => (ab i).1, fun i hi => (hab1 i hi).1⟩,
      ⟨fun i => (ab i).2, fun i hi => (hab1 i hi).2⟩, lhDomain_ext fun i => ?_⟩
    rw [lhDomain_add_apply, colResWU_apply, colResWV_apply]
    exact hab2 i
  · rintro ⟨a, b, rfl⟩
    refine lhDomain_ext fun i => ?_
    rw [colDelta_apply', lhDomain_zero_apply, lhDomain_add_apply,
      colResWU_apply, colResWV_apply]
    by_cases hi : 2 * (i : ℕ) ≤ n
    · rw [deltaTerm_of_le mv hi,
        (mv.exact_W _ _).mpr ⟨_, _, rfl⟩, cohCast_zero]
    · rw [deltaTerm_of_gt mv hi]

/-- **Exactness of the column at the ambient space.**  The summand with
`2i = n+1` is the boundary rung: its source is zero and its target is `H^0(X)`,
so exactness there is `MVFacts.exactZero`. -/
theorem colExactX (mv : MVSequence X U V W) (hf : MVFacts mv) (r n : ℕ)
    (c : lhDomain X r (n + 1)) :
    (colResU mv r (n + 1) c = 0 ∧ colResV mv r (n + 1) c = 0)
      ↔ ∃ w : lhDomain W r n, colDelta mv r n w = c := by
  constructor
  · rintro ⟨hU, hV⟩
    have hUc : ∀ i : Fin r, mv.resU (n + 1 - 2 * (i : ℕ))
        ((c : (j : Fin r) → Hmod2 X (n + 1 - 2 * (j : ℕ))) i) = 0 := by
      intro i
      have h' := lhDomain_apply_eq hU i
      rwa [colResU_apply, lhDomain_zero_apply] at h'
    have hVc : ∀ i : Fin r, mv.resV (n + 1 - 2 * (i : ℕ))
        ((c : (j : Fin r) → Hmod2 X (n + 1 - 2 * (j : ℕ))) i) = 0 := by
      intro i
      have h' := lhDomain_apply_eq hV i
      rwa [colResV_apply, lhDomain_zero_apply] at h'
    -- The summands the connecting map cannot reach are already zero.
    have hzero : ∀ i : Fin r, n < 2 * (i : ℕ) →
        (c : (j : Fin r) → Hmod2 X (n + 1 - 2 * (j : ℕ))) i = 0 := by
      intro i hi
      by_cases htop : n + 1 < 2 * (i : ℕ)
      · exact lhDomain_vanish c i htop
      · have he : n + 1 - 2 * (i : ℕ) = 0 := by omega
        have h0 : cohCast he ((c : (j : Fin r) → Hmod2 X (n + 1 - 2 * (j : ℕ))) i) = 0 := by
          refine hf.exactZero _ ?_ ?_
          · rw [resU_cohCast, hUc i, cohCast_zero]
          · rw [resV_cohCast, hVc i, cohCast_zero]
        exact (cohCast_eq_zero_iff _ _).mp h0
    have hchoice : ∃ w : lhDomain W r n, ∀ i : Fin r,
        deltaTerm mv n (i : ℕ)
            ((w : (j : Fin r) → Hmod2 W (n - 2 * (j : ℕ))) i)
          = (c : (j : Fin r) → Hmod2 X (n + 1 - 2 * (j : ℕ))) i := by
      refine lhDomain_choice
        (fun i wi => deltaTerm mv n (i : ℕ) wi
          = (c : (j : Fin r) → Hmod2 X (n + 1 - 2 * (j : ℕ))) i) ?_ ?_
      · intro i hi
        rw [deltaTerm_of_gt mv (by omega), hzero i hi]
      · intro i hi
        have he : n + 1 - 2 * (i : ℕ) = (n - 2 * (i : ℕ)) + 1 := by omega
        obtain ⟨w, hw⟩ := (mv.exact_X (n - 2 * (i : ℕ))
          (cohCast he ((c : (j : Fin r) → Hmod2 X (n + 1 - 2 * (j : ℕ))) i))).mp
          ⟨by rw [resU_cohCast, hUc i, cohCast_zero],
            by rw [resV_cohCast, hVc i, cohCast_zero]⟩
        refine ⟨w, ?_⟩
        rw [deltaTerm_of_le mv hi, hw, cohCast_cohCast, cohCast_self]
    obtain ⟨w, hw⟩ := hchoice
    exact ⟨w, lhDomain_ext fun i => by rw [colDelta_apply']; exact hw i⟩
  · rintro ⟨w, rfl⟩
    constructor
    · refine lhDomain_ext fun i => ?_
      rw [colResU_apply, colDelta_apply', lhDomain_zero_apply]
      by_cases hi : 2 * (i : ℕ) ≤ n
      · rw [deltaTerm_of_le mv hi, resU_cohCast,
          ((mv.exact_X _ _).mpr ⟨_, rfl⟩).1, cohCast_zero]
      · rw [deltaTerm_of_gt mv hi, map_zero]
    · refine lhDomain_ext fun i => ?_
      rw [colResV_apply, colDelta_apply', lhDomain_zero_apply]
      by_cases hi : 2 * (i : ℕ) ≤ n
      · rw [deltaTerm_of_le mv hi, resV_cohCast,
          ((mv.exact_X _ _).mpr ⟨_, rfl⟩).2, cohCast_zero]
      · rw [deltaTerm_of_gt mv hi, map_zero]

/-- **Exactness of the column in the middle.** -/
theorem colExactSum (mv : MVSequence X U V W) (r n : ℕ)
    (a : lhDomain U r n) (b : lhDomain V r n) :
    colResWU mv r n a + colResWV mv r n b = 0
      ↔ ∃ c : lhDomain X r n, colResU mv r n c = a ∧ colResV mv r n c = b := by
  constructor
  · intro h
    have hcomp : ∀ i : Fin r,
        mv.resWU (n - 2 * (i : ℕ)) ((a : (j : Fin r) → Hmod2 U (n - 2 * (j : ℕ))) i)
          = mv.resWV (n - 2 * (i : ℕ))
              ((b : (j : Fin r) → Hmod2 V (n - 2 * (j : ℕ))) i) := by
      intro i
      have h' := lhDomain_apply_eq h i
      rw [lhDomain_add_apply, colResWU_apply, colResWV_apply, lhDomain_zero_apply] at h'
      exact (add_eq_zero_iff_eq _ _).mp h'
    have hchoice : ∃ c : lhDomain X r n, ∀ i : Fin r,
        mv.resU (n - 2 * (i : ℕ))
              ((c : (j : Fin r) → Hmod2 X (n - 2 * (j : ℕ))) i)
            = (a : (j : Fin r) → Hmod2 U (n - 2 * (j : ℕ))) i ∧
          mv.resV (n - 2 * (i : ℕ))
              ((c : (j : Fin r) → Hmod2 X (n - 2 * (j : ℕ))) i)
            = (b : (j : Fin r) → Hmod2 V (n - 2 * (j : ℕ))) i := by
      refine lhDomain_choice
        (fun i x => mv.resU (n - 2 * (i : ℕ)) x
            = (a : (j : Fin r) → Hmod2 U (n - 2 * (j : ℕ))) i ∧
          mv.resV (n - 2 * (i : ℕ)) x
            = (b : (j : Fin r) → Hmod2 V (n - 2 * (j : ℕ))) i) ?_ ?_
      · intro i hi
        exact ⟨by rw [map_zero, lhDomain_vanish a i hi],
          by rw [map_zero, lhDomain_vanish b i hi]⟩
      · intro i _
        exact (mv.exact_sum _ _ _).mp (hcomp i)
    obtain ⟨c, hc⟩ := hchoice
    exact ⟨c, lhDomain_ext fun i => by rw [colResU_apply]; exact (hc i).1,
      lhDomain_ext fun i => by rw [colResV_apply]; exact (hc i).2⟩
  · rintro ⟨c, rfl, rfl⟩
    refine lhDomain_ext fun i => ?_
    rw [lhDomain_add_apply, colResWU_apply, colResWV_apply, colResU_apply,
      colResV_apply, lhDomain_zero_apply, resW_compat]
    exact add_self _ _ _

end

end LH
end CharClass
end GroupApproximation
