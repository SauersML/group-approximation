import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellPocketNoncrossing
import GroupApproximation.GGT.VanKampen.ClosedWalkFirstTurnEnclosure
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04: rotating past a loop of the carrier

Let `γ = g₀ … g₁` be a stretch of darts chained by the face permutation, and `e = φ g₁` the dart
after it.  Suppose that rotating twice from `e` returns to `g₀`: `σ e = d` and `σ d = g₀`.
Then `γ` is a closed walk.  Each step inside `γ` is a face step, and the closing step
`g₁ → g₀` turns past `e` and `d`, which lie off the edges of `γ`.

* `SafeRun M c u x k`: rotating `k` times from `u` reaches `x`, and every earlier dart lies off the
  edges of `c`.  `SafeRun.trans` composes runs.  `firstTurn_of_safeRun` turns a run from `σ (α x)`
  to `y` into a first turn `x → y`.
* `loop_turnMem`: the loop `γ` is chained by first turns, so it turns like a noncrossing walk
  (`turnMem_of_firstTurn`).
* `loop_safeRun`: **rotating from `g₀` to `e` stays off the edges of any walk `c`** whose darts are
  off `γ` and lie on the faces of `g₀` or `d`.  The darts met rotating around the vertex from `g₀`
  before `e` are `Inside γ`: on `γ`, or based in a face enclosed by `γ`.  The dart `g₀` is on `γ`.
  If `w` is inside, so is `α w` (`inside_alpha`).  Crossing an edge off `γ` keeps the enclosed
  faces, and the reversal of a walk dart with reversal off the walk is enclosed.  Then
  `σ w = φ (α w)` is on `γ` or on the same enclosed face, unless `α w = g₁`, that is `σ w = e`
  (`loop_step`).  A walk dart of `c` inside `γ` would be a dart off `γ` in an enclosed face.  Its
  face is the face of `g₀` (not enclosed: `g₀` is a walk dart, `faceOf_not_mem_enclosedFaces`) or
  the face of `d`.  If `d` were in an enclosed face, crossing its edge (off `γ`,
  `alpha_not_mem`) would enclose `α d`, whose face is the face of `φ (α d) = σ d = g₀`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.RotationTurns

open Equiv
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
open GroupApproximation.GGT.VanKampen.FirstTurnEnclosure

universe v

/-- **A safe run**: `k` rotation steps from `u` reach `x`, every earlier dart off the edges of `c`. -/
structure SafeRun (M : CombMap.{v}) (c : List M.Dart) (u x : M.Dart) (k : ℕ) : Prop where
  pow_eq : (M.sigma ^ k) u = x
  safe : ∀ t, t < k → ¬ walkKeep M c ((M.sigma ^ t) u)

variable {M : CombMap.{v}}

namespace SafeRun

variable {c : List M.Dart}

theorem one {u x : M.Dart} (hu : ¬ walkKeep M c u) (h : M.sigma u = x) : SafeRun M c u x 1 :=
  ⟨by rw [pow_one]; exact h, fun t ht => by
    obtain rfl : t = 0 := by omega
    rwa [pow_zero, Perm.one_apply]⟩

theorem trans {u x y : M.Dart} {k₁ k₂ : ℕ} (h₁ : SafeRun M c u x k₁) (h₂ : SafeRun M c x y k₂) :
    SafeRun M c u y (k₂ + k₁) := by
  refine ⟨by rw [pow_add, Perm.mul_apply, h₁.pow_eq, h₂.pow_eq], fun t ht => ?_⟩
  by_cases htk : t < k₁
  · exact h₁.safe t htk
  · obtain ⟨s, rfl⟩ : ∃ s, t = s + k₁ := ⟨t - k₁, by omega⟩
    rw [pow_add, Perm.mul_apply, h₁.pow_eq]
    exact h₂.safe s (by omega)

end SafeRun

/-- A safe run from `σ (α x)` to `y` is a first turn from `x` to `y`. -/
theorem firstTurn_of_safeRun {c : List M.Dart} {x y : M.Dart} {k : ℕ}
    (h : SafeRun M c (M.sigma (M.alpha x)) y k) : FirstTurn M c x y := by
  refine ⟨k + 1, by omega, ?_, fun t ht htk => ?_⟩
  · rw [pow_succ, Perm.mul_apply]
    exact h.pow_eq
  · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    rw [pow_succ, Perm.mul_apply]
    exact h.safe s (by omega)

/-- A dart on `γ`, or based in a face enclosed by `γ`. -/
def Inside (M : CombMap.{v}) (γ : List M.Dart) (w : M.Dart) : Prop :=
  w ∈ γ ∨ M.faceOf w ∈ enclosedFaces M γ

theorem inside_alpha {γ : List M.Dart} {w : M.Dart} (hw : Inside M γ w) :
    Inside M γ (M.alpha w) := by
  by_cases hα : M.alpha w ∈ γ
  · exact Or.inl hα
  · refine Or.inr ?_
    by_cases hwγ : w ∈ γ
    · exact (mem_enclosedFaces_iff M γ _).mpr ⟨w, hwγ, hα, .refl _⟩
    · rcases hw with hw | hw
      · exact absurd hw hwγ
      · exact faceOf_alpha_mem_enclosedFaces (by rintro (h | h) <;> contradiction) hw

theorem facePerm_mem_of_isChain {γ : List M.Dart} (hchain : γ.IsChain fun a b => M.facePerm a = b)
    {g₁ a : M.Dart} (h₁ : γ.getLast? = some g₁) (ha : a ∈ γ) (hne : a ≠ g₁) :
    M.facePerm a ∈ γ := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem ha
  cases t with
  | nil => exact hne (by simpa using h₁)
  | cons b t =>
    have hab : M.facePerm a = b := List.isChain_iff_forall_rel_of_append_cons_cons.mp hchain rfl
    rw [hab]
    simp

theorem facePerm_alpha {x y : M.Dart} (h : M.sigma x = y) : M.facePerm (M.alpha x) = y := by
  rw [CombMap.facePerm, Perm.mul_apply, M.alpha_involutive x, h]

theorem loop_step {γ : List M.Dart} (hchain : γ.IsChain fun a b => M.facePerm a = b)
    {g₁ e w : M.Dart} (h₁ : γ.getLast? = some g₁) (he : M.facePerm g₁ = e) (hw : Inside M γ w)
    (hne : M.sigma w ≠ e) : Inside M γ (M.sigma w) := by
  have hfp : M.facePerm (M.alpha w) = M.sigma w := facePerm_alpha rfl
  rw [← hfp]
  rcases inside_alpha hw with hα | hα
  · refine Or.inl (facePerm_mem_of_isChain hchain h₁ hα fun h => hne ?_)
    rw [← hfp, h, he]
  · refine Or.inr ?_
    rwa [M.faceOf_facePerm]

theorem alpha_not_mem {γ : List M.Dart} (hnd : γ.Nodup)
    (hchain : γ.IsChain fun a b => M.facePerm a = b) {g₀ g₁ e d : M.Dart}
    (h₀ : γ.head? = some g₀) (h₁ : γ.getLast? = some g₁) (he : M.facePerm g₁ = e) (heγ : e ∉ γ)
    (hdg : M.sigma d = g₀) : M.alpha d ∉ γ := by
  intro hαd
  have hfp : M.facePerm (M.alpha d) = g₀ := facePerm_alpha hdg
  by_cases hlast : M.alpha d = g₁
  · rw [hlast, he] at hfp
    exact heγ (by rw [hfp]; exact List.mem_of_mem_head? h₀)
  · obtain ⟨s, t, rfl⟩ := List.append_of_mem hαd
    cases t with
    | nil => exact hlast (by simpa using h₁)
    | cons b t =>
      have hab : M.facePerm (M.alpha d) = b :=
        List.isChain_iff_forall_rel_of_append_cons_cons.mp hchain rfl
      have hb : b = g₀ := hab.symm.trans hfp
      cases s with
      | nil =>
        rw [List.nil_append] at hnd
        have h0 : M.alpha d = g₀ := by simpa using h₀
        exact (List.nodup_cons.mp hnd).1 (by simp [hb, h0])
      | cons a s =>
        rw [List.cons_append] at hnd
        have h0 : a = g₀ := by simpa using h₀
        exact (List.nodup_cons.mp hnd).1 (by simp [hb, h0])

theorem loop_turnMem {γ : List M.Dart} (hchain : γ.IsChain fun a b => M.facePerm a = b)
    {g₀ g₁ e d : M.Dart} (h₀ : γ.head? = some g₀) (h₁ : γ.getLast? = some g₁)
    (he : M.facePerm g₁ = e) (hed : M.sigma e = d) (hdg : M.sigma d = g₀)
    (hekeep : ¬ walkKeep M γ e) (hdkeep : ¬ walkKeep M γ d) :
    γ ≠ [] ∧ γ.IsChain (fun a b => M.vertexOf (M.alpha a) = M.vertexOf b) ∧ TurnMem M γ := by
  have hne : γ ≠ [] := by
    rintro rfl
    simp at h₀
  have hft : γ.IsChain (FirstTurn M γ) := hchain.imp fun _ _ h => FirstTurn.of_facePerm h
  have hlast : γ.getLast hne = g₁ := by
    rw [List.getLast?_eq_some_getLast hne] at h₁
    exact Option.some.inj h₁
  have hhead : γ.head hne = g₀ := by
    rw [List.head?_eq_some_head hne] at h₀
    exact Option.some.inj h₀
  have hclose : FirstTurn M γ (γ.getLast hne) (γ.head hne) := by
    rw [hlast, hhead]
    exact SameCellPocketNoncrossing.firstTurn_of_three he hekeep hed hdkeep hdg
  refine ⟨hne, hchain.imp fun a b h => ?_, turnMem_of_firstTurn hne hft hclose⟩
  rw [← h, CombMap.facePerm, Perm.mul_apply, M.vertexOf_sigma]

/-- **Rotating from the start of a loop of the carrier to the dart after it is safe.** -/
theorem loop_safeRun (hM : M.IsPlanar) {γ c : List M.Dart} (hnd : γ.Nodup)
    (hchain : γ.IsChain fun a b => M.facePerm a = b) {g₀ g₁ e d : M.Dart}
    (h₀ : γ.head? = some g₀) (h₁ : γ.getLast? = some g₁) (he : M.facePerm g₁ = e)
    (hed : M.sigma e = d) (hdg : M.sigma d = g₀) (heγ : e ∉ γ) (hαe : M.alpha e ∉ γ)
    (hdγ : d ∉ γ) (hγc : ∀ x ∈ γ, x ∉ c)
    (hc : ∀ x ∈ c, M.faceOf x = M.faceOf g₀ ∨ M.faceOf x = M.faceOf d) :
    ∃ k, SafeRun M c g₀ e k := by
  classical
  have hαd := alpha_not_mem hnd hchain h₀ h₁ he heγ hdg
  have hekeep : ¬ walkKeep M γ e := by rintro (h | h) <;> contradiction
  have hdkeep : ¬ walkKeep M γ d := by rintro (h | h) <;> contradiction
  obtain ⟨hne, hvchain, hturn⟩ := loop_turnMem hchain h₀ h₁ he hed hdg hekeep hdkeep
  have hg₀ : g₀ ∈ γ := List.mem_of_mem_head? h₀
  have hout : M.faceOf g₀ ∉ enclosedFaces M γ :=
    faceOf_not_mem_enclosedFaces hM hne hvchain hturn hg₀
  have hdout : M.faceOf d ∉ enclosedFaces M γ := fun hd => by
    have h := faceOf_alpha_mem_enclosedFaces hdkeep hd
    have h2 : M.faceOf (M.alpha d) = M.faceOf g₀ := by
      rw [← facePerm_alpha hdg, M.faceOf_facePerm]
    rw [h2] at h
    exact hout h
  have hnot : ∀ w, Inside M γ w → w ∉ c := by
    rintro w (hw | hw) hwc
    · exact hγc w hw hwc
    · rcases hc w hwc with h | h
      · rw [h] at hw
        exact hout hw
      · rw [h] at hw
        exact hdout hw
  have hsafe : ∀ w, Inside M γ w → ¬ walkKeep M c w := by
    rintro w hw (h | h)
    · exact hnot w hw h
    · exact hnot _ (inside_alpha hw) h
  have hv : M.vertexOf g₀ = M.vertexOf e := by
    rw [← hdg, ← hed, M.vertexOf_sigma, M.vertexOf_sigma]
  have hex : ∃ i : ℕ, (M.sigma ^ i) g₀ = e := ((M.vertexOf_eq_iff _ _).mp hv).exists_nat_pow_eq
  have hinside : ∀ t, t < Nat.find hex → Inside M γ ((M.sigma ^ t) g₀) := by
    intro t
    induction t with
    | zero =>
      intro _
      rw [pow_zero, Perm.one_apply]
      exact Or.inl hg₀
    | succ t ih =>
      intro ht
      rw [pow_succ', Perm.mul_apply]
      exact loop_step hchain h₁ he (ih (by omega)) fun h =>
        Nat.find_min hex ht (by rw [pow_succ', Perm.mul_apply]; exact h)
  exact ⟨Nat.find hex, Nat.find_spec hex, fun t ht => hsafe _ (hinside t ht)⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.RotationTurns
