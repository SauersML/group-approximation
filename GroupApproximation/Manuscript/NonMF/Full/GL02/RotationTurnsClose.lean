import GroupApproximation.Manuscript.NonMF.Full.GL02.RotationTurnsWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04: the pocket spellings are closed by first turns

*GL02 copy.*  Re-proof of the foreign module `Piece04.RotationTurnsClose`
(origin/main blob `3b46e2895`), moved to namespace `Piece04.GL02` since the modules it
imports include files last changed by commits marked WIP.  Only namespaces, the imports of
copied modules, and the qualification of foreign names differ from the original.

This file continues `RotationTurnsWalk` for a pocket setting: the walk `X T Y U`, the carrier
`q B p A`.

* `passTail`: rotation from `p.head` reaches `(X T).head` safely.  If `U` ends with `u` and
  `p = γ (α u) p'`, then `φ u = (X T).head`.  If `γ = []`, the run is the single step
  `σ (α u) = φ u`.  Otherwise `σ ((X T).head) = γ.head`, and `loop_safeRun` passes the loop `γ`
  up to `α u`.
* `firstTurnClosed_X`: **`B X` is closed by first turns.**  Inside `B` and inside `X` the steps
  are face steps.  From `B.last` the face step is `p.head`, then `passTail` reaches `X.head`.  The
  closing step turns in the same way.
  - If `X = []`: face step to `p.head`, `passTail` to `T.head`, `passHead` to `B.head`.
  - If `B = []`: face step from `X.last` to `T.head`, `passHead` to `p.head`, `passTail` to
    `X.head`.
  - Otherwise: face step from `X.last` to `T.head`, then `passHead` to `B.head`.
* `firstTurnClosed_Y`: `A Y` is the same statement for the swapped setting `Y U X T`,
  `p A q B`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.RotationTurns

open Equiv
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides

universe v

variable {M : CombMap.{v}} {X T Y U q B p A : List M.Dart}

/-- **Passing the tail of the source window**: rotation from `p.head` reaches `(X T).head`
safely. -/
theorem passTail (h : PocketSetting M X T Y U q B p A) {g x : M.Dart} (hg : p.head? = some g)
    (hx : (X ++ T).head? = some x) : ∃ k, Piece04.RotationTurns.SafeRun M (B ++ X) g x k := by
  obtain ⟨u, U', p', γ, rfl, rfl, hγ⟩ := h.tailU
  have hu : u ∈ U' ++ [u] := List.mem_append_right U' (List.mem_singleton_self u)
  have hnotU := not_keep_U h hu
  have hfu : M.facePerm u = x := succ_blocks (s := X ++ T ++ Y ++ U') (a := [u]) (r := [])
    (d := u) (faceCycle_of_eq h.walk (by simp)) rfl
    (by rw [List.nil_append]; exact head?_append_of_head? (head?_append_of_head? hx Y) U')
  have hed : M.sigma (M.alpha u) = x := by rwa [CombMap.facePerm, Perm.mul_apply] at hfu
  by_cases hγn : γ = []
  · subst hγn
    have hg' : M.alpha u = g := by simpa using hg
    subst hg'
    exact ⟨1, Piece04.RotationTurns.SafeRun.one hnotU hed⟩
  obtain ⟨g₁, hg₁⟩ : ∃ g, γ.getLast? = some g := ⟨_, List.getLast?_eq_some_getLast hγn⟩
  have hg₀ : γ.head? = some g := head?_left_of_ne_nil hγn hg
  have hdg : M.sigma x = g := by
    rw [← hfu]
    exact hγ g hg₀
  have hfK : M.IsFaceCycle (q ++ B ++ γ ++ (M.alpha u :: p' ++ A)) :=
    faceCycle_of_eq h.carrier (by simp)
  have he : M.facePerm g₁ = M.alpha u := succ_blocks hfK hg₁ (by simp)
  have hγnd : γ.Nodup := (List.nodup_append.mp (List.nodup_append.mp hfK.nodup).1).2.1
  have hγchain : γ.IsChain fun a b => M.facePerm a = b :=
    hfK.chain.infix ⟨q ++ B, M.alpha u :: p' ++ A, rfl⟩
  have hγmem : ∀ y ∈ γ, y ∈ q ++ B ++ (γ ++ M.alpha u :: p') ++ A := fun y hy =>
    List.mem_append_left A (List.mem_append_right _ (List.mem_append_left _ hy))
  have hxw : x ∈ X ++ T ++ Y ++ (U' ++ [u]) :=
    List.mem_append_left _ (List.mem_append_left Y (List.mem_of_mem_head? hx))
  have huw : u ∈ X ++ T ++ Y ++ (U' ++ [u]) := List.mem_append_right _ hu
  have heγ : M.alpha u ∉ γ := fun hm => ne_of_nodup h.carrier.nodup (s := q ++ B) (m := [])
    (r := p' ++ A) (by simp) hm (List.mem_singleton_self _) rfl
  have hαe : M.alpha (M.alpha u) ∉ γ := by
    rw [M.alpha_involutive u]
    exact fun hm => h.ne_of_face huw (hγmem _ hm) rfl
  have hdγ : x ∉ γ := fun hm => h.ne_of_face hxw (hγmem _ hm) rfl
  have hγc : ∀ y ∈ γ, y ∉ B ++ X := by
    intro y hy hyc
    rcases List.mem_append.mp hyc with hyB | hyX
    · exact ne_of_nodup h.carrier.nodup (s := q) (m := []) (r := M.alpha u :: p' ++ A)
        (by simp) hyB hy rfl
    · exact h.ne_of_face (List.mem_append_left _ (List.mem_append_left Y
        (List.mem_append_left T hyX))) (hγmem _ hy) rfl
  have hc : ∀ y ∈ B ++ X, M.faceOf y = M.faceOf g ∨ M.faceOf y = M.faceOf x := by
    intro y hy
    rcases List.mem_append.mp hy with hyB | hyX
    · exact Or.inl (face_eq h.carrier (List.mem_append_left A (List.mem_append_left _
        (List.mem_append_right q hyB))) (hγmem _ (List.mem_of_mem_head? hg₀)))
    · exact Or.inr (face_eq h.walk (List.mem_append_left _ (List.mem_append_left Y
        (List.mem_append_left T hyX))) hxw)
  obtain ⟨k, hk⟩ := Piece04.RotationTurns.loop_safeRun h.planar hγnd hγchain hg₀ hg₁ he hed hdg heγ hαe hdγ hγc hc
  exact ⟨1 + k, hk.trans (Piece04.RotationTurns.SafeRun.one hnotU hed)⟩

theorem closed_of {c : List M.Dart} (hchain : c.IsChain (FirstTurn M c))
    (hclose : ∀ x, c.getLast? = some x → ∀ y, c.head? = some y → FirstTurn M c x y) :
    FirstTurnClosed M c :=
  fun hc => ⟨hchain, hclose _ (List.getLast?_eq_some_getLast hc) _ (List.head?_eq_some_head hc)⟩

theorem PocketSetting.head_p (h : PocketSetting M X T Y U q B p A) :
    ∃ g, p.head? = some g := by
  obtain ⟨_, _, _, _, -, rfl, -⟩ := h.tailU
  exact ⟨_, List.head?_eq_some_head (by simp)⟩

theorem PocketSetting.head_T (h : PocketSetting M X T Y U q B p A) :
    ∃ t, T.head? = some t := by
  obtain ⟨t, _, _, _, rfl, -, -⟩ := h.headT
  exact ⟨t, rfl⟩

/-- **The spelling `B X` is closed by first turns.** -/
theorem firstTurnClosed_X (h : PocketSetting M X T Y U q B p A) : FirstTurnClosed M (B ++ X) := by
  obtain ⟨g, hg⟩ := h.head_p
  obtain ⟨t, ht⟩ := h.head_T
  have hlastB : ∀ x, B.getLast? = some x → M.facePerm x = g := fun x hx =>
    succ_blocks (s := q) (a := B) (r := p ++ A) (faceCycle_of_eq h.carrier (by simp)) hx
      (head?_append_of_head? (head?_append_of_head? hg A) q)
  have hlastX : ∀ x, X.getLast? = some x → M.facePerm x = t := fun x hx =>
    succ_blocks (s := []) (a := X) (r := T ++ Y ++ U) (faceCycle_of_eq h.walk (by simp)) hx
      (by rw [List.append_nil]; exact head?_append_of_head? (head?_append_of_head? ht Y) U)
  refine closed_of (List.isChain_append.mpr ⟨?_, ?_, ?_⟩) ?_
  · exact (h.carrier.chain.infix ⟨q, p ++ A, by simp only [List.append_assoc]⟩).imp
      fun _ _ hab => FirstTurn.of_facePerm hab
  · exact (h.walk.chain.infix
      ⟨[], T ++ Y ++ U, by simp only [List.nil_append, List.append_assoc]⟩).imp
      fun _ _ hab => FirstTurn.of_facePerm hab
  · intro x hx y hy
    rw [Option.mem_def] at hx hy
    obtain ⟨k, hk⟩ := passTail h hg (head?_append_of_head? hy T)
    exact firstTurn_of_face_run (hlastB x hx) hk
  · intro x hx y hy
    by_cases hX : X = []
    · subst hX
      rw [List.append_nil] at hx hy
      obtain ⟨k₁, hk₁⟩ := passTail h hg (by rw [List.nil_append]; exact ht)
      obtain ⟨k₂, hk₂⟩ := passHead h ht (head?_append_of_head? hy p)
      exact firstTurn_of_face_run (hlastB x hx) (hk₁.trans hk₂)
    · have hx' := getLast?_right_of_ne_nil hX hx
      by_cases hB : B = []
      · subst hB
        rw [List.nil_append] at hy
        obtain ⟨k₁, hk₁⟩ := passHead h ht (by rw [List.nil_append]; exact hg)
        obtain ⟨k₂, hk₂⟩ := passTail h hg (head?_append_of_head? hy T)
        exact firstTurn_of_face_run (hlastX x hx') (hk₁.trans hk₂)
      · obtain ⟨k, hk⟩ := passHead h ht (head?_append_of_head? (head?_left_of_ne_nil hB hy) p)
        exact firstTurn_of_face_run (hlastX x hx') hk

theorem mem_swap {ι : Type*} {a b c d : List ι} {x : ι} (h : x ∈ c ++ d ++ a ++ b) :
    x ∈ a ++ b ++ c ++ d := by
  simp only [List.mem_append] at h ⊢
  tauto

theorem faceCycle_swap {a b c d : List M.Dart} (h : M.IsFaceCycle (a ++ b ++ c ++ d)) :
    M.IsFaceCycle (c ++ d ++ a ++ b) :=
  faceCycle_of_eq (h.rotate (a ++ b).length) (by
    rw [List.append_assoc (a ++ b) c d, List.rotate_append_length_eq]
    simp only [List.append_assoc])

/-- The swapped pocket setting: the walk `Y U X T` and the carrier `p A q B`. -/
theorem PocketSetting.swap (h : PocketSetting M X T Y U q B p A) (headU : WindowHeadShape M U p)
    (tailT : WindowTailShape M T q) : PocketSetting M Y U X T p A q B where
  planar := h.planar
  walk := faceCycle_swap h.walk
  carrier := faceCycle_swap h.carrier
  face_ne := fun x hx y hy => h.face_ne x (mem_swap hx) y (mem_swap hy)
  cross_T := h.cross_U
  cross_U := h.cross_T
  headT := headU
  tailU := tailT

/-- **The spelling `A Y` is closed by first turns.** -/
theorem firstTurnClosed_Y (h : PocketSetting M X T Y U q B p A) (headU : WindowHeadShape M U p)
    (tailT : WindowTailShape M T q) : FirstTurnClosed M (A ++ Y) :=
  firstTurnClosed_X (h.swap headU tailT)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.RotationTurns

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.RotationTurns.passTail
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.RotationTurns.closed_of
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.RotationTurns.PocketSetting.head_p
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.RotationTurns.PocketSetting.head_T
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.RotationTurns.firstTurnClosed_X
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.RotationTurns.mem_swap
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.RotationTurns.faceCycle_swap
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.RotationTurns.PocketSetting.swap
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.RotationTurns.firstTurnClosed_Y
