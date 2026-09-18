import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.RotationTurnsLoop
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.RCellEnclosureWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04: passing a window of the pocket

The walk is a face cycle `X T Y U`.  The carrier `∂Π` is a face cycle `q B p A` of a different
face.  Every dart of `T` reverses into `q`, and every dart of `U` reverses into `p`.  We study the
spelling `c = B X` and rotate around vertices from the end of one block of `c` to the start of the
next.

* `WindowHeadShape M T q`: `T` starts with `t`, and `q = q' (α t) γ`.  If `γ` is nonempty, then
  `σ (φ γ.last) = t`.  `γ` is the whole gap in front of the first side of the window.
  `WindowTailShape M U p` is the mirror image.
* `not_keep_T`, `not_keep_U`: a dart of `T` and the reversal of a dart of `U` are off the edges of
  `c`.  A dart of `T` is on the walk, not in `X` (walk duplicate free) and not on the face of `Π`.
  Its reversal lies in `q`, so it is not in `B` (carrier duplicate free) and not on the face of the
  walk.
* `passHead`: from `t = T.head` rotation reaches `e = (B p).head` safely.  If `γ = []`, then
  `φ (α t) = e`, so `σ t = e`.  Otherwise `σ t = γ.head` and `σ (φ γ.last) = t`, and
  `loop_safeRun` passes the loop `γ`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.RotationTurns

open Equiv
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
open GroupApproximation.GGT.VanKampen.FirstTurnEnclosure

universe v

/-- **The head of a window**: `T` starts with `t`, and `q = q' (α t) γ` with `σ (φ γ.last) = t`
whenever `γ` is nonempty. -/
def WindowHeadShape (M : CombMap.{v}) (T q : List M.Dart) : Prop :=
  ∃ (t : M.Dart) (T' q' γ : List M.Dart), T = t :: T' ∧ q = q' ++ M.alpha t :: γ ∧
    ∀ g, γ.getLast? = some g → M.sigma (M.facePerm g) = t

/-- **The tail of a window**: `U` ends with `u`, and `p = γ (α u) p'` with `σ (φ u) = γ.head`
whenever `γ` is nonempty. -/
def WindowTailShape (M : CombMap.{v}) (U p : List M.Dart) : Prop :=
  ∃ (u : M.Dart) (U' p' γ : List M.Dart), U = U' ++ [u] ∧ p = γ ++ M.alpha u :: p' ∧
    ∀ g, γ.head? = some g → M.sigma (M.facePerm u) = g

/-- **A pocket setting**: the walk `X T Y U` and the carrier `q B p A` of one planar map. -/
structure PocketSetting (M : CombMap.{v}) (X T Y U q B p A : List M.Dart) : Prop where
  planar : M.IsPlanar
  walk : M.IsFaceCycle (X ++ T ++ Y ++ U)
  carrier : M.IsFaceCycle (q ++ B ++ p ++ A)
  face_ne : ∀ x ∈ X ++ T ++ Y ++ U, ∀ y ∈ q ++ B ++ p ++ A, M.faceOf x ≠ M.faceOf y
  cross_T : ∀ d ∈ T, M.alpha d ∈ q
  cross_U : ∀ d ∈ U, M.alpha d ∈ p
  headT : WindowHeadShape M T q
  tailU : WindowTailShape M U p

variable {M : CombMap.{v}}

theorem faceCycle_of_eq {L L' : List M.Dart} (hL : M.IsFaceCycle L) (h : L = L') :
    M.IsFaceCycle L' := h ▸ hL

theorem ne_of_nodup {ι : Type*} {l s a m b r : List ι} {x y : ι} (h : l.Nodup)
    (hl : l = s ++ a ++ m ++ b ++ r) (hx : x ∈ a) (hy : y ∈ b) : x ≠ y := by
  subst hl
  exact (List.nodup_append.mp (List.nodup_append.mp h).1).2.2 x
    (List.mem_append_left m (List.mem_append_right s hx)) y hy

theorem face_eq {L : List M.Dart} (hL : M.IsFaceCycle L) {x y : M.Dart} (hx : x ∈ L)
    (hy : y ∈ L) : M.faceOf x = M.faceOf y :=
  ((hL.mem_iff x).mp hx).trans ((hL.mem_iff y).mp hy).symm

theorem sigma_eq_of_facePerm_alpha {x y : M.Dart} (h : M.facePerm (M.alpha x) = y) :
    M.sigma x = y := by
  rwa [CombMap.facePerm, Perm.mul_apply, M.alpha_involutive x] at h

theorem head?_append_of_head? {ι : Type*} {l : List ι} {a : ι} (h : l.head? = some a)
    (l' : List ι) : (l ++ l').head? = some a := by
  rw [List.head?_append, h, Option.some_or]

theorem head?_left_of_ne_nil {ι : Type*} {l l' : List ι} {a : ι} (hl : l ≠ [])
    (h : (l ++ l').head? = some a) : l.head? = some a := by
  rw [List.head?_append, List.head?_eq_some_head hl, Option.some_or] at h
  rw [List.head?_eq_some_head hl]
  exact h

theorem getLast?_right_of_ne_nil {ι : Type*} {l l' : List ι} {a : ι} (hl' : l' ≠ [])
    (h : (l ++ l').getLast? = some a) : l'.getLast? = some a := by
  rw [List.getLast?_append, List.getLast?_eq_some_getLast hl', Option.some_or] at h
  rw [List.getLast?_eq_some_getLast hl']
  exact h

/-- In a face cycle `s a r`, the dart after the last dart of `a` is the first dart of `r s`. -/
theorem succ_blocks {s a r : List M.Dart} {d e : M.Dart} (hL : M.IsFaceCycle (s ++ a ++ r))
    (ha : a.getLast? = some d) (hr : (r ++ s).head? = some e) : M.facePerm d = e := by
  have hc := (hL.rotate s.length).chain
  rw [List.append_assoc, List.rotate_append_length_eq, List.append_assoc] at hc
  exact (List.isChain_append.mp hc).2.2 d (Option.mem_def.mpr ha) e (Option.mem_def.mpr hr)

theorem firstTurn_of_face_run {c : List M.Dart} {a g b : M.Dart} {k : ℕ}
    (hpa : M.facePerm a = g) (hk : SafeRun M c g b k) : FirstTurn M c a b := by
  subst hpa
  exact firstTurn_of_safeRun hk

variable {X T Y U q B p A : List M.Dart}

theorem PocketSetting.ne_of_face (h : PocketSetting M X T Y U q B p A) {x y : M.Dart}
    (hx : x ∈ X ++ T ++ Y ++ U) (hy : y ∈ q ++ B ++ p ++ A) : x ≠ y :=
  fun hxy => h.face_ne x hx y hy (congrArg M.faceOf hxy)

theorem not_keep_T (h : PocketSetting M X T Y U q B p A) {t : M.Dart} (ht : t ∈ T) :
    ¬ walkKeep M (B ++ X) t := by
  have htw : t ∈ X ++ T ++ Y ++ U :=
    List.mem_append_left U (List.mem_append_left Y (List.mem_append_right X ht))
  have hαq : M.alpha t ∈ q ++ B ++ p ++ A :=
    List.mem_append_left A (List.mem_append_left p (List.mem_append_left B (h.cross_T t ht)))
  rintro (h₁ | h₁) <;> rcases List.mem_append.mp h₁ with h₂ | h₂
  · exact h.ne_of_face htw
      (List.mem_append_left A (List.mem_append_left p (List.mem_append_right q h₂))) rfl
  · exact ne_of_nodup h.walk.nodup (s := []) (m := []) (r := Y ++ U) (by simp) h₂ ht rfl
  · exact ne_of_nodup h.carrier.nodup (s := []) (m := []) (r := p ++ A) (by simp)
      (h.cross_T t ht) h₂ rfl
  · exact h.ne_of_face
      (List.mem_append_left U (List.mem_append_left Y (List.mem_append_left T h₂))) hαq rfl

theorem not_keep_U (h : PocketSetting M X T Y U q B p A) {u : M.Dart} (hu : u ∈ U) :
    ¬ walkKeep M (B ++ X) (M.alpha u) := by
  have huw : u ∈ X ++ T ++ Y ++ U := List.mem_append_right _ hu
  have hαp : M.alpha u ∈ q ++ B ++ p ++ A :=
    List.mem_append_left A (List.mem_append_right _ (h.cross_U u hu))
  rintro (h₁ | h₁) <;> rcases List.mem_append.mp h₁ with h₂ | h₂
  · exact ne_of_nodup h.carrier.nodup (s := q) (m := []) (r := A) (by simp) h₂
      (h.cross_U u hu) rfl
  · exact h.ne_of_face
      (List.mem_append_left U (List.mem_append_left Y (List.mem_append_left T h₂))) hαp rfl
  · rw [M.alpha_involutive u] at h₂
    exact h.ne_of_face huw
      (List.mem_append_left A (List.mem_append_left p (List.mem_append_right q h₂))) rfl
  · rw [M.alpha_involutive u] at h₂
    exact ne_of_nodup h.walk.nodup (s := []) (m := T ++ Y) (r := []) (by simp) h₂ hu rfl

theorem passHead_core {t e : M.Dart} {T' q' γ : List M.Dart}
    (h : PocketSetting M X (t :: T') Y U (q' ++ M.alpha t :: γ) B p A)
    (hγ : ∀ g, γ.getLast? = some g → M.sigma (M.facePerm g) = t)
    (he : (B ++ p).head? = some e) :
    ∃ k, SafeRun M (B ++ X) t e k := by
  have hnotT := not_keep_T h List.mem_cons_self
  have hBpA := head?_append_of_head? he A
  by_cases hγn : γ = []
  · subst hγn
    exact ⟨1, SafeRun.one hnotT (sigma_eq_of_facePerm_alpha (succ_blocks (s := q')
      (a := [M.alpha t]) (r := B ++ p ++ A) (d := M.alpha t)
      (faceCycle_of_eq h.carrier (by simp)) rfl
      (head?_append_of_head? hBpA q')))⟩
  obtain ⟨g₀, hg₀⟩ : ∃ g, γ.head? = some g := ⟨_, List.head?_eq_some_head hγn⟩
  obtain ⟨g₁, hg₁⟩ : ∃ g, γ.getLast? = some g := ⟨_, List.getLast?_eq_some_getLast hγn⟩
  have hfK1 : M.IsFaceCycle (q' ++ [M.alpha t] ++ (γ ++ (B ++ p ++ A))) :=
    faceCycle_of_eq h.carrier (by simp)
  have hfK2 : M.IsFaceCycle (q' ++ [M.alpha t] ++ γ ++ (B ++ p ++ A)) :=
    faceCycle_of_eq h.carrier (by simp)
  have hdg : M.sigma t = g₀ := sigma_eq_of_facePerm_alpha (succ_blocks (d := M.alpha t) hfK1 rfl
    (head?_append_of_head? (head?_append_of_head? hg₀ _) q'))
  have hfe : M.facePerm g₁ = e := succ_blocks hfK2 hg₁ (head?_append_of_head? hBpA _)
  have hed : M.sigma e = t := by
    rw [← hfe]
    exact hγ g₁ hg₁
  have hγnd : γ.Nodup := (List.nodup_append.mp (List.nodup_append.mp hfK2.nodup).1).2.1
  have hγchain : γ.IsChain fun a b => M.facePerm a = b :=
    hfK2.chain.infix ⟨q' ++ [M.alpha t], B ++ p ++ A, rfl⟩
  have hγmem : ∀ y ∈ γ, y ∈ q' ++ M.alpha t :: γ ++ B ++ p ++ A := fun y hy =>
    List.mem_append_left A (List.mem_append_left p (List.mem_append_left B
      (List.mem_append_right q' (List.mem_cons_of_mem _ hy))))
  have htw : t ∈ X ++ t :: T' ++ Y ++ U :=
    List.mem_append_left U (List.mem_append_left Y (List.mem_append_right X List.mem_cons_self))
  have heγ : e ∉ γ := fun hm => ne_of_nodup h.carrier.nodup (s := q' ++ [M.alpha t]) (m := [])
    (r := A) (by simp) hm (List.mem_of_mem_head? he) rfl
  have hαe : M.alpha e ∉ γ := fun hm => h.face_ne t htw _ (hγmem _ hm)
    (by rw [← facePerm_alpha hed, M.faceOf_facePerm])
  have hdγ : t ∉ γ := fun hm => h.ne_of_face htw (hγmem _ hm) rfl
  have hγc : ∀ y ∈ γ, y ∉ B ++ X := by
    intro y hy hyc
    rcases List.mem_append.mp hyc with hyB | hyX
    · exact ne_of_nodup h.carrier.nodup (s := q' ++ [M.alpha t]) (m := []) (r := p ++ A)
        (by simp) hy hyB rfl
    · exact h.ne_of_face (List.mem_append_left U (List.mem_append_left Y
        (List.mem_append_left _ hyX))) (hγmem _ hy) rfl
  have hc : ∀ y ∈ B ++ X, M.faceOf y = M.faceOf g₀ ∨ M.faceOf y = M.faceOf t := by
    intro y hy
    rcases List.mem_append.mp hy with hyB | hyX
    · exact Or.inl (face_eq h.carrier (List.mem_append_left A (List.mem_append_left p
        (List.mem_append_right _ hyB))) (hγmem _ (List.mem_of_mem_head? hg₀)))
    · exact Or.inr (face_eq h.walk (List.mem_append_left U (List.mem_append_left Y
        (List.mem_append_left _ hyX))) htw)
  obtain ⟨k, hk⟩ :=
    loop_safeRun h.planar hγnd hγchain hg₀ hg₁ hfe hed hdg heγ hαe hdγ hγc hc
  exact ⟨k + 1, (SafeRun.one hnotT hdg).trans hk⟩

/-- **Passing the head of the target window**: rotation from `T.head` reaches `(B p).head`
safely. -/
theorem passHead (h : PocketSetting M X T Y U q B p A) {t e : M.Dart} (ht : T.head? = some t)
    (he : (B ++ p).head? = some e) : ∃ k, SafeRun M (B ++ X) t e k := by
  obtain ⟨t', _, _, _, rfl, rfl, hγ⟩ := h.headT
  obtain rfl : t' = t := by simpa using ht
  exact passHead_core h hγ he

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.RotationTurns

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.RotationTurns.faceCycle_of_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.RotationTurns.ne_of_nodup
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.RotationTurns.face_eq
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.RotationTurns.sigma_eq_of_facePerm_alpha
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.RotationTurns.head?_append_of_head?
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.RotationTurns.head?_left_of_ne_nil
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.RotationTurns.getLast?_right_of_ne_nil
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.RotationTurns.succ_blocks
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.RotationTurns.firstTurn_of_face_run
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.RotationTurns.PocketSetting.ne_of_face
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.RotationTurns.not_keep_T
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.RotationTurns.not_keep_U
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.RotationTurns.passHead_core
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.RotationTurns.passHead
