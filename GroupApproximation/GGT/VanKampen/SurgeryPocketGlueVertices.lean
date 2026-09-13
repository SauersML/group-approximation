import GroupApproximation.GGT.VanKampen.SurgeryPocketGlueCount
import GroupApproximation.GGT.VanKampen.CombMapRestriction
import GroupApproximation.Meta.AxiomGuard

/-!
# Vertices of the glued map

A restriction keeps the vertices meeting a retained dart, so the vertices of an ambient map
are the vertices of the restriction together with the vertices meeting no retained dart
(`vertexCount_eq_add_of_isRestriction`).  For the reclosed pocket inside `M` these dead
vertices are the vertices all of whose darts are internal to `faces`; for `X` inside the glued
map they are the vertices with no dart of `X`.  On internal darts the glued vertex rotation is
the vertex rotation of `M`, so the two kinds of dead vertices correspond, and the glued map and
the pocket together have as many vertices as `M` and `X` together (`Seam.glue_vertexCount`).
-/

noncomputable section

namespace GroupApproximation.GGT.VanKampen.Surgery.PocketGlue

open Equiv MapCollapse

universe v

/-- The ambient vertices are the retained vertices and the vertices meeting no retained
dart. -/
theorem vertexCount_eq_add_of_isRestriction {M N : CombMap.{v}} {e : N.Dart ↪ M.Dart}
    (h : M.IsRestriction N e) :
    M.vertexCount =
      N.vertexCount + Nat.card {c : M.Vertex // ∀ d : N.Dart, M.vertexOf (e d) ≠ c} := by
  classical
  have h1 : N.vertexCount = Nat.card {c : M.Vertex // ∃ d : N.Dart, M.vertexOf (e d) = c} :=
    Nat.card_congr (PermFirstReturn.orbitEquiv M.sigma N.sigma e h.sigma_firstReturn)
  have h2 : Nat.card {c : M.Vertex // ∃ d : N.Dart, M.vertexOf (e d) = c} +
      Nat.card {c : M.Vertex // ¬∃ d : N.Dart, M.vertexOf (e d) = c} = M.vertexCount :=
    card_sum_compl (fun c : M.Vertex => ∃ d : N.Dart, M.vertexOf (e d) = c)
  have h3 : Nat.card {c : M.Vertex // ¬∃ d : N.Dart, M.vertexOf (e d) = c} =
      Nat.card {c : M.Vertex // ∀ d : N.Dart, M.vertexOf (e d) ≠ c} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => not_exists)
  omega

theorem vertexOf_sigma_pow (N : CombMap.{v}) (n : ℕ) (d : N.Dart) :
    N.vertexOf ((N.sigma ^ n) d) = N.vertexOf d := by
  induction n with
  | zero => rw [pow_zero, Perm.one_apply]
  | succ n ih => rw [pow_succ', Perm.mul_apply, N.vertexOf_sigma, ih]

namespace Seam

variable {M X : CombMap.{v}} (S : Seam M X)

theorem inr_mem_range (x : {x : X.Dart // X.faceOf x ≠ S.outer}) :
    (Sum.inr x : S.GlueDart) ∈ Set.range S.glueEmbedding :=
  Set.mem_range.2 ⟨x.1, S.glueEmbedding_of_ne x.1 x.2⟩

theorem mem_of_inl_notMem_range (d : {d : M.Dart // M.faceOf d ∈ S.faces})
    (h : (Sum.inl d : S.GlueDart) ∉ Set.range S.glueEmbedding) :
    M.faceOf (M.alpha d.1) ∈ S.faces := by
  by_contra hn
  exact h (Set.mem_range.2
    ⟨(S.seamEquiv ⟨d.1, d.2, hn⟩).1, S.glueEmbedding_seam ⟨d.1, d.2, hn⟩⟩)

/-- A vertex of `M` all of whose darts are internal to `faces`. -/
def DeadM (c : M.Vertex) : Prop :=
  ∀ d : M.Dart, M.vertexOf d = c → InternalDart M S.faces d

/-- A vertex of the glued map with no dart of `X`. -/
def DeadY (c : S.glueMap.Vertex) : Prop :=
  ∀ g : S.GlueDart, S.glueMap.vertexOf g = c → g ∉ Set.range S.glueEmbedding

theorem deadM_pow {d : M.Dart} (h : S.DeadM (M.vertexOf d)) (n : ℕ) :
    InternalDart M S.faces ((M.sigma ^ n) d) :=
  h _ (vertexOf_sigma_pow M n d)

theorem deadY_pow {g : S.GlueDart} (h : S.DeadY (S.glueMap.vertexOf g)) (n : ℕ) :
    ((S.glueMap.sigma ^ n) g : S.GlueDart) ∉ Set.range S.glueEmbedding :=
  h _ (vertexOf_sigma_pow S.glueMap n g)

/-- Along glued darts off the image of `X`, the glued vertex rotation is the vertex rotation
of `M`. -/
theorem glueSigma_pow_of_notMem (d : {d : M.Dart // M.faceOf d ∈ S.faces})
    (h : ∀ k : ℕ, ((S.glueMap.sigma ^ k) (Sum.inl d : S.GlueDart) : S.GlueDart) ∉
      Set.range S.glueEmbedding) (n : ℕ) :
    ∃ e : {d : M.Dart // M.faceOf d ∈ S.faces}, e.1 = (M.sigma ^ n) d.1 ∧
      (S.glueMap.sigma ^ n) (Sum.inl d : S.GlueDart) = Sum.inl e := by
  induction n with
  | zero =>
    refine ⟨d, ?_, ?_⟩
    · rw [pow_zero, Perm.one_apply]
    · rw [pow_zero, Perm.one_apply]
  | succ n ih =>
    obtain ⟨e, he, hpow⟩ := ih
    have hnot : (Sum.inl e : S.GlueDart) ∉ Set.range S.glueEmbedding := by
      rewrite [← hpow]
      exact h n
    have hα := S.mem_of_inl_notMem_range e hnot
    refine ⟨⟨M.sigma e.1, S.mem_sigma e.1 hα⟩, ?_, ?_⟩
    · show M.sigma e.1 = (M.sigma ^ (n + 1)) d.1
      rw [pow_succ', Perm.mul_apply, he]
    · rewrite [pow_succ', Perm.mul_apply, hpow]
      exact S.glueSigma_inl_of_mem e hα

theorem deadY_inl {d : M.Dart} (h : S.DeadM (M.vertexOf d)) :
    S.DeadY (S.glueMap.vertexOf (Sum.inl ⟨d, (h d rfl).1⟩ : S.GlueDart)) := by
  intro g hg hmem
  have hsame : S.glueMap.sigma.SameCycle (Sum.inl ⟨d, (h d rfl).1⟩ : S.GlueDart) g :=
    ((S.glueMap.vertexOf_eq_iff _ _).1 hg).symm
  obtain ⟨n, hn⟩ := hsame.exists_nat_pow_eq
  obtain ⟨e, he, hpow⟩ :=
    S.glueSigma_pow_inl ⟨d, (h d rfl).1⟩ n (fun k _ => S.deadM_pow h k)
  have hin : InternalDart M S.faces e.1 := by
    rw [he]
    exact S.deadM_pow h n
  rewrite [← hn, hpow] at hmem
  exact S.inl_notMem_range e hin.2 hmem

/-- A dart of `M` on the boundary of `faces`. -/
def someDart : M.Dart := (Classical.choice (nonempty_boundaryDart M S.faces S.boundary)).1

/-- The dart of `M` under a glued dart based on `faces`. -/
def leftDart : S.GlueDart → M.Dart := Sum.elim Subtype.val (fun _ => S.someDart)

/-- Darts of `M` at vertices all of whose darts are internal. -/
abbrev DeadDartM := {d : M.Dart // S.DeadM (M.vertexOf d)}

/-- Darts of the glued map at vertices with no dart of `X`. -/
abbrev DeadDartY := {g : S.glueMap.Dart // S.DeadY (S.glueMap.vertexOf g)}

theorem deadM_leftDart (g : S.DeadDartY) : S.DeadM (M.vertexOf (S.leftDart g.1)) := by
  obtain ⟨g | x, h⟩ := g
  · intro d' hd'
    have hsame : M.sigma.SameCycle g.1 d' := ((M.vertexOf_eq_iff _ _).1 hd').symm
    obtain ⟨n, hn⟩ := hsame.exists_nat_pow_eq
    obtain ⟨e, he, hpow⟩ := S.glueSigma_pow_of_notMem g (fun k => S.deadY_pow h k) n
    have hnot : (Sum.inl e : S.GlueDart) ∉ Set.range S.glueEmbedding := by
      rewrite [← hpow]
      exact S.deadY_pow h n
    rw [← hn, ← he]
    exact ⟨e.2, S.mem_of_inl_notMem_range e hnot⟩
  · exact absurd (S.inr_mem_range x) (h _ rfl)

/-- The dead darts of `M` are the dead darts of the glued map. -/
def deadDartEquiv : S.DeadDartM ≃ S.DeadDartY where
  toFun d := ⟨Sum.inl ⟨d.1, (d.2 d.1 rfl).1⟩, S.deadY_inl d.2⟩
  invFun g := ⟨S.leftDart g.1, S.deadM_leftDart g⟩
  left_inv d := Subtype.ext rfl
  right_inv g := by
    obtain ⟨g | x, h⟩ := g
    · exact Subtype.ext rfl
    · exact absurd (S.inr_mem_range x) (h _ rfl)

/-- Vertex rotation on the dead darts of `M`. -/
def deadSigmaM : Perm S.DeadDartM :=
  M.sigma.subtypePerm (p := fun d => S.DeadM (M.vertexOf d))
    (fun d => iff_of_eq (congrArg S.DeadM (M.vertexOf_sigma d)))

/-- Vertex rotation on the dead darts of the glued map. -/
def deadSigmaY : Perm S.DeadDartY :=
  S.glueMap.sigma.subtypePerm (p := fun g => S.DeadY (S.glueMap.vertexOf g))
    (fun g => iff_of_eq (congrArg S.DeadY (S.glueMap.vertexOf_sigma g)))

theorem deadDartEquiv_permCongr :
    S.deadDartEquiv.permCongr S.deadSigmaM = S.deadSigmaY := by
  apply Equiv.ext
  intro g
  obtain ⟨d, rfl⟩ := S.deadDartEquiv.surjective g
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  exact Subtype.ext (S.glueSigma_inl_of_mem ⟨d.1, (d.2 d.1 rfl).1⟩ (d.2 d.1 rfl).2).symm

theorem card_deadM_eq_card_deadY :
    Nat.card {c : M.Vertex // S.DeadM c} = Nat.card {c : S.glueMap.Vertex // S.DeadY c} := by
  have h1 : Nat.card (CombMap.Orbit S.deadSigmaM) = Nat.card {c : M.Vertex // S.DeadM c} :=
    Nat.card_congr (orbitSubtypeEquiv M.sigma S.DeadM
      (fun d => iff_of_eq (congrArg S.DeadM (M.vertexOf_sigma d))))
  have h2 : Nat.card (CombMap.Orbit S.deadSigmaY) =
      Nat.card {c : S.glueMap.Vertex // S.DeadY c} :=
    Nat.card_congr (orbitSubtypeEquiv S.glueMap.sigma S.DeadY
      (fun g => iff_of_eq (congrArg S.DeadY (S.glueMap.vertexOf_sigma g))))
  have h3 : Nat.card (CombMap.Orbit S.deadSigmaM) = Nat.card (CombMap.Orbit S.deadSigmaY) :=
    Nat.card_congr ((orbitPermCongr S.deadDartEquiv S.deadSigmaM).trans
      (orbitCongrOfEq S.deadDartEquiv_permCongr))
  omega

theorem glue_vertexCount (hwalk : S.boundary.FollowsBoundary) :
    S.glueMap.vertexCount + S.piece.vertexCount = M.vertexCount + X.vertexCount := by
  have hM : M.vertexCount = S.piece.vertexCount +
      Nat.card {c : M.Vertex // ∀ d : KeptDart M S.faces, M.vertexOf d.1 ≠ c} :=
    vertexCount_eq_add_of_isRestriction (reclosed_isRestriction M S.faces S.boundary hwalk)
  have hY : S.glueMap.vertexCount = X.vertexCount +
      Nat.card {c : S.glueMap.Vertex //
        ∀ x : X.Dart, S.glueMap.vertexOf (S.glueEmbedding x) ≠ c} :=
    vertexCount_eq_add_of_isRestriction (S.glue_isRestriction hwalk)
  have hdM : Nat.card {c : M.Vertex // ∀ d : KeptDart M S.faces, M.vertexOf d.1 ≠ c} =
      Nat.card {c : M.Vertex // S.DeadM c} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ =>
      ⟨fun h d hd => Classical.byContradiction fun hn => h ⟨d, hn⟩ hd,
        fun h d hd => d.2 (h d.1 hd)⟩)
  have hdY : Nat.card {c : S.glueMap.Vertex //
        ∀ x : X.Dart, S.glueMap.vertexOf (S.glueEmbedding x) ≠ c} =
      Nat.card {c : S.glueMap.Vertex // S.DeadY c} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ =>
      ⟨fun h g hg hmem => by
          obtain ⟨x, hx⟩ := hmem
          exact h x ((congrArg S.glueMap.vertexOf hx).trans hg),
        fun h x hx => h (S.glueEmbedding x) hx (Set.mem_range_self x)⟩)
  have hd := S.card_deadM_eq_card_deadY
  omega

end Seam

end GroupApproximation.GGT.VanKampen.Surgery.PocketGlue

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.PocketGlue.vertexCount_eq_add_of_isRestriction
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.PocketGlue.Seam.card_deadM_eq_card_deadY
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.PocketGlue.Seam.glue_vertexCount
