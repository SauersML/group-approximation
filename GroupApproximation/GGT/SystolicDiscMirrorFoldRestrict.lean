import GroupApproximation.GGT.SystolicDiscMirrorFoldStage
import GroupApproximation.GGT.VanKampen.CombMapInvariantRestrict
import GroupApproximation.Meta.AxiomGuard

set_option linter.unusedSectionVars false

/-!
# Fold stages on one side (HC6, the mirror fold)

When a surgery splits the map of a stage into two connected pieces, the piece carrying the
exterior cycle is again a stage, and a pending digon on that piece deletes away.

* `reachSide`: the darts reached from one dart, an invariant set (`reachSide_alpha`,
  `reachSide_sigma`).
* `eq_or_eq_of_eqvGen_digon`: a digon whose two darts form one edge is a piece of its own.
* `FoldStage.restrictStage`: the stage on an invariant set of darts containing the exterior
  cycle, with the same boundary (`restrictStage_boundary`), fewer faces when the complement
  has a dart (`restrictStage_faceCount_lt`), planar when both pieces are connected and the map
  has Euler characteristic four (`restrictStage_planar`).
* `FoldStage.exists_disc_of_sides`: a stage of Euler characteristic four, every dart reached
  from `c` or from `c'` but not both, the exterior cycle on the side of `c` and a pending
  digon at `c`, gives a triangulated disc with the same boundary and three faces fewer.
-/

namespace GroupApproximation.Systolic

open GGT.VanKampen

universe u

variable {V : Type u} {X : TriangleComplex V}

/-- A map with a dart has a face. -/
theorem one_le_faceCount_of_dart (M : CombMap.{0}) (x : M.Dart) : 1 ≤ M.faceCount := by
  have : Nonempty M.Face := ⟨M.faceOf x⟩
  exact Nat.card_pos

/-- The darts reached from `c` by elementary moves. -/
def reachSide (M : CombMap.{0}) (c x : M.Dart) : Prop :=
  Relation.EqvGen M.Adjacent c x

theorem reachSide_alpha (M : CombMap.{0}) (c x : M.Dart) :
    reachSide M c (M.alpha x) ↔ reachSide M c x :=
  ⟨fun h => Relation.EqvGen.trans _ _ _ h
      (Relation.EqvGen.rel _ _ (Or.inl (M.alpha_involutive x))),
    fun h => Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.rel _ _ (Or.inl rfl))⟩

theorem reachSide_sigma (M : CombMap.{0}) (c x : M.Dart) :
    reachSide M c (M.sigma x) ↔ reachSide M c x :=
  ⟨fun h => Relation.EqvGen.trans _ _ _ h
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inr rfl))),
    fun h => Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.rel _ _ (Or.inr rfl))⟩

theorem reachSide_facePerm (M : CombMap.{0}) (c x : M.Dart) (h : reachSide M c x) :
    reachSide M c (M.facePerm x) :=
  Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.trans _ (M.alpha x) _
    (Relation.EqvGen.rel _ _ (Or.inl rfl)) (Relation.EqvGen.rel _ _ (Or.inr rfl)))

/-- **A digon forming one edge is a piece of its own.**  If `facePerm a = b`,
`facePerm b = a` and `alpha a = b`, every dart reached from `a` is `a` or `b`. -/
theorem eq_or_eq_of_eqvGen_digon (M : CombMap.{0}) {a b x : M.Dart} (hab : M.facePerm a = b)
    (hba : M.facePerm b = a) (hα : M.alpha a = b) (h : Relation.EqvGen M.Adjacent a x) :
    x = a ∨ x = b := by
  have hαb : M.alpha b = a := by rw [← hα, M.alpha_involutive]
  have hσa : M.sigma a = a := by rw [← Systolic.facePerm_alpha, hα, hba]
  have hσb : M.sigma b = b := by rw [← Systolic.facePerm_alpha, hαb, hab]
  have hA : ∀ y, (M.alpha y = a ∨ M.alpha y = b) ↔ (y = a ∨ y = b) := by
    intro y
    constructor
    · rintro (h1 | h1)
      · right
        rw [← hα, ← h1, M.alpha_involutive]
      · left
        rw [← hαb, ← h1, M.alpha_involutive]
    · rintro (h1 | h1)
      · rw [h1]
        exact Or.inr hα
      · rw [h1]
        exact Or.inl hαb
  have hS : ∀ y, (M.sigma y = a ∨ M.sigma y = b) ↔ (y = a ∨ y = b) := by
    intro y
    constructor
    · rintro (h1 | h1)
      · exact Or.inl (M.sigma.injective (h1.trans hσa.symm))
      · exact Or.inr (M.sigma.injective (h1.trans hσb.symm))
    · rintro (h1 | h1)
      · rw [h1]
        exact Or.inl hσa
      · rw [h1]
        exact Or.inr hσb
  exact (CombMap.iff_of_eqvGen M (fun y => y = a ∨ y = b) hA hS h).mp (Or.inl rfl)

namespace FoldStage

/-- A list inside a set lifts to the subtype. -/
theorem exists_map_subtypeVal {α : Type*} {P : α → Prop} :
    ∀ l : List α, (∀ x ∈ l, P x) → ∃ l' : List {x // P x}, l'.map Subtype.val = l
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨l', hl'⟩ := exists_map_subtypeVal l fun x hx => h x (List.mem_cons_of_mem a hx)
    exact ⟨⟨a, h a List.mem_cons_self⟩ :: l', by rw [List.map_cons, hl']⟩

/-! ### Restricting a stage -/

section Restrict

variable (S : FoldStage X) (T : S.map.Dart → Prop)
  (hα : ∀ x, T (S.map.alpha x) ↔ T x) (hσ : ∀ x, T (S.map.sigma x) ↔ T x)

/-- The exterior cycle lifted to an invariant set containing it. -/
noncomputable def restrictCyc (hT : ∀ z ∈ S.cyc, T z) : List (S.map.restrict T hα hσ).Dart :=
  (exists_map_subtypeVal S.cyc hT).choose

theorem map_val_restrictCyc (hT : ∀ z ∈ S.cyc, T z) :
    (S.restrictCyc T hα hσ hT).map Subtype.val = S.cyc :=
  (exists_map_subtypeVal S.cyc hT).choose_spec

theorem mem_restrictCyc_iff (hT : ∀ z ∈ S.cyc, T z) (x : (S.map.restrict T hα hσ).Dart) :
    x ∈ S.restrictCyc T hα hσ hT ↔ x.1 ∈ S.cyc := by
  rw [← S.map_val_restrictCyc T hα hσ hT]
  exact (List.mem_map_of_injective Subtype.val_injective).symm

theorem isFaceCycle_restrictCyc (hT : ∀ z ∈ S.cyc, T z) :
    (S.map.restrict T hα hσ).IsFaceCycle (S.restrictCyc T hα hσ hT) := by
  have hc := S.isFaceCycle
  rw [← S.map_val_restrictCyc T hα hσ hT] at hc
  have hne : S.restrictCyc T hα hσ hT ≠ [] := fun h => hc.ne_nil (List.map_eq_nil_iff.mpr h)
  refine ⟨hne, List.Nodup.of_map Subtype.val hc.nodup, ?_, ?_⟩
  · exact ((List.isChain_map Subtype.val).mp hc.chain).imp_of_mem_imp
      fun a b _ _ (h : S.map.facePerm a.1 = b.1) => Subtype.ext h
  · apply Subtype.ext
    have h' := hc.closes
    rw [List.getLast_map, List.head_map] at h'
    exact h'

/-- **The stage on an invariant set of darts** containing the exterior cycle. -/
noncomputable def restrictStage (hT : ∀ z ∈ S.cyc, T z) : FoldStage X where
  map := S.map.restrict T hα hσ
  lab := fun x => S.lab x.1
  lab_sigma := fun x => S.lab_sigma x.1
  adj := fun x => S.adj x.1
  cyc := S.restrictCyc T hα hσ hT
  isFaceCycle := S.isFaceCycle_restrictCyc T hα hσ hT
  bad := fun x => S.bad x.1
  bad_facePerm := fun x => S.bad_facePerm x.1
  cyc_bad := fun x hx => S.cyc_bad x.1 ((S.mem_restrictCyc_iff T hα hσ hT x).mp hx)
  tri := fun x hx hxb => S.tri_of_embed (N := S.map.restrict T hα hσ) (fun y => S.lab y.1)
    (S.isFaceCycle_restrictCyc T hα hσ hT) (fun y => S.bad y.1) (fun y => S.bad_facePerm y.1)
    Subtype.val Subtype.val_injective (fun _ => rfl)
    (fun y hy hm => hy ((S.mem_restrictCyc_iff T hα hσ hT y).mpr hm)) (fun _ h => h)
    (fun _ _ _ => rfl) x hx hxb

/-- Restricting keeps the boundary. -/
theorem restrictStage_boundary (hT : ∀ z ∈ S.cyc, T z) :
    (S.restrictStage T hα hσ hT).boundary = S.boundary := by
  apply boundary_eq_of_map_lab
  have e1 := congrArg (List.map S.lab) (S.map_val_restrictCyc T hα hσ hT)
  rw [List.map_map] at e1
  exact e1

/-- Restricting to a set missing a dart loses a face. -/
theorem restrictStage_faceCount_lt (hT : ∀ z ∈ S.cyc, T z) {c' : S.map.Dart} (hc' : ¬ T c') :
    (S.restrictStage T hα hσ hT).map.faceCount + 1 ≤ S.map.faceCount := by
  have h := S.map.faceCount_restrict_add T hα hσ
  have h1 := one_le_faceCount_of_dart
    (S.map.restrict (fun x => ¬ T x) (S.map.compl_alpha T hα) (S.map.compl_sigma T hσ)) ⟨c', hc'⟩
  show (S.map.restrict T hα hσ).faceCount + 1 ≤ S.map.faceCount
  omega

/-- Two connected pieces of a map of Euler characteristic four are planar. -/
theorem restrictStage_planar (hT : ∀ z ∈ S.cyc, T z) (h4 : S.map.eulerCharacteristic = 4)
    {c c' : S.map.Dart} (hc : T c) (hreach : ∀ x, T x → Relation.EqvGen S.map.Adjacent c x)
    (hc' : ¬ T c') (hreach' : ∀ x, ¬ T x → Relation.EqvGen S.map.Adjacent c' x) :
    (S.restrictStage T hα hσ hT).map.IsPlanar :=
  S.map.restrict_planar_of_euler_four T hα hσ h4 (S.map.restrict_connected T hα hσ hc hreach)
    (S.map.restrict_connected (fun x => ¬ T x) (S.map.compl_alpha T hα) (S.map.compl_sigma T hσ)
      hc' hreach')

end Restrict

/-! ### One side of a split stage -/

section Sides

variable (S : FoldStage X) (c : S.map.Dart)

/-- The stage on the darts reached from `c`. -/
noncomputable abbrev sideStage (hcyc : ∀ z ∈ S.cyc, reachSide S.map c z) : FoldStage X :=
  S.restrictStage (reachSide S.map c) (reachSide_alpha S.map c) (reachSide_sigma S.map c) hcyc

/-- **A pending digon at `c` on the side of `c`**, when the other pending darts lie off
that side. -/
theorem isDigon_side (hcyc : ∀ z ∈ S.cyc, reachSide S.map c z) (hbad : S.bad c)
    (hback : S.map.facePerm (S.map.facePerm c) = c)
    (himp : ∀ z, S.bad z → z = c ∨ z = S.map.facePerm c ∨ ¬ reachSide S.map c z) :
    IsDigon (S.sideStage c hcyc) ⟨c, Relation.EqvGen.refl c⟩
      ⟨S.map.facePerm c, reachSide_facePerm S.map c c (Relation.EqvGen.refl c)⟩
      (fun _ => False) :=
  { fwd := Subtype.ext rfl
    bwd := Subtype.ext hback
    alpha_ne := fun h => by
      have h' : S.map.alpha c = S.map.facePerm c := congrArg Subtype.val h
      have hz := List.head_mem S.isFaceCycle.ne_nil
      rcases eq_or_eq_of_eqvGen_digon S.map (a := c) rfl hback h' (hcyc _ hz) with h1 | h1
      · exact S.cyc_bad _ hz (by rw [h1]; exact hbad)
      · exact S.cyc_bad _ hz (by rw [h1]; exact (S.bad_facePerm c).mpr hbad)
    bad_a := hbad
    rest_facePerm := fun _ => Iff.rfl
    bad_imp := fun z hz => by
      rcases himp z.1 hz with h1 | h1 | h1
      · exact Or.inl (Subtype.ext h1)
      · exact Or.inr (Or.inl (Subtype.ext h1))
      · exact (h1 z.2).elim
    rest_imp := fun _ h => False.elim h }

/-- **One side of a split stage is a smaller disc.**  Let a stage of Euler characteristic
four have every dart reached from `c` or from `c'`, not `c'` from `c`, the exterior cycle on
the side of `c`, and a pending digon `c, facePerm c` whose other pending darts lie off that
side.  Then some triangulated disc with the same boundary has three faces fewer. -/
theorem exists_disc_of_sides {γ : List V} (h4 : S.map.eulerCharacteristic = 4) {c' : S.map.Dart}
    (hsplit : ∀ x, reachSide S.map c x ∨ reachSide S.map c' x) (hcc' : ¬ reachSide S.map c c')
    (hcyc : ∀ z ∈ S.cyc, reachSide S.map c z) (hbad : S.bad c)
    (hback : S.map.facePerm (S.map.facePerm c) = c)
    (himp : ∀ z, S.bad z → z = c ∨ z = S.map.facePerm c ∨ ¬ reachSide S.map c z)
    (hb : S.boundary = γ) :
    ∃ D : TriangulatedDisc X γ, D.innerFaceCount + 3 ≤ S.map.faceCount := by
  have hR : (S.sideStage c hcyc).map.IsPlanar :=
    S.restrictStage_planar (reachSide S.map c) (reachSide_alpha S.map c)
      (reachSide_sigma S.map c) hcyc h4 (Relation.EqvGen.refl c) (fun _ hx => hx) hcc'
      (fun x hx => (hsplit x).resolve_left hx)
  have hdig := S.isDigon_side c hcyc hbad hback himp
  obtain ⟨D, hD⟩ := (deleteDigon hdig).exists_triangulatedDisc (deleteDigon_planar hdig hR)
    (fun _ h => h) ((deleteDigon_boundary hdig).trans
      ((S.restrictStage_boundary (reachSide S.map c) (reachSide_alpha S.map c)
        (reachSide_sigma S.map c) hcyc).trans hb))
  have h1 := deleteDigon_faceCount hdig hR
  have h2 : (S.sideStage c hcyc).map.faceCount + 1 ≤ S.map.faceCount :=
    S.restrictStage_faceCount_lt (reachSide S.map c) (reachSide_alpha S.map c)
      (reachSide_sigma S.map c) hcyc hcc'
  exact ⟨D, by omega⟩

end Sides

end FoldStage

end GroupApproximation.Systolic

#audit_axioms GroupApproximation.Systolic.eq_or_eq_of_eqvGen_digon
#audit_axioms GroupApproximation.Systolic.FoldStage.restrictStage_boundary
#audit_axioms GroupApproximation.Systolic.FoldStage.restrictStage_faceCount_lt
#audit_axioms GroupApproximation.Systolic.FoldStage.restrictStage_planar
#audit_axioms GroupApproximation.Systolic.FoldStage.isDigon_side
#audit_axioms GroupApproximation.Systolic.FoldStage.exists_disc_of_sides
