import GroupApproximation.GGT.SystolicDiscMirrorFoldSteps
import GroupApproximation.GGT.VanKampen.FoldMap
import GroupApproximation.Meta.AxiomGuard

set_option linter.unusedSectionVars false

/-!
# The three moves of the distinct mirror fold

Let `d` be a dart between two different triangles `[d, d1, d2]` and `[alpha d, e1, e2]` whose far
corners `d2` and `e2` start at different vertices.  The distinct case of HC6 removes both triangles
in three moves:

1. delete the edge of `d`; the triangles merge into the square `[d1, d2, e1, e2]` (`MirrorQuad.M1`);
2. fold the pair `d2 e1` (`FoldMap`); the square becomes the digon `[e2, d1]` (`MirrorQuad.M2`);
3. delete the edge of `e2`; the digon disappears (`MirrorQuad.M3`).

`MirrorQuad` collects the darts and the conditions the moves use.  The final map is planar
(`MirrorQuad.planar3`) and has two faces fewer (`MirrorQuad.faceCount_add_two`).

## Manuscript status

Infrastructure for the torsion-free hyperbolic property (T) witness on the
Kotowski--Ollivier route; certifies no manuscript step on its own.
-/

namespace GroupApproximation.GGT.VanKampen.EdgeDeletion

universe u

variable {M : CombMap.{u}} [DecidableEq M.Dart] {a : M.Dart}

/-- Face rotation of the deleted map at a dart whose old successor survives. -/
theorem facePerm_eq_of_ne {x y : Dart M a} (h1 : M.facePerm (value M a x) ≠ a)
    (h2 : M.facePerm (value M a x) ≠ M.alpha a) (h : M.facePerm (value M a x) = value M a y) :
    (toCombMap M a).facePerm x = y :=
  value_injective M a ((value_facePerm_eq_next M a x).trans ((next_of_ne_of_ne M a h1 h2).trans h))

/-- Face rotation of the deleted map at a dart whose old successor was `a`. -/
theorem facePerm_eq_of_eq {x y : Dart M a} (h1 : M.facePerm (value M a x) = a)
    (h2 : M.facePerm (M.alpha a) ≠ M.alpha a) (h : M.facePerm (M.alpha a) = value M a y) :
    (toCombMap M a).facePerm x = y := by
  apply value_injective M a
  rw [value_facePerm_eq_next, next, if_pos h1, if_neg h2, h]

/-- Face rotation of the deleted map at a dart whose old successor was `alpha a`. -/
theorem facePerm_eq_of_eq_reverse {x y : Dart M a} (h1 : M.facePerm (value M a x) = M.alpha a)
    (h2 : M.facePerm a ≠ a) (h : M.facePerm a = value M a y) :
    (toCombMap M a).facePerm x = y := by
  have h0 : M.facePerm (value M a x) ≠ a := by
    rw [h1]
    exact M.alpha_fixedPointFree a
  apply value_injective M a
  rw [value_facePerm_eq_next, next, if_neg h0, if_pos h1, if_neg h2, h]

end GroupApproximation.GGT.VanKampen.EdgeDeletion

namespace GroupApproximation.GGT.VanKampen

open scoped Classical

noncomputable section

universe u

/-- Two different triangles `[d, d1, d2]` and `[alpha d, e1, e2]` on the edge of `d`, whose far
corners `d2` and `e2` start at different vertices, with the conditions the three moves use. -/
structure MirrorQuad (M : CombMap.{u}) where
  d : M.Dart
  d1 : M.Dart
  d2 : M.Dart
  e1 : M.Dart
  e2 : M.Dart
  f_d : M.facePerm d = d1
  f_d1 : M.facePerm d1 = d2
  f_d2 : M.facePerm d2 = d
  f_ad : M.facePerm (M.alpha d) = e1
  f_e1 : M.facePerm e1 = e2
  f_e2 : M.facePerm e2 = M.alpha d
  d1_ne_d : d1 ≠ d
  d2_ne_d : d2 ≠ d
  e1_ne_d : e1 ≠ d
  e2_ne_d : e2 ≠ d
  d1_ne_ad : d1 ≠ M.alpha d
  d2_ne_ad : d2 ≠ M.alpha d
  e1_ne_ad : e1 ≠ M.alpha d
  e2_ne_ad : e2 ≠ M.alpha d
  d1_ne_e1 : d1 ≠ e1
  d2_ne_e1 : d2 ≠ e1
  e2_ne_e1 : e2 ≠ e1
  e2_ne_d1 : e2 ≠ d1
  d2_ne_d1 : d2 ≠ d1
  d2_ne_e2 : d2 ≠ e2
  e1_ne_ad2 : e1 ≠ M.alpha d2
  d1_ne_ae1 : d1 ≠ M.alpha e1
  d2_ne_ae1 : d2 ≠ M.alpha e1
  e2_ne_ae1 : e2 ≠ M.alpha e1
  d1_ne_ae2 : d1 ≠ M.alpha e2
  d2_ne_ae2 : d2 ≠ M.alpha e2
  ends_ne : M.vertexOf (M.alpha d1) ≠ M.vertexOf (M.alpha e1)
  face_ne : M.faceOf d ≠ M.faceOf (M.alpha d)

namespace MirrorQuad

variable {M : CombMap.{u}} (Q : MirrorQuad M)

/-! ### The first move: delete the edge of `d` -/

/-- The square: the map with the edge of `d` deleted. -/
abbrev M1 : CombMap.{u} := EdgeDeletion.toCombMap M Q.d

/-- The dart `d1` of the square. -/
def d1' : Q.M1.Dart := EdgeDeletion.ofValue M Q.d Q.d1 Q.d1_ne_d Q.d1_ne_ad

/-- The dart `d2` of the square. -/
def d2' : Q.M1.Dart := EdgeDeletion.ofValue M Q.d Q.d2 Q.d2_ne_d Q.d2_ne_ad

/-- The dart `e1` of the square. -/
def e1' : Q.M1.Dart := EdgeDeletion.ofValue M Q.d Q.e1 Q.e1_ne_d Q.e1_ne_ad

/-- The dart `e2` of the square. -/
def e2' : Q.M1.Dart := EdgeDeletion.ofValue M Q.d Q.e2 Q.e2_ne_d Q.e2_ne_ad

theorem value1_alpha (x : Q.M1.Dart) :
    EdgeDeletion.value M Q.d (Q.M1.alpha x) = M.alpha (EdgeDeletion.value M Q.d x) :=
  EdgeDeletion.value_alpha x

theorem ne1 {x y : Q.M1.Dart} (h : EdgeDeletion.value M Q.d x ≠ EdgeDeletion.value M Q.d y) :
    x ≠ y :=
  fun e => h (congrArg (EdgeDeletion.value M Q.d) e)

theorem ne1_alpha {x y : Q.M1.Dart}
    (h : EdgeDeletion.value M Q.d x ≠ M.alpha (EdgeDeletion.value M Q.d y)) : x ≠ Q.M1.alpha y :=
  fun e => h ((congrArg (EdgeDeletion.value M Q.d) e).trans (Q.value1_alpha y))

theorem f1_d1' : Q.M1.facePerm Q.d1' = Q.d2' := by
  apply EdgeDeletion.facePerm_eq_of_ne
  · show M.facePerm Q.d1 ≠ Q.d
    rw [Q.f_d1]
    exact Q.d2_ne_d
  · show M.facePerm Q.d1 ≠ M.alpha Q.d
    rw [Q.f_d1]
    exact Q.d2_ne_ad
  · exact Q.f_d1

theorem f1_d2' : Q.M1.facePerm Q.d2' = Q.e1' := by
  apply EdgeDeletion.facePerm_eq_of_eq
  · exact Q.f_d2
  · rw [Q.f_ad]
    exact Q.e1_ne_ad
  · exact Q.f_ad

theorem f1_e1' : Q.M1.facePerm Q.e1' = Q.e2' := by
  apply EdgeDeletion.facePerm_eq_of_ne
  · show M.facePerm Q.e1 ≠ Q.d
    rw [Q.f_e1]
    exact Q.e2_ne_d
  · show M.facePerm Q.e1 ≠ M.alpha Q.d
    rw [Q.f_e1]
    exact Q.e2_ne_ad
  · exact Q.f_e1

theorem f1_e2' : Q.M1.facePerm Q.e2' = Q.d1' := by
  apply EdgeDeletion.facePerm_eq_of_eq_reverse
  · exact Q.f_e2
  · rw [Q.f_d]
    exact Q.d1_ne_d
  · exact Q.f_d

/-- **The pair `d2 e1` of the square can be folded.** -/
theorem isFoldable : FoldMap.IsFoldable Q.M1 Q.d1' Q.d2' Q.e1' where
  prev := Q.f1_d1'
  next := Q.f1_d2'
  prev_ne_next := Q.ne1 Q.d1_ne_e1
  not_spur := Q.ne1_alpha Q.e1_ne_ad2
  distinct_ends := fun h => by
    have h1 := (EdgeDeletion.vertexOf_eq_iff M Q.d _ _).mp ((CombMap.vertexOf_eq_iff _ _ _).mpr h)
    rw [Q.value1_alpha, Q.value1_alpha] at h1
    exact Q.ends_ne h1

theorem planar1 (hM : M.IsPlanar) : Q.M1.IsPlanar :=
  EdgeDeletion.planar_of_neFace M Q.d hM Q.d1' Q.face_ne

theorem faceCount1 (hM : M.IsPlanar) : Q.M1.faceCount + 1 = M.faceCount := by
  have hbal : Q.M1.faceCount + M.vertexCount + 1 = Q.M1.vertexCount + M.faceCount :=
    EdgeDeletion.faceCount_balance_of_neFace M Q.d Q.face_ne
  have hv : Q.M1.vertexCount = M.vertexCount :=
    EdgeDeletion.vertexCount_eq_of_neFace M Q.d hM.1 Q.d1' Q.face_ne
  omega

/-! ### The second move: fold `d2 e1` -/

/-- The square with the ends of the pair `d2 e1` joined. -/
abbrev J : CombMap.{u} := FoldMap.joined Q.M1 Q.d1' Q.e1'

/-- The map after folding `d2 e1`. -/
abbrev M2 : CombMap.{u} := FoldMap.toCombMap Q.M1 Q.d1' Q.e1'

/-- The dart `d1` after the fold. -/
def d1'' : Q.M2.Dart :=
  EdgeDeletion.ofValue Q.J Q.e1' Q.d1' (Q.ne1 Q.d1_ne_e1)
    (show Q.d1' ≠ Q.M1.alpha Q.e1' from Q.ne1_alpha Q.d1_ne_ae1)

/-- The dart `d2` after the fold. -/
def d2'' : Q.M2.Dart :=
  EdgeDeletion.ofValue Q.J Q.e1' Q.d2' (Q.ne1 Q.d2_ne_e1)
    (show Q.d2' ≠ Q.M1.alpha Q.e1' from Q.ne1_alpha Q.d2_ne_ae1)

/-- The dart `e2` after the fold. -/
def e2'' : Q.M2.Dart :=
  EdgeDeletion.ofValue Q.J Q.e1' Q.e2' (Q.ne1 Q.e2_ne_e1)
    (show Q.e2' ≠ Q.M1.alpha Q.e1' from Q.ne1_alpha Q.e2_ne_ae1)

theorem value2_alpha (x : Q.M2.Dart) :
    EdgeDeletion.value Q.J Q.e1' (Q.M2.alpha x) = Q.J.alpha (EdgeDeletion.value Q.J Q.e1' x) :=
  EdgeDeletion.value_alpha x

/-- Reversing a dart of the folded map, read in the original map. -/
theorem vv_alpha (x : Q.M2.Dart) :
    EdgeDeletion.value M Q.d (EdgeDeletion.value Q.J Q.e1' (Q.M2.alpha x)) =
      M.alpha (EdgeDeletion.value M Q.d (EdgeDeletion.value Q.J Q.e1' x)) := by
  rw [Q.value2_alpha]
  exact Q.value1_alpha _

theorem ne2 {x y : Q.M2.Dart}
    (h : EdgeDeletion.value M Q.d (EdgeDeletion.value Q.J Q.e1' x) ≠
      EdgeDeletion.value M Q.d (EdgeDeletion.value Q.J Q.e1' y)) : x ≠ y :=
  fun e => h (congrArg (fun z : Q.M2.Dart =>
    EdgeDeletion.value M Q.d (EdgeDeletion.value Q.J Q.e1' z)) e)

theorem f2_d1'' : Q.M2.facePerm Q.d1'' = Q.e2'' := by
  have hJ : Q.J.facePerm Q.d1' = Q.e2' := by
    rw [FoldMap.joined_facePerm_prev, Q.f1_e1']
  apply EdgeDeletion.facePerm_eq_of_ne
  · show Q.J.facePerm Q.d1' ≠ Q.e1'
    rw [hJ]
    exact Q.ne1 Q.e2_ne_e1
  · show Q.J.facePerm Q.d1' ≠ Q.M1.alpha Q.e1'
    rw [hJ]
    exact Q.ne1_alpha Q.e2_ne_ae1
  · exact hJ

theorem f2_e2'' : Q.M2.facePerm Q.e2'' = Q.d1'' := by
  have h1 : Q.e2' ≠ Q.d1' := Q.ne1 Q.e2_ne_d1
  have h2 : Q.e2' ≠ Q.e1' := Q.ne1 Q.e2_ne_e1
  have hJ : Q.J.facePerm Q.e2' = Q.d1' := by
    rw [FoldMap.joined_facePerm_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Q.f1_e2']
  apply EdgeDeletion.facePerm_eq_of_ne
  · show Q.J.facePerm Q.e2' ≠ Q.e1'
    rw [hJ]
    exact Q.ne1 Q.d1_ne_e1
  · show Q.J.facePerm Q.e2' ≠ Q.M1.alpha Q.e1'
    rw [hJ]
    exact Q.ne1_alpha Q.d1_ne_ae1
  · exact hJ

theorem planar2 (hM : M.IsPlanar) : Q.M2.IsPlanar :=
  FoldMap.planar (Q.planar1 hM) Q.isFoldable

/-! ### The third move: delete the edge of `e2` -/

theorem e2''_ne_d1'' : Q.e2'' ≠ Q.d1'' :=
  Q.ne2 Q.e2_ne_d1

theorem alpha_e2''_ne_d1'' : Q.M2.alpha Q.e2'' ≠ Q.d1'' := by
  intro h
  have h1 := congrArg (EdgeDeletion.value M Q.d) (congrArg (EdgeDeletion.value Q.J Q.e1') h)
  rw [Q.vv_alpha] at h1
  exact Q.d1_ne_ae2 h1.symm

theorem d2''_ne_alpha_e2'' : Q.d2'' ≠ Q.M2.alpha Q.e2'' := by
  intro h
  have h1 := congrArg (EdgeDeletion.value M Q.d) (congrArg (EdgeDeletion.value Q.J Q.e1') h)
  rw [Q.vv_alpha] at h1
  exact Q.d2_ne_ae2 h1

/-- **After the fold, `[e2, d1]` is a digon.** -/
theorem digon2 : Q.M2.IsFaceCycle [Q.e2'', Q.d1''] where
  ne_nil := List.cons_ne_nil _ _
  nodup := List.nodup_cons.mpr
    ⟨fun h => Q.e2''_ne_d1'' (List.mem_singleton.mp h), List.nodup_singleton _⟩
  chain := List.isChain_pair.mpr Q.f2_e2''
  closes := Q.f2_d1''

theorem face_ne2 : Q.M2.faceOf Q.e2'' ≠ Q.M2.faceOf (Q.M2.alpha Q.e2'') := by
  intro h
  have hm : Q.M2.alpha Q.e2'' ∈ [Q.e2'', Q.d1''] := (Q.digon2.mem_iff _).mpr h.symm
  rcases List.mem_cons.mp hm with h1 | h1
  · exact Q.M2.alpha_fixedPointFree _ h1
  · exact Q.alpha_e2''_ne_d1'' (List.mem_singleton.mp h1)

/-- The map after deleting the edge of `e2`. -/
abbrev M3 : CombMap.{u} := EdgeDeletion.toCombMap Q.M2 Q.e2''

/-- The dart `d1` of the final map. -/
def d1''' : Q.M3.Dart :=
  EdgeDeletion.ofValue Q.M2 Q.e2'' Q.d1'' Q.e2''_ne_d1''.symm Q.alpha_e2''_ne_d1''.symm

/-- The dart `d2` of the final map. -/
def d2''' : Q.M3.Dart :=
  EdgeDeletion.ofValue Q.M2 Q.e2'' Q.d2'' (Q.ne2 Q.d2_ne_e2) Q.d2''_ne_alpha_e2''

/-- **The final map is planar.** -/
theorem planar3 (hM : M.IsPlanar) : Q.M3.IsPlanar :=
  EdgeDeletion.planar_of_neFace Q.M2 Q.e2'' (Q.planar2 hM) Q.d1''' Q.face_ne2

/-- **The three moves remove two faces.** -/
theorem faceCount_add_two (hM : M.IsPlanar) : Q.M3.faceCount + 2 = M.faceCount := by
  have hbal : Q.M3.faceCount + Q.M2.vertexCount + 1 = Q.M3.vertexCount + Q.M2.faceCount :=
    EdgeDeletion.faceCount_balance_of_neFace Q.M2 Q.e2'' Q.face_ne2
  have hv : Q.M3.vertexCount = Q.M2.vertexCount :=
    EdgeDeletion.vertexCount_eq_of_neFace Q.M2 Q.e2'' (Q.planar2 hM).1 Q.d1''' Q.face_ne2
  have h2 : Q.M2.faceCount = Q.M1.faceCount := FoldMap.faceCount_eq (Q.planar1 hM) Q.isFoldable
  have h1 : Q.M1.faceCount + 1 = M.faceCount := Q.faceCount1 hM
  omega

end MirrorQuad

end

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.facePerm_eq_of_eq
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.facePerm_eq_of_eq_reverse
#audit_axioms GroupApproximation.GGT.VanKampen.MirrorQuad.isFoldable
#audit_axioms GroupApproximation.GGT.VanKampen.MirrorQuad.digon2
#audit_axioms GroupApproximation.GGT.VanKampen.MirrorQuad.planar3
#audit_axioms GroupApproximation.GGT.VanKampen.MirrorQuad.faceCount_add_two
