import GroupApproximation.GGT.SystolicDiscMirrorFoldEmbed
import GroupApproximation.GGT.SystolicDiscMirrorFoldCases
import GroupApproximation.Meta.AxiomGuard

set_option linter.unusedSectionVars false

/-!
# HC6, distinct third vertices

Two inner triangles `[d, d1, d2]` and `[alpha d, e1, e2]` of a cycle disc on the two sides of an
edge, whose third corners carry one label at two different vertices, form a `MirrorQuad`: the
labels of the two triangles separate their darts, and the two third vertices separate the rest.
The three moves of `MirrorQuad` produce a planar map that embeds in the disc along face rotation
and reads its labels compatibly, so it is a cycle disc with the same boundary and two faces fewer.

* `CycleDisc.DistinctPair.quad`: the quadrilateral of the pair.
* `CycleDisc.DistinctPair.exists_fold`: the folded cycle disc.
* `mirrorFoldDistinct`: `MirrorFoldDistinctStatement X`.

## Manuscript status

Infrastructure for the torsion-free hyperbolic property (T) witness on the
Kotowski--Ollivier route; certifies no manuscript step on its own.
-/

namespace GroupApproximation.Systolic

open GGT.VanKampen

universe u

variable {V : Type u} {X : TriangleComplex V}

namespace CycleDisc

variable (D : CycleDisc X)

/-- The start label of a face successor is the end label. -/
theorem lab_facePerm (z : D.map.Dart) : D.lab (D.map.facePerm z) = D.lab (D.map.alpha z) := by
  rw [Systolic.facePerm_apply, D.lab_sigma]

theorem ne_of_lab {x y : D.map.Dart} (h : D.lab x ≠ D.lab y) : x ≠ y :=
  fun e => h (congrArg D.lab e)

theorem ne_of_lab_alpha {x y : D.map.Dart} (h : D.lab (D.map.alpha x) ≠ D.lab (D.map.alpha y)) :
    x ≠ y :=
  fun e => h (congrArg (fun z => D.lab (D.map.alpha z)) e)

/-- **Two mirror triangles with distinct third vertices**: the darts `d` and `alpha d` lie on
inner faces, and the third corners of their triangles carry one label at two vertices. -/
structure DistinctPair (d : D.map.Dart) : Prop where
  not_mem : d ∉ D.cyc
  alpha_not_mem : D.map.alpha d ∉ D.cyc
  lab_third : D.lab (D.map.facePerm (D.map.facePerm d)) =
    D.lab (D.map.facePerm (D.map.facePerm (D.map.alpha d)))
  vertex_ne : D.map.vertexOf (D.map.facePerm (D.map.facePerm d)) ≠
    D.map.vertexOf (D.map.facePerm (D.map.facePerm (D.map.alpha d)))

namespace DistinctPair

variable {D} {d : D.map.Dart} (P : D.DistinctPair d)

include P

theorem f3 : D.map.facePerm (D.map.facePerm (D.map.facePerm d)) = d := by
  have h := (D.tri d P.not_mem).1
  rwa [perm_pow_three_apply] at h

theorem f3_alpha :
    D.map.facePerm (D.map.facePerm (D.map.facePerm (D.map.alpha d))) = D.map.alpha d := by
  have h := (D.tri _ P.alpha_not_mem).1
  rwa [perm_pow_three_apply] at h

theorem tri_lab :
    X.Tri (D.lab d) (D.lab (D.map.alpha d)) (D.lab (D.map.facePerm (D.map.facePerm d))) := by
  have h := (D.tri d P.not_mem).2
  rwa [D.lab_facePerm d, perm_pow_two_apply] at h

theorem ne_ab : D.lab d ≠ D.lab (D.map.alpha d) := (X.tri_adj P.tri_lab).1.ne

theorem ne_bc : D.lab (D.map.alpha d) ≠ D.lab (D.map.facePerm (D.map.facePerm d)) :=
  (X.tri_adj P.tri_lab).2.1.ne

theorem ne_ac : D.lab d ≠ D.lab (D.map.facePerm (D.map.facePerm d)) :=
  (X.tri_adj P.tri_lab).2.2.ne

theorem lab_alpha_d2 : D.lab (D.map.alpha (D.map.facePerm (D.map.facePerm d))) = D.lab d :=
  (D.lab_facePerm _).symm.trans (congrArg D.lab P.f3)

theorem lab_e1 : D.lab (D.map.facePerm (D.map.alpha d)) = D.lab d :=
  (D.lab_facePerm _).trans (congrArg D.lab (D.map.alpha_involutive d))

theorem lab_alpha_e1 :
    D.lab (D.map.alpha (D.map.facePerm (D.map.alpha d))) =
      D.lab (D.map.facePerm (D.map.facePerm d)) :=
  (D.lab_facePerm _).symm.trans P.lab_third.symm

theorem lab_e2 :
    D.lab (D.map.facePerm (D.map.facePerm (D.map.alpha d))) =
      D.lab (D.map.facePerm (D.map.facePerm d)) :=
  P.lab_third.symm

theorem lab_alpha_e2 :
    D.lab (D.map.alpha (D.map.facePerm (D.map.facePerm (D.map.alpha d)))) =
      D.lab (D.map.alpha d) :=
  (D.lab_facePerm _).symm.trans (congrArg D.lab P.f3_alpha)

theorem e1_ne_ad2 :
    D.map.facePerm (D.map.alpha d) ≠ D.map.alpha (D.map.facePerm (D.map.facePerm d)) := by
  intro e
  have h : D.map.alpha (D.map.facePerm (D.map.alpha d)) = D.map.facePerm (D.map.facePerm d) := by
    rw [e, D.map.alpha_involutive _]
  exact P.vertex_ne ((Systolic.vertexOf_facePerm D.map (D.map.facePerm (D.map.alpha d))).trans
    (congrArg D.map.vertexOf h)).symm

theorem d2_ne_ae1 :
    D.map.facePerm (D.map.facePerm d) ≠ D.map.alpha (D.map.facePerm (D.map.alpha d)) := fun e =>
  P.vertex_ne ((congrArg D.map.vertexOf e).trans
    (Systolic.vertexOf_facePerm D.map (D.map.facePerm (D.map.alpha d))).symm)

theorem d1_ne_ae2 :
    D.map.facePerm d ≠ D.map.alpha (D.map.facePerm (D.map.facePerm (D.map.alpha d))) := by
  intro e
  have h : D.map.alpha (D.map.facePerm d) = D.map.facePerm (D.map.facePerm (D.map.alpha d)) := by
    rw [e, D.map.alpha_involutive _]
  exact P.vertex_ne ((Systolic.vertexOf_facePerm D.map (D.map.facePerm d)).trans
    (congrArg D.map.vertexOf h))

theorem ends_ne :
    D.map.vertexOf (D.map.alpha (D.map.facePerm d)) ≠
      D.map.vertexOf (D.map.alpha (D.map.facePerm (D.map.alpha d))) := fun h =>
  P.vertex_ne ((Systolic.vertexOf_facePerm D.map (D.map.facePerm d)).trans
    (h.trans (Systolic.vertexOf_facePerm D.map (D.map.facePerm (D.map.alpha d))).symm))

theorem face_ne : D.map.faceOf d ≠ D.map.faceOf (D.map.alpha d) := fun h =>
  D.toTriangulatedDisc.faceOf_alpha_ne_of_inner (d := d)
    (fun hm => P.not_mem ((D.isFaceCycle.mem_iff d).mpr hm)) h.symm

/-- **The quadrilateral of the pair.** -/
def quad : MirrorQuad D.map where
  d := d
  d1 := D.map.facePerm d
  d2 := D.map.facePerm (D.map.facePerm d)
  e1 := D.map.facePerm (D.map.alpha d)
  e2 := D.map.facePerm (D.map.facePerm (D.map.alpha d))
  f_d := rfl
  f_d1 := rfl
  f_d2 := P.f3
  f_ad := rfl
  f_e1 := rfl
  f_e2 := P.f3_alpha
  d1_ne_d := D.ne_of_lab (by rw [D.lab_facePerm d]; exact P.ne_ab.symm)
  d2_ne_d := D.ne_of_lab P.ne_ac.symm
  e1_ne_d := D.ne_of_lab_alpha (by rw [P.lab_alpha_e1]; exact P.ne_bc.symm)
  e2_ne_d := D.ne_of_lab (by rw [P.lab_e2]; exact P.ne_ac.symm)
  d1_ne_ad := D.ne_of_lab_alpha (by
    rw [← D.lab_facePerm (D.map.facePerm d), D.map.alpha_involutive d]
    exact P.ne_ac.symm)
  d2_ne_ad := D.ne_of_lab P.ne_bc.symm
  e1_ne_ad := D.ne_of_lab (by rw [P.lab_e1]; exact P.ne_ab)
  e2_ne_ad := D.ne_of_lab (by rw [P.lab_e2]; exact P.ne_bc.symm)
  d1_ne_e1 := D.ne_of_lab (by rw [D.lab_facePerm d, P.lab_e1]; exact P.ne_ab.symm)
  d2_ne_e1 := D.ne_of_lab (by rw [P.lab_e1]; exact P.ne_ac.symm)
  e2_ne_e1 := D.ne_of_lab (by rw [P.lab_e2, P.lab_e1]; exact P.ne_ac.symm)
  e2_ne_d1 := D.ne_of_lab (by rw [P.lab_e2, D.lab_facePerm d]; exact P.ne_bc.symm)
  d2_ne_d1 := D.ne_of_lab (by rw [D.lab_facePerm d]; exact P.ne_bc.symm)
  d2_ne_e2 := D.ne_of_lab_alpha (by rw [P.lab_alpha_d2, P.lab_alpha_e2]; exact P.ne_ab)
  e1_ne_ad2 := P.e1_ne_ad2
  d1_ne_ae1 := D.ne_of_lab (by rw [D.lab_facePerm d, P.lab_alpha_e1]; exact P.ne_bc)
  d2_ne_ae1 := P.d2_ne_ae1
  e2_ne_ae1 := D.ne_of_lab_alpha (by
    rw [P.lab_alpha_e2, D.map.alpha_involutive (D.map.facePerm (D.map.alpha d)), P.lab_e1]
    exact P.ne_ab.symm)
  d1_ne_ae2 := P.d1_ne_ae2
  d2_ne_ae2 := D.ne_of_lab (by rw [P.lab_alpha_e2]; exact P.ne_bc.symm)
  ends_ne := P.ends_ne
  face_ne := P.face_ne

/-- The reading carries start labels. -/
theorem lab_tau (x : P.quad.M3.Dart) : D.lab (P.quad.tau x) = D.lab (P.quad.vc x) := by
  rcases P.quad.tau_cases x with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h]
  · rw [h1, h2]
    exact P.lab_alpha_e2.trans (D.lab_facePerm d).symm
  · rw [h1, h2]
    exact P.lab_alpha_e1

/-- The reading carries end labels. -/
theorem lab_alpha_tau (x : P.quad.M3.Dart) :
    D.lab (D.map.alpha (P.quad.tau x)) = D.lab (D.map.alpha (P.quad.vc x)) := by
  rcases P.quad.tau_cases x with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h]
  · rw [h1, h2, D.map.alpha_involutive _]
    exact P.lab_e2.trans (D.lab_facePerm (D.map.facePerm d))
  · rw [h1, h2, D.map.alpha_involutive _]
    exact P.lab_e1.trans P.lab_alpha_d2.symm

theorem lab_embed (x : P.quad.M3.Dart) :
    D.lab (D.map.alpha (P.quad.tau (P.quad.M3.alpha x))) = D.lab (P.quad.tau x) := by
  rw [P.lab_alpha_tau, P.quad.vc_alpha, D.map.alpha_involutive _, P.lab_tau]

/-- The exterior cycle is read. -/
theorem exists_tau_eq {z : D.map.Dart} (hz : z ∈ D.cyc) : ∃ x, P.quad.tau x = z := by
  have hd1 : D.map.facePerm d ∉ D.cyc := D.facePerm_not_mem P.not_mem
  have hd2 : D.map.facePerm (D.map.facePerm d) ∉ D.cyc := D.facePerm_not_mem hd1
  have he1 : D.map.facePerm (D.map.alpha d) ∉ D.cyc := D.facePerm_not_mem P.alpha_not_mem
  have he2 : D.map.facePerm (D.map.facePerm (D.map.alpha d)) ∉ D.cyc := D.facePerm_not_mem he1
  have ne : ∀ {w : D.map.Dart}, w ∉ D.cyc → z ≠ w := fun hw h => hw (h ▸ hz)
  by_cases hae1 : z = D.map.alpha (D.map.facePerm (D.map.alpha d))
  · exact ⟨P.quad.d2''', P.quad.tau_d2'''.trans hae1.symm⟩
  by_cases hae2 : z = D.map.alpha (D.map.facePerm (D.map.facePerm (D.map.alpha d)))
  · exact ⟨P.quad.d1''', P.quad.tau_d1'''.trans hae2.symm⟩
  exact P.quad.exists_tau_eq_of_ne (ne P.not_mem) (ne P.alpha_not_mem) (ne hd1) (ne hd2)
    (ne he1) hae1 (ne he2) hae2

/-- **The pair folds away**: a cycle disc with the same boundary and two faces fewer. -/
theorem exists_fold :
    ∃ E : CycleDisc X, E.boundary = D.boundary ∧ E.map.faceCount + 2 = D.map.faceCount := by
  obtain ⟨E, hE, hcount⟩ := D.exists_of_embed (P.quad.planar3 D.planar) P.quad.tau
    P.quad.tau_injective P.quad.tau_facePerm P.lab_embed (fun _ hz => P.exists_tau_eq hz)
  refine ⟨E, hE, ?_⟩
  rw [hcount]
  exact P.quad.faceCount_add_two D.planar

end DistinctPair

end CycleDisc

/-- **HC6, distinct third vertices.** -/
theorem mirrorFoldDistinct (X : TriangleComplex V) : MirrorFoldDistinctStatement X := by
  intro γ T d hd had hlab hthird
  classical
  let B := FaceBoundary.based T.map T.base
  have hbase : T.base ∈ B.darts := (B.mem_iff T.base).mpr rfl
  obtain ⟨k, rest, _, hrot⟩ := B.isFaceCycle.exists_rotate_cons hbase
  have hcyc : T.map.IsFaceCycle (T.base :: rest) := by
    have h := B.isFaceCycle.rotate k
    rwa [hrot] at h
  have hout : ∀ z, z ∈ T.base :: rest → T.map.faceOf z = T.outer := fun z hz => by
    have h := (hcyc.mem_iff z).mp hz
    rwa [List.head_cons, T.base_outer] at h
  let D : CycleDisc X :=
    { map := T.map
      planar := T.planar
      lab := fun z => T.vtx (T.map.vertexOf z)
      lab_sigma := fun z => by rw [T.map.vertexOf_sigma]
      adj := T.adj
      cyc := T.base :: rest
      isFaceCycle := hcyc
      tri := fun z hz => T.tri z (fun hface => hz ((hcyc.mem_iff z).mpr
        (by rw [List.head_cons, T.base_outer]; exact hface))) }
  have hb : D.boundary = γ := by
    rw [← T.boundary]
    have hdeg : T.map.faceDegree T.outer = (T.base :: rest).length := by
      rw [← T.base_outer]
      exact hcyc.length_eq.symm
    show (T.base :: rest).map (fun z => T.vtx (T.map.vertexOf z)) ++
        [T.vtx (T.map.vertexOf ((T.base :: rest).head hcyc.ne_nil))] = _
    rw [hdeg]
    exact (ofFn_boundary_eq hcyc (fun z => T.vtx (T.map.vertexOf z))).symm
  have h3 : T.vtx (T.map.vertexOf (T.map.facePerm (T.map.facePerm d))) =
      T.vtx (T.map.vertexOf (T.map.facePerm (T.map.facePerm (T.map.alpha d)))) := by
    have h := hlab
    unfold TriangulatedDisc.third at h
    rwa [perm_pow_two_apply, perm_pow_two_apply] at h
  have hv : T.map.vertexOf (T.map.facePerm (T.map.facePerm d)) ≠
      T.map.vertexOf (T.map.facePerm (T.map.facePerm (T.map.alpha d))) := by
    have h := hthird
    unfold TriangulatedDisc.third at h
    rwa [perm_pow_two_apply, perm_pow_two_apply] at h
  have P : D.DistinctPair d :=
    { not_mem := fun hm => hd (hout d hm)
      alpha_not_mem := fun hm => had (hout _ hm)
      lab_third := h3
      vertex_ne := hv }
  obtain ⟨E, hE, hcount⟩ := P.exists_fold
  have key : ∀ γ' (h : E.boundary = γ'),
      ∃ D' : TriangulatedDisc X γ', D'.innerFaceCount + 2 ≤ T.innerFaceCount := by
    intro γ' h
    subst h
    refine ⟨E.toTriangulatedDisc, ?_⟩
    have h1 : 1 ≤ E.toTriangulatedDisc.map.faceCount := E.toTriangulatedDisc.one_le_faceCount
    have h1' : 1 ≤ E.map.faceCount := h1
    have h2 : E.map.faceCount + 2 = T.map.faceCount := hcount
    show E.map.faceCount - 1 + 2 ≤ T.map.faceCount - 1
    omega
  exact key γ (hE.trans hb)

end GroupApproximation.Systolic

#audit_axioms GroupApproximation.Systolic.CycleDisc.DistinctPair.quad
#audit_axioms GroupApproximation.Systolic.CycleDisc.DistinctPair.exists_fold
#audit_axioms GroupApproximation.Systolic.mirrorFoldDistinct
