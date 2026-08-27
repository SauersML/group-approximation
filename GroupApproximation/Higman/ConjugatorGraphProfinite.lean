import GroupApproximation.Higman.PairedReturnGraphIntersection
import GroupApproximation.Higman.CoordCalculus
import GroupApproximation.Sofic.ProfiniteRetract

/-!
# Profinite closedness of Higman's conjugator graph

The first coordinate of the graph lies in the kernel of the retraction
`retK`, hence has a unique word in the conjugate basis `a^h`.  A finite
quotient of `F₃` can read the value of that word by a finite two-coordinate
action: the `K` letters move the state in the finite quotient, while `a`
writes the current state.  Thus every mismatch in the graph is detected by a
finite quotient.
-/

namespace GroupApproximation
namespace Higman
namespace ConjugatorGraphProfinite

open Conj

variable {Q : Type} [Group Q]

/-- On a finite quotient state, `a` writes the current state into the first
coordinate. -/
def writeCurrent : Equiv.Perm (Q × Q) where
  toFun p := (p.2 * p.1, p.2)
  invFun p := (p.2⁻¹ * p.1, p.2)
  left_inv p := by rcases p with ⟨u, s⟩; apply Prod.ext <;> simp
  right_inv p := by rcases p with ⟨u, s⟩; apply Prod.ext <;> simp

/-- A conjugating letter translates the finite quotient state. -/
def shiftState (k : Q) : Equiv.Perm (Q × Q) where
  toFun p := (p.1, k * p.2)
  invFun p := (p.1, k⁻¹ * p.2)
  left_inv p := by rcases p with ⟨u, s⟩; apply Prod.ext <;> simp
  right_inv p := by rcases p with ⟨u, s⟩; apply Prod.ext <;> simp

/-- The finite state action associated to a quotient of `F₃`. -/
def finiteReadAct (q : F₃ →* Q) : F₃ →* Equiv.Perm (Q × Q) :=
  FreeGroup.lift fun i : Fin 3 ↦
    if i = 0 then writeCurrent
    else if i = 1 then shiftState (q b)
    else shiftState (q c)

@[simp] theorem finiteReadAct_a (q : F₃ →* Q) :
    finiteReadAct q a = writeCurrent := by simp [finiteReadAct, a]

@[simp] theorem finiteReadAct_b (q : F₃ →* Q) :
    finiteReadAct q b = shiftState (q b) := by simp [finiteReadAct, b]

@[simp] theorem finiteReadAct_c (q : F₃ →* Q) :
    finiteReadAct q c = shiftState (q c) := by simp [finiteReadAct, c]

/-- Elements of `K` translate the state by their quotient image. -/
theorem finiteReadAct_of_mem_K (q : F₃ →* Q) {x : F₃} (hx : x ∈ K)
    (p : Q × Q) : finiteReadAct q x p = (p.1, q x * p.2) := by
  induction hx using Subgroup.closure_induction generalizing p with
  | mem y hy =>
      rcases hy with rfl | hy
      · rw [finiteReadAct_b]
        rfl
      · rw [Set.mem_singleton_iff] at hy
        subst y
        rw [finiteReadAct_c]
        rfl
  | one =>
      rw [map_one, map_one]
      apply Prod.ext <;> simp
  | mul x y _ _ hx hy =>
      rw [map_mul, map_mul]
      change finiteReadAct q x (finiteReadAct q y p) = _
      rw [hy, hx]
      apply Prod.ext
      · rfl
      · group
  | inv x _ hx =>
      rw [map_inv, map_inv]
      apply (finiteReadAct q x).symm_apply_eq.mpr
      change p = finiteReadAct q x (p.1, (q x)⁻¹ * p.2)
      rw [hx]
      apply Prod.ext
      · rfl
      · group

/-- A conjugate `a^h` writes precisely the image of `h`. -/
theorem finiteReadAct_conj (q : F₃ →* Q) (h : ↥K) (u : Q) :
    finiteReadAct q ((h : F₃)⁻¹ * a * (h : F₃)) (u, 1) =
      (q (h : F₃) * u, 1) := by
  rw [map_mul, map_mul]
  change finiteReadAct q (h : F₃)⁻¹
    (finiteReadAct q a (finiteReadAct q (h : F₃) (u, 1))) = _
  rw [finiteReadAct_of_mem_K q h.property, finiteReadAct_a]
  rw [show q (h : F₃) * 1 = q (h : F₃) by simp]
  rw [show writeCurrent (u, q (h : F₃)) =
    (q (h : F₃) * u, q (h : F₃)) from rfl]
  rw [finiteReadAct_of_mem_K q (K.inv_mem h.property), map_inv]
  apply Prod.ext
  · rfl
  · group

/-- Words for which the finite action reads the evaluation homomorphism. -/
def Readable (q : F₃ →* Q) : Subgroup (FreeGroup ↥K) where
  carrier := {w | ∀ u : Q,
    finiteReadAct q (cbHom w) (u, 1) = (q (Star.evalHom w) * u, 1)}
  one_mem' := by intro u; simp
  mul_mem' := by
    intro x y hx hy u
    rw [map_mul, map_mul, map_mul]
    change finiteReadAct q (cbHom x)
      (finiteReadAct q (cbHom y) (u, 1)) = _
    rw [hy, hx]
    apply Prod.ext
    · simp only [map_mul]
      group
    · rfl
  inv_mem' := by
    intro x hx u
    have hkey := hx ((q (Star.evalHom x))⁻¹ * u)
    have hkey' : finiteReadAct q (cbHom x)
        ((q (Star.evalHom x))⁻¹ * u, 1) = (u, 1) := by
      simpa using hkey
    have hinv : (finiteReadAct q (cbHom x))⁻¹ (u, 1) =
        ((q (Star.evalHom x))⁻¹ * u, 1) :=
      (finiteReadAct q (cbHom x)).symm_apply_eq.mpr hkey'.symm
    simpa only [map_inv] using hinv

theorem readable_eq_top (q : F₃ →* Q) : Readable q = ⊤ := by
  apply top_unique
  have hall : ∀ w : FreeGroup ↥K, w ∈ Readable q := by
    intro w
    induction w using FreeGroup.induction_on with
    | C1 => exact (Readable q).one_mem
    | of h =>
        intro u
        rw [cbHom_of, Star.evalHom_of]
        exact finiteReadAct_conj q h u
    | inv_of h hh => exact (Readable q).inv_mem hh
    | mul x y hx hy => exact (Readable q).mul_mem hx hy
  intro w _
  exact hall w

/-- The finite action reads every conjugate-basis word. -/
theorem finiteReadAct_cbHom (q : F₃ →* Q) (w : FreeGroup ↥K) (u : Q) :
    finiteReadAct q (cbHom w) (u, 1) =
      (q (Star.evalHom w) * u, 1) := by
  have hw : w ∈ Readable q := by rw [readable_eq_top]; trivial
  exact hw u

section Finite

variable [Finite Q]

/-- The finite test quotient simultaneously observes the first-coordinate
action and the ordinary second-coordinate quotient. -/
def graphTest (q : F₃ →* Q) :
    F₃ × F₃ →* Equiv.Perm (Q × Q) × Q :=
  ((finiteReadAct q).comp (MonoidHom.fst F₃ F₃)).prod
    (q.comp (MonoidHom.snd F₃ F₃))

/-- A point in the profinite closure of the graph has matching evaluation in
every finite quotient, once its first coordinate is written in the conjugate
basis. -/
theorem finite_quotient_matches {x y : F₃} (q : F₃ →* Q)
    (hz : (x, y) ∈ profiniteClosure Star.graphSub)
    (w : FreeGroup ↥K) (hw : cbHom w = x) :
    q (Star.evalHom w) = q y := by
  have hmem := hz (Equiv.Perm (Q × Q) × Q) (graphTest q)
  obtain ⟨g, hg, hgz⟩ := Subgroup.mem_map.mp hmem
  obtain ⟨v, hv⟩ := Star.mem_graphSub.mp hg
  have hsecond := congrArg Prod.snd hgz
  have hfirst := congrArg
    (fun p : Equiv.Perm (Q × Q) × Q ↦ p.1 ((1 : Q), (1 : Q))) hgz
  change q g.2 = q y at hsecond
  change finiteReadAct q g.1 (1, 1) = finiteReadAct q x (1, 1) at hfirst
  rw [← hv, Star.graphHom_apply, finiteReadAct_cbHom,
    ← hw, finiteReadAct_cbHom] at hfirst
  have hvalues : q (Star.evalHom v) = q (Star.evalHom w) := by
    simpa only [mul_one] using congrArg Prod.fst hfirst
  rw [← hv, Star.graphHom_apply] at hsecond
  exact hvalues.symm.trans hsecond

end Finite

/-- An element of a residually finite group which dies in every finite
quotient is trivial. -/
theorem eq_one_of_all_finite_images_one (x : F₃)
    (h : ∀ (Q : Type) [Group Q] [Finite Q] (q : F₃ →* Q), q x = 1) :
    x = 1 := by
  by_contra hx
  obtain ⟨N, hN⟩ := Group.exists_finiteIndexNormalSubgroup_notMem x hx
  letI := N.isNormal'
  letI := N.isFiniteIndex'
  let Q := F₃ ⧸ N.toSubgroup
  letI : Finite Q := Subgroup.finite_quotient_of_finiteIndex
  let q : F₃ →* Q := QuotientGroup.mk' N.toSubgroup
  apply hN
  exact (QuotientGroup.eq_one_iff x).mp (h Q q)

/-- The first coordinate of a closure point lies in the conjugate-basis
range. -/
theorem first_mem_cbHom_range {x y : F₃}
    (hz : (x, y) ∈ profiniteClosure Star.graphSub) : x ∈ cbHom.range := by
  have hret : Coord.retK x = 1 := by
    apply eq_one_of_all_finite_images_one
    intro Q _ _ q
    let test : F₃ × F₃ →* Q :=
      q.comp (Coord.retK.comp (MonoidHom.fst F₃ F₃))
    have hmem := hz Q test
    obtain ⟨g, hg, hgz⟩ := Subgroup.mem_map.mp hmem
    have hgker := PairedReturnGraphIntersection.graphSub_le_retK_fst_ker hg
    have hgret : Coord.retK g.1 = 1 := by
      change (Coord.retK.comp (MonoidHom.fst F₃ F₃)) g = 1
      exact MonoidHom.mem_ker.mp hgker
    calc
      q (Coord.retK x) = test (x, y) := rfl
      _ = test g := hgz.symm
      _ = q (Coord.retK g.1) := rfl
      _ = 1 := by rw [hgret, map_one]
  have hxker : x ∈ MonoidHom.ker Coord.retK := MonoidHom.mem_ker.mpr hret
  rwa [Coord.ker_retK_eq_cbHom_range] at hxker

/-- **Higman's infinite conjugator graph is profinitely closed in
`F₃ × F₃`.** -/
theorem profiniteClosure_graphSub :
    profiniteClosure Star.graphSub = Star.graphSub := by
  apply le_antisymm
  · rintro ⟨x, y⟩ hz
    obtain ⟨w, hw⟩ := first_mem_cbHom_range hz
    have heval : Star.evalHom w = y := by
      have hdiff : (Star.evalHom w)⁻¹ * y = 1 := by
        apply eq_one_of_all_finite_images_one
        intro Q _ _ q
        have hmatch := finite_quotient_matches q hz w hw
        rw [map_mul, map_inv, hmatch, inv_mul_cancel]
      exact inv_mul_eq_one.mp hdiff
    exact Star.mem_graphSub.mpr ⟨w, by
      apply Prod.ext
      · exact hw
      · exact heval⟩
  · exact le_profiniteClosure Star.graphSub

end ConjugatorGraphProfinite
end Higman
end GroupApproximation
