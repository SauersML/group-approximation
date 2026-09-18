import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2Thom.LEFBound
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2Endpoint.ThomGroup
import GroupApproximation.Sofic.LEF
import GroupApproximation.Meta.AxiomGuard

/-!
# Thom's group is LEF (Thom, Lemma 2.3)

`simple_kazhdan_sofic_group.tex`, Introduction, tex l.57–59 (table row A2): "Thom constructed a
finitely generated Kazhdan group that is locally embeddable into finite groups but not residually
finite". This file proves the "locally embeddable into finite groups" part for
`G = G_0(K[t,t⁻¹]) / C` with `K` a finite nontrivial commutative ring, in particular `K = F_p`.

Thom's proof of Lemma 2.3 (Groups Geom. Dyn. 4 (2010), §2.1): given a finite set of elements of
`G`, pick representatives in `G_0`. Their entries are Laurent polynomials in some window
`[-N, N]`, and the products of pairs agree with representatives of the products up to central
`e_15(q)` with `q ∈ K[t]` of bounded degree. Evaluating at `t ↦ X ∈ K[X]/(X^M - 1)` for large `M`
gives a finite group `G_0(K[ℤ/M])`. Taking the quotient by the images of those bounded central
elements (a finite central subgroup `W`) gives a map that is multiplicative on the set and
injective, because evaluation is injective on the window (`LaurentBound.eq_of_cycEval_eq`).

* `thomMap π : G_0(R) →* G_0(S)` for a ring hom `π`, and `thomMap_thomCentral`.
* `laurentBound_mul_central`: multiplying by `e_15(q)` keeps entries in the window.
* `isTextbookLEF_thomGroup`, `isLEF_thomGroup_of_finite`, and the endpoint `isLEF_thomGroup`.
-/

namespace GroupApproximation.Full.A2Thom

open Polynomial
open GroupApproximation.Full.A2Endpoint

section Map

variable {R S : Type*} [CommRing R] [CommRing S]

theorem ringHom_one_apply (π : R →+* S) (i j : Fin 5) :
    π ((1 : Matrix (Fin 5) (Fin 5) R) i j) = (1 : Matrix (Fin 5) (Fin 5) S) i j := by
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, map_zero]

/-- A ring hom `π : R → S` induces `G_0(R) →* G_0(S)` entrywise. -/
noncomputable def thomMap (π : R →+* S) : thomG0 R →* thomG0 S where
  toFun g := ⟨Matrix.SpecialLinearGroup.map π g.1, (mem_thomG0 S).2
    ⟨fun i => by
      show π (g.1.1 i 0) = (1 : Matrix (Fin 5) (Fin 5) S) i 0
      rw [((mem_thomG0 R).1 g.2).col i]
      exact ringHom_one_apply π i 0,
    fun j => by
      show π (g.1.1 4 j) = (1 : Matrix (Fin 5) (Fin 5) S) 4 j
      rw [((mem_thomG0 R).1 g.2).row j]
      exact ringHom_one_apply π 4 j⟩⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (Matrix.SpecialLinearGroup.map π)
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul (Matrix.SpecialLinearGroup.map π) a.1 b.1

theorem thomMap_apply (π : R →+* S) (g : thomG0 R) (i j : Fin 5) :
    (thomMap π g).1.1 i j = π (g.1.1 i j) :=
  rfl

theorem thomMap_thomCentral (π : R →+* S) (c : R) :
    thomMap π (thomCentral R (Multiplicative.ofAdd c)) =
      thomCentral S (Multiplicative.ofAdd (π c)) := by
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  show π (Matrix.transvection (0 : Fin 5) 4 c i j) = Matrix.transvection (0 : Fin 5) 4 (π c) i j
  by_cases h : (0 : Fin 5) = i ∧ (4 : Fin 5) = j
  · obtain ⟨rfl, rfl⟩ := h
    rw [transvection_apply_self fin_zero_ne_four, transvection_apply_self fin_zero_ne_four]
  · rw [Matrix.transvection, Matrix.transvection, Matrix.add_apply, Matrix.add_apply,
      Matrix.single_apply_of_ne (0 : Fin 5) (4 : Fin 5) c i j h,
      Matrix.single_apply_of_ne (0 : Fin 5) (4 : Fin 5) (π c) i j h, add_zero, add_zero]
    exact ringHom_one_apply π i j

theorem finite_thomG0 [Finite S] : Finite (thomG0 S) :=
  Finite.of_injective (fun g : thomG0 S => g.1.1) (fun _ _ h => Subtype.ext (Subtype.ext h))

end Map

/-- The polynomials of degree at most `D`. -/
def degLE (K : Type*) [CommRing K] (D : ℕ) : AddSubgroup K[X] where
  carrier := {q | q.natDegree ≤ D}
  add_mem' := by
    intro a b ha hb
    have ha' : a.natDegree ≤ D := ha
    have hb' : b.natDegree ≤ D := hb
    show (a + b).natDegree ≤ D
    exact (Polynomial.natDegree_add_le a b).trans (max_le ha' hb')
  zero_mem' := by
    show (0 : K[X]).natDegree ≤ D
    rw [Polynomial.natDegree_zero]
    exact Nat.zero_le _
  neg_mem' := by
    intro a ha
    have ha' : a.natDegree ≤ D := ha
    show (-a).natDegree ≤ D
    rw [Polynomial.natDegree_neg]
    exact ha'

theorem mem_degLE (K : Type*) [CommRing K] (D : ℕ) {q : K[X]} :
    q ∈ degLE K D ↔ q.natDegree ≤ D :=
  Iff.rfl

section Window

variable {K : Type*} [CommRing K]

/-- Multiplying a representative by `e_15(q)`, `deg q ≤ N`, keeps its entries in `[-N, N]`. -/
theorem laurentBound_mul_central {N : ℕ} (g : thomG0 (LaurentPolynomial K))
    (hg : ∀ i j, LaurentBound N (g.1.1 i j)) (r : K[X]) (hr : r.natDegree ≤ N) (i j : Fin 5) :
    LaurentBound N ((g * thomCentral (LaurentPolynomial K)
      (Multiplicative.ofAdd (Polynomial.toLaurent r))).1.1 i j) := by
  have hval : (g * thomCentral (LaurentPolynomial K)
      (Multiplicative.ofAdd (Polynomial.toLaurent r))).1.1 =
        g.1.1 * Matrix.transvection (0 : Fin 5) 4 (Polynomial.toLaurent r) :=
    rfl
  rw [hval]
  by_cases hj : j = 4
  · subst hj
    rw [Matrix.mul_transvection_apply_same, ((mem_thomG0 _).1 g.2).col i]
    by_cases hi : i = 0
    · subst hi
      rw [Matrix.one_apply_eq, mul_one]
      exact (hg 0 4).add (laurentBound_toLaurent r hr)
    · rw [Matrix.one_apply_ne hi, mul_zero, add_zero]
      exact hg i 4
  · rw [Matrix.mul_transvection_apply_of_ne (0 : Fin 5) 4 i j hj]
    exact hg i j

variable (K) in
/-- The central subgroup `{e_15(q(X)) : deg q ≤ D}` of `G_0(K[X]/(X^{m+1} - 1))`. -/
theorem exists_central_window (m D : ℕ) :
    ∃ W : Subgroup (thomG0 (CycRing K m)),
      (∀ r : K[X], r.natDegree ≤ D →
        thomCentral (CycRing K m) (Multiplicative.ofAdd (cycEval K m (Polynomial.toLaurent r))) ∈
          W) ∧
      (∀ w ∈ W, ∃ r : K[X], r.natDegree ≤ D ∧
        w = thomCentral (CycRing K m)
          (Multiplicative.ofAdd (cycEval K m (Polynomial.toLaurent r)))) := by
  refine ⟨((thomCentral (CycRing K m)).comp (AddMonoidHom.toMultiplicative
      ((cycEval K m).toAddMonoidHom.comp
        ((Polynomial.toLaurent (R := K)).toAddMonoidHom.comp (degLE K D).subtype)))).range,
    fun r hr => MonoidHom.mem_range.2
      ⟨Multiplicative.ofAdd (⟨r, (mem_degLE K D).2 hr⟩ : degLE K D), rfl⟩, fun w hw => ?_⟩
  obtain ⟨r, rfl⟩ := MonoidHom.mem_range.1 hw
  exact ⟨(Multiplicative.toAdd r).1, (mem_degLE K D).1 (Multiplicative.toAdd r).2, rfl⟩

end Window

/-- **Thom, Lemma 2.3** (textbook form): `G_0(K[t,t⁻¹]) / C` is locally embeddable into finite
groups for every finite nontrivial commutative ring `K` (tex l.57–59). -/
theorem isTextbookLEF_thomGroup (K : Type) [CommRing K] [Nontrivial K] [Finite K] :
    IsTextbookLEF (ThomGroup K) := by
  intro s
  obtain ⟨out, hout⟩ : ∃ out : ThomGroup K → thomG0 (LaurentPolynomial K),
      ∀ x, QuotientGroup.mk' (thomC K) (out x) = x :=
    ⟨Function.surjInv (QuotientGroup.mk'_surjective (thomC K)),
      Function.surjInv_eq (QuotientGroup.mk'_surjective (thomC K))⟩
  have hbd : ∀ x : ThomGroup K, ∃ N : ℕ, ∀ i j, LaurentBound N ((out x).1.1 i j) := by
    intro x
    choose n hn using fun ij : Fin 5 × Fin 5 => exists_laurentBound ((out x).1.1 ij.1 ij.2)
    exact ⟨Finset.univ.sup n, fun i j =>
      (hn (i, j)).mono (Finset.le_sup (f := n) (Finset.mem_univ (i, j)))⟩
  choose Nx hNx using hbd
  have hprod : ∀ x y : ThomGroup K, ∃ q : K[X], out x * out y =
      out (x * y) * thomCentral (LaurentPolynomial K)
        (Multiplicative.ofAdd (Polynomial.toLaurent q)) := by
    intro x y
    have hxy : QuotientGroup.mk' (thomC K) (out (x * y)) =
        QuotientGroup.mk' (thomC K) (out x * out y) := by
      rw [map_mul, hout, hout, hout]
    obtain ⟨z, hz, hz'⟩ := (QuotientGroup.mk'_eq_mk' (thomC K)).1 hxy
    obtain ⟨q, rfl⟩ := MonoidHom.mem_range.1 hz
    exact ⟨Multiplicative.toAdd q, hz'.symm⟩
  choose qx hqx using hprod
  obtain ⟨D, hD⟩ : ∃ D : ℕ, ∀ x ∈ s, ∀ y ∈ s, (qx x y).natDegree ≤ D :=
    ⟨s.sup fun x => s.sup fun y => (qx x y).natDegree, fun x hx y hy =>
      (Finset.le_sup (f := fun y => (qx x y).natDegree) hy).trans
        (Finset.le_sup (f := fun x => s.sup fun y => (qx x y).natDegree) hx)⟩
  obtain ⟨E, hE⟩ : ∃ E : ℕ, ∀ x ∈ s, Nx x ≤ E :=
    ⟨s.sup Nx, fun x hx => Finset.le_sup (f := Nx) hx⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = 2 * (D + E) := ⟨_, rfl⟩
  obtain ⟨W, hWmem, hWcases⟩ := exists_central_window K m D
  have hWle : W ≤ (thomCentral (CycRing K m)).range := by
    intro w hw
    obtain ⟨r, _, rfl⟩ := hWcases w hw
    exact MonoidHom.mem_range.2 ⟨_, rfl⟩
  haveI : W.Normal := normal_of_le_range (CycRing K m) hWle
  haveI : Finite (thomG0 (CycRing K m)) := finite_thomG0
  haveI : Finite (thomG0 (CycRing K m) ⧸ W) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective W)
  have hmul : ∀ x ∈ s, ∀ y ∈ s, QuotientGroup.mk' W (thomMap (cycEval K m) (out (x * y))) =
      QuotientGroup.mk' W (thomMap (cycEval K m) (out x)) *
        QuotientGroup.mk' W (thomMap (cycEval K m) (out y)) := by
    intro x hx y hy
    have hc : QuotientGroup.mk' W (thomMap (cycEval K m) (thomCentral (LaurentPolynomial K)
        (Multiplicative.ofAdd (Polynomial.toLaurent (qx x y))))) = 1 := by
      rw [thomMap_thomCentral, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hWmem _ (hD x hx y hy)
    rw [← map_mul, ← map_mul, hqx x y, map_mul, map_mul, hc, mul_one]
  have hinj : ∀ x ∈ s, ∀ y ∈ s, QuotientGroup.mk' W (thomMap (cycEval K m) (out x)) =
      QuotientGroup.mk' W (thomMap (cycEval K m) (out y)) → x = y := by
    intro x hx y hy hxy
    obtain ⟨z, hz, hz'⟩ := (QuotientGroup.mk'_eq_mk' W).1 hxy
    obtain ⟨r, hr, rfl⟩ := hWcases z hz
    rw [← thomMap_thomCentral (cycEval K m) (Polynomial.toLaurent r), ← map_mul] at hz'
    have hEx := hE x hx
    have hEy := hE y hy
    have hbx : ∀ i j, LaurentBound (D + E) ((out x * thomCentral (LaurentPolynomial K)
        (Multiplicative.ofAdd (Polynomial.toLaurent r))).1.1 i j) :=
      laurentBound_mul_central (out x) (fun i j => (hNx x i j).mono (by omega)) r (by omega)
    have heq : out x * thomCentral (LaurentPolynomial K)
        (Multiplicative.ofAdd (Polynomial.toLaurent r)) = out y := by
      apply Subtype.ext
      apply Subtype.ext
      refine Matrix.ext fun i j ↦ ?_
      have hij : cycEval K m ((out x * thomCentral (LaurentPolynomial K)
          (Multiplicative.ofAdd (Polynomial.toLaurent r))).1.1 i j) =
            cycEval K m ((out y).1.1 i j) :=
        congrArg (fun g : thomG0 (CycRing K m) => g.1.1 i j) hz'
      exact (hbx i j).eq_of_cycEval_eq ((hNx y i j).mono (by omega)) (by omega) hij
    calc x = QuotientGroup.mk' (thomC K) (out x) := (hout x).symm
      _ = QuotientGroup.mk' (thomC K) (out x * thomCentral (LaurentPolynomial K)
          (Multiplicative.ofAdd (Polynomial.toLaurent r))) :=
        (QuotientGroup.mk'_eq_mk' (thomC K)).2
          ⟨thomCentral (LaurentPolynomial K) (Multiplicative.ofAdd (Polynomial.toLaurent r)),
            MonoidHom.mem_range.2 ⟨Multiplicative.ofAdd r, rfl⟩, rfl⟩
      _ = QuotientGroup.mk' (thomC K) (out y) := by rw [heq]
      _ = y := hout y
  refine ⟨⟨thomG0 (CycRing K m) ⧸ W, inferInstance, Fintype.ofFinite _, Classical.decEq _⟩,
    fun x => QuotientGroup.mk' W (thomMap (cycEval K m) (out x)), ?_,
    fun x hx y hy _ => hmul x hx y hy⟩
  intro x hx y hy hxy
  exact hinj x (Finset.mem_coe.1 hx) y (Finset.mem_coe.1 hy) hxy

/-- **Thom, Lemma 2.3**: `G_0(K[t,t⁻¹]) / C` is LEF for every finite nontrivial commutative ring
`K` (tex l.57–59). -/
theorem isLEF_thomGroup_of_finite (K : Type) [CommRing K] [Nontrivial K] [Finite K] :
    IsLEF (ThomGroup K) :=
  (isLEF_iff_textbook _).2 (isTextbookLEF_thomGroup K)

/-- **tex l.57–59** ("locally embeddable into finite groups"): Thom's group
`G_0(F_p[t,t⁻¹]) / C` is LEF (Thom, GGD 4 (2010), Lemma 2.3). -/
theorem isLEF_thomGroup (p : ℕ) [Fact p.Prime] : IsLEF (ThomGroup (ZMod p)) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact isLEF_thomGroup_of_finite (ZMod p)

#audit_axioms GroupApproximation.Full.A2Thom.isLEF_thomGroup

end GroupApproximation.Full.A2Thom
