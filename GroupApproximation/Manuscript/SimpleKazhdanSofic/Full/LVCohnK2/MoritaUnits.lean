import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnK2.MoritaSteinberg
import Mathlib.Data.Matrix.Basis

/-!
# Diagonal block generators in `St_I(M_J(R))` (lane LVCohnK2)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii.  For the Morita
invariance of stable `K₂` (Ara–Brustenga–Cortiñas 2009, ultramatricial stages of the Cohn algebra)
the generator `x_{(i,k),(i,l)}(a)` of `St_{I×J}(R)` (with `k ≠ l`) is sent to
`diagElem i p k l a = ⁅x_{ip}(e_{kl} a), x_{pi}(e_{ll})⁆` in `St_I(M_J(R))`.  This file proves:

* `diagElem_indep`, `diagElem_add`: independence of `p` and additivity in `a`;
* `commute_diagElem_x`, `commute_x_diagElem`, `commute_diagElem_x_away`: commutation with root
  elements;
* `commute_diagElem_diagElem_same`, `commute_diagElem_diagElem_ne`, `commute_x_x_swap`: the
  commutation cases of the Steinberg relations of `St_{I×J}(R)` not covered by `x_commute_of_ne`;
* `commutator_x_x_eq_diagElem`, `commutator_x_diagElem`, `commutator_diagElem_x`,
  `commutator_diagElem_diagElem`: the adjacent cases involving equal first coordinates.
-/

namespace GroupApproximation.Full.LVCohnK2

open SteinbergGroup
open scoped commutatorElement

variable {I : Type*} [Fintype I] [DecidableEq I] {J : Type*} [Fintype J] [DecidableEq J]
  {R : Type*} [Ring R]

/-- `e_{tt} e_{kl}(a) = 0` for `t ≠ k`.  (`simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem single_one_mul_single (t k l : J) (htk : t ≠ k) (a : R) :
    Matrix.single t t (1 : R) * Matrix.single k l a = 0 :=
  Matrix.single_mul_single_of_ne (c := (1 : R)) t t k htk a

/-- The image of the block generator `x_{(i,k),(i,l)}(a)`:
`⁅x_{ip}(e_{kl} a), x_{pi}(e_{ll})⁆`.  (`simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
def diagElem (i p : I) (hip : i ≠ p) (k l : J) (a : R) : SteinbergGroup I (Matrix J J R) :=
  ⁅x i p hip (Matrix.single k l a), x p i hip.symm (Matrix.single l l (1 : R))⁆

/-- `diagElem` does not depend on the auxiliary index.  (`simple_kazhdan_sofic_group.tex`
l.733-735, leaf T1b.iii.) -/
theorem diagElem_indep (i p q : I) (hip : i ≠ p) (hiq : i ≠ q) (k l : J) (hlk : l ≠ k)
    (a : R) : diagElem i p hip k l a = diagElem i q hiq k l a :=
  diag_eq_of_ne i p q hip hiq.symm (Matrix.single k l a) (Matrix.single l l (1 : R))
    (single_one_mul_single l k l hlk a)

/-- `diagElem` is additive in the coefficient.  (`simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem diagElem_add (i p q : I) (hip : i ≠ p) (hqi : q ≠ i) (hqp : q ≠ p) (k l : J)
    (hlk : l ≠ k) (a b : R) :
    diagElem i p hip k l (a + b) = diagElem i p hip k l a * diagElem i p hip k l b := by
  unfold diagElem
  rw [Matrix.single_add k l a b]
  exact diag_add i p q hip hqi hqp (Matrix.single k l a) (Matrix.single k l b)
    (Matrix.single l l (1 : R)) (single_one_mul_single l k l hlk a)
    (single_one_mul_single l k l hlk b)

/-- `diagElem i p k l a` commutes with `x_{ij}(e_{k'l'} b)` when `l ≠ k'`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem commute_diagElem_x (i p j q : I) (hip : i ≠ p) (hij : i ≠ j) (hiq : i ≠ q)
    (hqj : q ≠ j) (k l : J) (hlk : l ≠ k) (a : R) (k' l' : J) (hlk' : l ≠ k') (b : R) :
    Commute (diagElem i p hip k l a) (x i j hij (Matrix.single k' l' b)) := by
  rw [diagElem_indep i p q hip hiq k l hlk a]
  refine (commute_iff_eq _ _).mpr (commutatorElement_eq_one_iff_mul_comm.mp ?_)
  unfold diagElem
  rw [commutator_diag_x i q j hiq hij hqj (Matrix.single k l a) (Matrix.single l l (1 : R))
      (Matrix.single k' l' b) (single_one_mul_single l k l hlk a),
    Matrix.single_mul_single_of_ne (c := (1 : R)) l l k' hlk' b, mul_zero, x_zero]

/-- `x_{si}(e_{k'l'} b)` commutes with `diagElem i p k l a` when `l' ≠ k`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem commute_x_diagElem (s i p q : I) (hsi : s ≠ i) (hip : i ≠ p) (hiq : i ≠ q)
    (hsq : s ≠ q) (k l : J) (hlk : l ≠ k) (a : R) (k' l' : J) (hl'k : l' ≠ k) (b : R) :
    Commute (x s i hsi (Matrix.single k' l' b)) (diagElem i p hip k l a) := by
  rw [diagElem_indep i p q hip hiq k l hlk a]
  refine (commute_iff_eq _ _).mpr (commutatorElement_eq_one_iff_mul_comm.mp ?_)
  unfold diagElem
  rw [commutator_x_diag s i q hsi hiq hsq (Matrix.single k' l' b) (Matrix.single k l a)
      (Matrix.single l l (1 : R)) (single_one_mul_single l k l hlk a),
    Matrix.single_mul_single_of_ne (c := b) k' l' k hl'k a, zero_mul, x_zero]

/-- `diagElem i p k l a` commutes with `x_{st}(N)` when `s ≠ i`, `t ≠ i`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem commute_diagElem_x_away (i p q s t : I) (hip : i ≠ p) (hiq : i ≠ q) (hst : s ≠ t)
    (hqs : q ≠ s) (hti : t ≠ i) (his : i ≠ s) (htq : t ≠ q) (k l : J) (hlk : l ≠ k) (a : R)
    (N : Matrix J J R) : Commute (diagElem i p hip k l a) (x s t hst N) := by
  rw [diagElem_indep i p q hip hiq k l hlk a]
  exact diag_commute_x i q s t hiq hst hqs hti his htq (Matrix.single k l a)
    (Matrix.single l l (1 : R)) N

/-- Two block generators with the same first coordinate commute when `l ≠ k'` and `l' ≠ k`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem commute_diagElem_diagElem_same (i p p' q : I) (hip : i ≠ p) (hip' : i ≠ p')
    (hiq : i ≠ q) (hqp' : q ≠ p') (k l : J) (hlk : l ≠ k) (a : R) (k' l' : J) (b : R)
    (hlk' : l ≠ k') (hl'k : l' ≠ k) :
    Commute (diagElem i p hip k l a) (diagElem i p' hip' k' l' b) := by
  rw [diagElem_indep i p q hip hiq k l hlk a]
  have h1 : Commute (diagElem i q hiq k l a) (x i p' hip' (Matrix.single k' l' b)) :=
    commute_diagElem_x i q p' q hiq hip' hiq hqp' k l hlk a k' l' hlk' b
  have h2 : Commute (diagElem i q hiq k l a) (x p' i hip'.symm (Matrix.single l' l' (1 : R))) :=
    (commute_x_diagElem p' i q q hip'.symm hiq hiq hqp'.symm k l hlk a l' l' hl'k 1).symm
  have h3 := commute_commutatorElement h1 h2
  have e : diagElem i p' hip' k' l' b =
      ⁅x i p' hip' (Matrix.single k' l' b), x p' i hip'.symm (Matrix.single l' l' (1 : R))⁆ :=
    rfl
  rw [e]
  exact h3

/-- Two block generators with different first coordinates commute.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem commute_diagElem_diagElem_ne (i p i' p' q r : I) (hip : i ≠ p) (hip' : i' ≠ p')
    (hii' : i ≠ i') (hi'q : i' ≠ q) (hiq : i ≠ q) (hir : i ≠ r) (hri' : r ≠ i') (hrq : r ≠ q)
    (k l : J) (hlk : l ≠ k) (a : R) (k' l' : J) (hl'k' : l' ≠ k') (b : R) :
    Commute (diagElem i p hip k l a) (diagElem i' p' hip' k' l' b) := by
  rw [diagElem_indep i' p' q hip' hi'q k' l' hl'k' b]
  have h1 : Commute (diagElem i p hip k l a) (x i' q hi'q (Matrix.single k' l' b)) :=
    commute_diagElem_x_away i p r i' q hip hir hi'q hri' hiq.symm hii' hrq.symm k l hlk a _
  have h2 : Commute (diagElem i p hip k l a)
      (x q i' hi'q.symm (Matrix.single l' l' (1 : R))) :=
    commute_diagElem_x_away i p r q i' hip hir hi'q.symm hrq hii'.symm hiq hri'.symm k l hlk a _
  have h3 := commute_commutatorElement h1 h2
  have e : diagElem i' q hi'q k' l' b =
      ⁅x i' q hi'q (Matrix.single k' l' b), x q i' hi'q.symm (Matrix.single l' l' (1 : R))⁆ :=
    rfl
  rw [e]
  exact h3

/-- `x_{ij}(e_{kl} a)` and `x_{ji}(e_{k'l'} b)` commute when `l ≠ k'` and `l' ≠ k`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem commute_x_x_swap (i j p : I) (hij : i ≠ j) (hjp : j ≠ p) (hpi : p ≠ i) (k l k' l' : J)
    (hlk' : l ≠ k') (hl'k : l' ≠ k) (a b : R) :
    Commute (x i j hij (Matrix.single k l a)) (x j i hij.symm (Matrix.single k' l' b)) := by
  have h := commutator_switch i j p hij hjp hpi (Matrix.single k l a) (Matrix.single k' l' b)
    (Matrix.single l' l' (1 : R)) (single_one_mul_single l' k l hl'k a)
  rw [Matrix.single_mul_single_same (c := b) k' l' l' (1 : R), mul_one,
    Matrix.single_mul_single_of_ne (c := a) k l k' hlk' b, x_zero, commutatorElement_one_left] at h
  exact (commute_iff_eq _ _).mpr (commutatorElement_eq_one_iff_mul_comm.mp h)

/-- `⁅x_{ij}(e_{kl} a), x_{ji}(e_{lt} b)⁆ = diagElem i p k t (a b)` for `t ≠ k`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem commutator_x_x_eq_diagElem (i j p : I) (hij : i ≠ j) (hjp : j ≠ p) (hpi : p ≠ i)
    (k l t : J) (htk : t ≠ k) (a b : R) :
    ⁅x i j hij (Matrix.single k l a), x j i hij.symm (Matrix.single l t b)⁆ =
      diagElem i p hpi.symm k t (a * b) := by
  have h := commutator_switch i j p hij hjp hpi (Matrix.single k l a) (Matrix.single l t b)
    (Matrix.single t t (1 : R)) (single_one_mul_single t k l htk a)
  rw [Matrix.single_mul_single_same (c := b) l t t (1 : R), mul_one,
    Matrix.single_mul_single_same (c := a) k l t b] at h
  exact h

/-- `⁅x_{si}(e_{kl} a), diagElem i p l t b⁆ = x_{si}(e_{kt}(a b))` for `t ≠ l`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem commutator_x_diagElem (s i p : I) (hsi : s ≠ i) (hip : i ≠ p) (hsp : s ≠ p)
    (k l t : J) (htl : t ≠ l) (a b : R) :
    ⁅x s i hsi (Matrix.single k l a), diagElem i p hip l t b⁆ =
      x s i hsi (Matrix.single k t (a * b)) := by
  unfold diagElem
  rw [commutator_x_diag s i p hsi hip hsp (Matrix.single k l a) (Matrix.single l t b)
      (Matrix.single t t (1 : R)) (single_one_mul_single t l t htl b),
    Matrix.single_mul_single_same (c := a) k l t b,
    Matrix.single_mul_single_same (c := a * b) k t t (1 : R), mul_one]

/-- `⁅diagElem i p k l a, x_{ij}(e_{lt} b)⁆ = x_{ij}(e_{kt}(a b))` for `l ≠ k`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem commutator_diagElem_x (i p j : I) (hip : i ≠ p) (hij : i ≠ j) (hpj : p ≠ j)
    (k l t : J) (hlk : l ≠ k) (a b : R) :
    ⁅diagElem i p hip k l a, x i j hij (Matrix.single l t b)⁆ =
      x i j hij (Matrix.single k t (a * b)) := by
  unfold diagElem
  rw [commutator_diag_x i p j hip hij hpj (Matrix.single k l a) (Matrix.single l l (1 : R))
      (Matrix.single l t b) (single_one_mul_single l k l hlk a),
    Matrix.single_mul_single_same (c := (1 : R)) l l t b, one_mul,
    Matrix.single_mul_single_same (c := a) k l t b]

/-- `⁅diagElem i q k l a, diagElem i p l t b⁆ = diagElem i p k t (a b)` for pairwise distinct
`k, l, t` and `q ≠ p`.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem commutator_diagElem_diagElem (i p q : I) (hip : i ≠ p) (hiq : i ≠ q) (hqp : q ≠ p)
    (k l t : J) (hlk : l ≠ k) (htl : t ≠ l) (htk : t ≠ k) (a b : R) :
    ⁅diagElem i q hiq k l a, diagElem i p hip l t b⁆ = diagElem i p hip k t (a * b) := by
  have hV : ⁅x i p hip (Matrix.single l t b), x p i hip.symm (Matrix.single t t (1 : R))⁆ =
      diagElem i p hip l t b := rfl
  have hXY : diagElem i q hiq k l a * x i p hip (Matrix.single l t b) *
      (diagElem i q hiq k l a)⁻¹ =
      x i p hip (Matrix.single k t (a * b)) * x i p hip (Matrix.single l t b) := by
    rw [conj_eq_commutator_mul, commutator_diagElem_x i q p hiq hip hqp k l t hlk a b]
  have hXZ : Commute (diagElem i q hiq k l a) (x p i hip.symm (Matrix.single t t (1 : R))) :=
    (commute_x_diagElem p i q q hip.symm hiq hiq hqp.symm k l hlk a t t htk 1).symm
  have hUV : Commute (x i p hip (Matrix.single k t (a * b))) (diagElem i p hip l t b) :=
    (commute_diagElem_x i p p q hip hip hiq hqp l t htl b k t htk (a * b)).symm
  have hVZ : Commute (diagElem i p hip l t b) (x p i hip.symm (Matrix.single t t (1 : R))) :=
    (commute_x_diagElem p i p q hip.symm hip hiq hqp.symm l t htl b t t htl 1).symm
  have h := commutator_switch_aux (diagElem i q hiq k l a) (x i p hip (Matrix.single l t b))
    (x p i hip.symm (Matrix.single t t (1 : R))) (x i p hip (Matrix.single k t (a * b)))
    (diagElem i p hip l t b) hV hXY hXZ hUV hVZ
  exact h

end GroupApproximation.Full.LVCohnK2
