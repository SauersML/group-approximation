import GroupApproximation.Leavitt.ElementarySimplicity
import GroupApproximation.Leavitt.LeavittMarkNontrivial
import GroupApproximation.Leavitt.BinaryLeavittSimple

/-!
# Root detection for `EL_ι(R)` when `R` carries a Leavitt family

`Leavitt.ElementarySimplicity` reduces Proposition `prop:simple` of
`non_mf_groups_exist.tex` to the single statement

  `RootDetection ι R`: every nontrivial normal subgroup of `EL_ι(R)` contains a
  nonzero elementary root `e_{ij}(x)`,

and proves everything downstream of it.  This file **proves**
`RootDetection ι R` for a coefficient ring that

* has two-sided division (`hdiv`: every nonzero `x` has `a * x * b = 1`),
* has no nontrivial central units (`hcentral`), and
* carries a binary Leavitt family `L` (`LeavittFamily R`).

All three hold for `R = L_{𝔽₂}(1,2)`, so the manuscript's `prop:simple` is
obtained unconditionally at the end of the file
(`isSimpleGroup_elementaryGroup_binaryLeavitt`).  No Preusser-style sandwich
classification is used, and no statement here carries a leading hypothesis
binder that is not discharged for the binary Leavitt algebra.

## The argument

Take `N ⊴ EL_ι(R)` with `N ≠ ⊥`, and `g ∈ N`, `g ≠ 1`.

**Diagonal branch.**  If `elMat (g⁻¹)` is diagonal then so is `elMat g`
(`elMat_inv_offDiag`), its diagonal entries `d_u` are units, and conjugation of
a root is a *root*: `g e_{kl}(a) g⁻¹ = e_{kl}(d_k a d_l⁻¹)`
(`conj_elGen_of_diagonal`).  Hence `⁅g, e_{kl}(a)⁆ = e_{kl}(d_k a d_l⁻¹ - a)`
lies in `N`, and it is a *nonzero* root unless `d_k a d_l⁻¹ = a` for every
`k ≠ l` and every `a` — which forces all `d_u` equal to one central unit, hence
equal to `1` by `hcentral`, hence `g = 1` (`exists_elGen_mem_of_diagonal`).

**Off-diagonal branch.**  Otherwise `elMat (g⁻¹) l p ≠ 0` for some `l ≠ p`.
Feed the landed double commutator `exists_colMatrix_mem_of_mem` the indices
`k ≠ l` arbitrary, `p`, and column index `q = l`; the four distinctness
constraints `k ≠ l`, `p ≠ q`, `l ≠ p`, `q ≠ k` all collapse to `k ≠ l` and
`l ≠ p`.  What is left is one *ring* obligation: coefficients `a, b` with

  `b * (elMat g) l k * a = 0`   and   `a * ((elMat g⁻¹) l p * b) ≠ 0`.

`exists_split_annihilator` supplies them from `hdiv` and the Leavitt relations
alone.  Writing `α c β = 1` for the obstruction entry `c = (elMat g) l k`, take
`a = β s₁` and `b = t₀ α`; then `b c a = t₀ (α c β) s₁ = t₀ s₁ = 0`, while
`a d b = β s₁ d t₀ α` is nonzero because sandwiching it back by `α c` and
`c β` returns `s₁ d t₀`, and `t₁ (s₁ d t₀) s₀ = d ≠ 0`.  Finally no column of
an invertible matrix annihilates a nonzero element on the right
(`∑_t (g⁻¹)_{kt} g_{tk} = 1`), so the produced column really is nonzero and the
landed extraction lemma `exists_elGen_mem_of_colMatrix_mem` returns the root.
-/

namespace GroupApproximation
namespace RootDetectionBinary

open ElementarySimplicity

/-! ## Sums against a diagonal matrix -/

section DiagonalSums

variable {ι R : Type*} [Fintype ι] [Ring R]

/-- A matrix product `∑_t A_{ut} B_{tv}` collapses when the *left* factor is
diagonal. -/
theorem sum_mul_of_diag_left (A B : Matrix ι ι R)
    (hA : ∀ u v : ι, u ≠ v → A u v = 0) (u v : ι) :
    ∑ t, A u t * B t v = A u u * B u v := by
  rw [Finset.sum_eq_single u]
  · intro t _ ht
    rw [hA u t (Ne.symm ht), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ u) h

/-- A matrix product `∑_t A_{ut} B_{tv}` collapses when the *right* factor is
diagonal. -/
theorem sum_mul_of_diag_right (A B : Matrix ι ι R)
    (hB : ∀ u v : ι, u ≠ v → B u v = 0) (u v : ι) :
    ∑ t, A u t * B t v = A u v * B v v := by
  rw [Finset.sum_eq_single v]
  · intro t _ ht
    rw [hB t v ht, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ v) h

end DiagonalSums

/-! ## Diagonal elements of `EL_ι(R)` -/

section Diagonal

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- Conjugating a single entry by two diagonal matrices keeps it a single
entry. -/
theorem conj_single_of_diagonal (A B : Matrix ι ι R)
    (hA : ∀ u v : ι, u ≠ v → A u v = 0) (hB : ∀ u v : ι, u ≠ v → B u v = 0)
    (k l : ι) (a : R) :
    A * Matrix.single k l a * B = Matrix.single k l (A k k * (a * B l l)) := by
  have hrow : (fun v => a * B l v) = (fun y => if y = l then a * B l l else 0) := by
    funext v
    by_cases hv : v = l
    · rw [if_pos hv, hv]
    · rw [if_neg hv, hB l v (fun h => hv h.symm), mul_zero]
  have hcol : (fun x => A x k * (a * B l l))
      = (fun x => if x = k then A k k * (a * B l l) else 0) := by
    funext x
    by_cases hx : x = k
    · rw [if_pos hx, hx]
    · rw [if_neg hx, hA x k hx, zero_mul]
  have h1 : Matrix.single k l a * B = Matrix.single k l (a * B l l) := by
    rw [single_mul_eq, single_eq_rowMatrix, hrow]
  rw [mul_assoc, h1, mul_single_eq, single_eq_colMatrix, hcol]

/-- A diagonal element of `EL_ι(R)` has unit diagonal entries. -/
theorem elMat_diag_mul_inv (g : elementaryGroup ι R)
    (hg : ∀ u v : ι, u ≠ v → elMat g u v = 0) (u : ι) :
    elMat g u u * elMat (g⁻¹) u u = 1 := by
  have h := congrFun (congrFun (elMat_mul_inv g) u) u
  rw [Matrix.mul_apply, sum_mul_of_diag_left (elMat g) (elMat (g⁻¹)) hg u u,
    Matrix.one_apply, if_pos (rfl : u = u)] at h
  exact h

/-- The same, on the other side. -/
theorem elMat_inv_diag_mul (g : elementaryGroup ι R)
    (hg : ∀ u v : ι, u ≠ v → elMat g u v = 0) (u : ι) :
    elMat (g⁻¹) u u * elMat g u u = 1 := by
  have h := congrFun (congrFun (elMat_inv_mul g) u) u
  rw [Matrix.mul_apply, sum_mul_of_diag_right (elMat (g⁻¹)) (elMat g) hg u u,
    Matrix.one_apply, if_pos (rfl : u = u)] at h
  exact h

/-- **The inverse of a diagonal element is diagonal.** -/
theorem elMat_inv_offDiag (g : elementaryGroup ι R)
    (hg : ∀ u v : ι, u ≠ v → elMat g u v = 0) {u v : ι} (huv : u ≠ v) :
    elMat (g⁻¹) u v = 0 := by
  have h := congrFun (congrFun (elMat_mul_inv g) u) v
  rw [Matrix.mul_apply, sum_mul_of_diag_left (elMat g) (elMat (g⁻¹)) hg u v,
    Matrix.one_apply, if_neg huv] at h
  calc elMat (g⁻¹) u v
      = elMat (g⁻¹) u u * elMat g u u * elMat (g⁻¹) u v := by
        rw [elMat_inv_diag_mul g hg u, one_mul]
    _ = elMat (g⁻¹) u u * (elMat g u u * elMat (g⁻¹) u v) := by rw [mul_assoc]
    _ = elMat (g⁻¹) u u * 0 := by rw [h]
    _ = 0 := mul_zero _

/-- **Conjugating a root by a diagonal element is again a root**, with
coefficient rescaled by the two diagonal entries at the root's indices. -/
theorem conj_elGen_of_diagonal (g : elementaryGroup ι R)
    (hg : ∀ u v : ι, u ≠ v → elMat g u v = 0) {k l : ι} (hkl : k ≠ l) (a : R) :
    g * elGen k l hkl a * g⁻¹
      = elGen k l hkl (elMat g k k * (a * elMat (g⁻¹) l l)) := by
  have hginv : ∀ u v : ι, u ≠ v → elMat (g⁻¹) u v = 0 := fun u v h =>
    elMat_inv_offDiag g hg h
  apply elMat_injective
  have hsplit : elMat (g * elGen k l hkl a * g⁻¹)
      = elMat g * elMat (elGen k l hkl a) * elMat (g⁻¹) := rfl
  rw [hsplit, elMat_elGen, elMat_elGen]
  calc elMat g * (1 + Matrix.single k l a) * elMat (g⁻¹)
      = elMat g * elMat (g⁻¹) + elMat g * Matrix.single k l a * elMat (g⁻¹) := by
        noncomm_ring
    _ = 1 + Matrix.single k l (elMat g k k * (a * elMat (g⁻¹) l l)) := by
        rw [elMat_mul_inv,
          conj_single_of_diagonal (elMat g) (elMat (g⁻¹)) hg hginv k l a]

/-- **The printed relations, read on the diagonal.**  For a diagonal `g`,
`conj_elGen_of_diagonal` turns the printed hypothesis "`g` commutes with
`e_{uv}(a)`" into the coefficient relation `λ_u a λ_v⁻¹ = a`, and conversely.
Both directions are used: the relations are what the printed argument computes
with, and the commuting form is what it assumes. -/
theorem commute_elGen_iff_diag_relation (g : elementaryGroup ι R)
    (hg : ∀ u v : ι, u ≠ v → elMat g u v = 0) {u v : ι} (huv : u ≠ v) (a : R) :
    g * elGen u v huv a = elGen u v huv a * g
      ↔ elMat g u u * (a * elMat (g⁻¹) v v) = a := by
  constructor
  · intro hcomm
    have hconj : g * elGen u v huv a * g⁻¹ = elGen u v huv a := by
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [conj_elGen_of_diagonal g hg huv a] at hconj
    have hone : elGen u v huv
        (elMat g u u * (a * elMat (g⁻¹) v v) - a) = 1 := by
      rw [sub_eq_add_neg, ← elGen_mul, hconj, elGen_mul, add_neg_cancel,
        elGen_zero]
    exact sub_eq_zero.mp ((LeavittMark.elGen_eq_one_iff u v huv _).mp hone)
  · intro hrel
    have hconj : g * elGen u v huv a * g⁻¹ = elGen u v huv a := by
      rw [conj_elGen_of_diagonal g hg huv a, hrel]
    calc g * elGen u v huv a
        = g * elGen u v huv a * g⁻¹ * g := by
          rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = elGen u v huv a * g := by rw [hconj]

/-- **`prop:simple`, diagonal case, first printed step.**  "If `g` commutes with
every `e_{ij}(a)`, then the relations with `a = 1` give `λ_i = λ_j` for all
`i ≠ j`." -/
theorem elMat_diag_eq_of_commute_elGen (g : elementaryGroup ι R)
    (hg : ∀ u v : ι, u ≠ v → elMat g u v = 0)
    (hcomm : ∀ (u v : ι) (huv : u ≠ v) (a : R),
      g * elGen u v huv a = elGen u v huv a * g)
    {i j : ι} (hij : i ≠ j) :
    elMat g i i = elMat g j j := by
  have h1 : elMat g i i * elMat (g⁻¹) j j = 1 := by
    have h2 := (commute_elGen_iff_diag_relation g hg hij 1).mp (hcomm i j hij 1)
    rwa [one_mul] at h2
  calc elMat g i i
      = elMat g i i * (elMat (g⁻¹) j j * elMat g j j) := by
        rw [elMat_inv_diag_mul g hg j, mul_one]
    _ = elMat g i i * elMat (g⁻¹) j j * elMat g j j := by rw [← mul_assoc]
    _ = elMat g j j := by rw [h1, one_mul]

/-- **`prop:simple`, diagonal case, second printed step.**  "Hence
`g = λ I₁₂` for some unit `λ ∈ R`."  The scalar is the common diagonal entry
supplied by the previous step, and its inverse is the corresponding diagonal
entry of `g⁻¹`. -/
theorem exists_unit_elMat_eq_diagonal_of_commute_elGen [Nontrivial ι]
    (g : elementaryGroup ι R)
    (hg : ∀ u v : ι, u ≠ v → elMat g u v = 0)
    (hcomm : ∀ (u v : ι) (huv : u ≠ v) (a : R),
      g * elGen u v huv a = elGen u v huv a * g) :
    ∃ lam : R, (∃ mu : R, lam * mu = 1 ∧ mu * lam = 1) ∧
      elMat g = Matrix.diagonal fun _ : ι => lam := by
  obtain ⟨k, -, -⟩ := exists_pair_ne ι
  refine ⟨elMat g k k, ⟨elMat (g⁻¹) k k, elMat_diag_mul_inv g hg k,
    elMat_inv_diag_mul g hg k⟩, ?_⟩
  ext u v
  rw [Matrix.diagonal_apply]
  by_cases huv : u = v
  · rw [if_pos huv, ← huv]
    by_cases hu : u = k
    · rw [hu]
    · exact elMat_diag_eq_of_commute_elGen g hg hcomm hu
  · rw [if_neg huv]
    exact hg u v huv

/-- **`prop:simple`, diagonal case, third printed step.**  "The relations for
arbitrary `a ∈ R` then give `λ a = a λ`, so `λ ∈ Z(R)^×`."  Both halves of the
membership are stated: the scalar commutes with every coefficient, and it is a
two-sided unit. -/
theorem elMat_diag_central_unit_of_commute_elGen [Nontrivial ι]
    (g : elementaryGroup ι R)
    (hg : ∀ u v : ι, u ≠ v → elMat g u v = 0)
    (hcomm : ∀ (u v : ι) (huv : u ≠ v) (a : R),
      g * elGen u v huv a = elGen u v huv a * g) (u : ι) :
    (∀ x : R, elMat g u u * x = x * elMat g u u) ∧
      ∃ mu : R, elMat g u u * mu = 1 ∧ mu * elMat g u u = 1 := by
  obtain ⟨v, hvu⟩ := exists_ne u
  have huv : u ≠ v := Ne.symm hvu
  refine ⟨fun x => ?_, elMat (g⁻¹) u u, elMat_diag_mul_inv g hg u,
    elMat_inv_diag_mul g hg u⟩
  have hrel := (commute_elGen_iff_diag_relation g hg huv x).mp (hcomm u v huv x)
  calc elMat g u u * x
      = elMat g u u * (x * (elMat (g⁻¹) v v * elMat g v v)) := by
        rw [elMat_inv_diag_mul g hg v, mul_one]
    _ = elMat g u u * (x * elMat (g⁻¹) v v) * elMat g v v := by noncomm_ring
    _ = x * elMat g v v := by rw [hrel]
    _ = x * elMat g u u := by
        rw [elMat_diag_eq_of_commute_elGen g hg hcomm huv]

/-- **Root detection, diagonal branch.**  A normal subgroup containing a
nontrivial *diagonal* element contains a nonzero elementary root, as soon as the
coefficient ring has no nontrivial central unit. -/
theorem exists_elGen_mem_of_diagonal [Nontrivial ι]
    (hcentral : ∀ lam : R, (∀ x : R, lam * x = x * lam) →
      (∃ mu : R, lam * mu = 1 ∧ mu * lam = 1) → lam = 1)
    (N : Subgroup (elementaryGroup ι R)) [hN : N.Normal]
    (g : elementaryGroup ι R) (hg : g ∈ N) (hgne : g ≠ 1)
    (hdiag : ∀ u v : ι, u ≠ v → elMat g u v = 0) :
    ∃ (i j : ι) (hij : i ≠ j) (x : R), x ≠ 0 ∧ elGen i j hij x ∈ N := by
  by_cases hall : ∀ u v : ι, u ≠ v → ∀ a : R,
      elMat g u u * (a * elMat (g⁻¹) v v) = a
  · -- Every conjugation is trivial, so `g` is a central scalar, so `g = 1`.
    exfalso
    apply hgne
    have hcomm : ∀ (u v : ι) (huv : u ≠ v) (a : R),
        g * elGen u v huv a = elGen u v huv a * g := fun u v huv a =>
      (commute_elGen_iff_diag_relation g hdiag huv a).mpr (hall u v huv a)
    obtain ⟨lam, ⟨mu, hlm, hml⟩, hscal⟩ :=
      exists_unit_elMat_eq_diagonal_of_commute_elGen g hdiag hcomm
    obtain ⟨k, -, -⟩ := exists_pair_ne ι
    have hk : elMat g k k = lam := by
      rw [hscal, Matrix.diagonal_apply, if_pos (rfl : k = k)]
    have hcen : ∀ x : R, lam * x = x * lam := by
      intro x
      have h := (elMat_diag_central_unit_of_commute_elGen g hdiag hcomm k).1 x
      rwa [hk] at h
    have hlam : lam = 1 := hcentral lam hcen ⟨mu, hlm, hml⟩
    apply elMat_injective
    rw [elMat_one]
    ext u v
    rw [hscal, Matrix.diagonal_apply, Matrix.one_apply]
    by_cases huv : u = v
    · rw [if_pos huv, if_pos huv]
      exact hlam
    · rw [if_neg huv, if_neg huv]
  · -- Some conjugation moves a root, and the commutator is that moved root.
    push Not at hall
    obtain ⟨u, v, huv, a, ha⟩ := hall
    have hinv : (elGen u v huv a)⁻¹ = elGen (R := R) u v huv (-a) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [elGen_mul, add_neg_cancel, elGen_zero]
    have heq : g * elGen u v huv a * g⁻¹ * (elGen u v huv a)⁻¹
        = elGen u v huv (elMat g u u * (a * elMat (g⁻¹) v v) - a) := by
      rw [conj_elGen_of_diagonal g hdiag huv a, hinv, elGen_mul,
        ← sub_eq_add_neg]
    have hmem : g * elGen u v huv a * g⁻¹ * (elGen u v huv a)⁻¹ ∈ N := by
      have h1 : elGen u v huv a * g⁻¹ * (elGen u v huv a)⁻¹ ∈ N :=
        hN.conj_mem (g⁻¹) (N.inv_mem hg) (elGen u v huv a)
      have h2 : g * elGen u v huv a * g⁻¹ * (elGen u v huv a)⁻¹
          = g * (elGen u v huv a * g⁻¹ * (elGen u v huv a)⁻¹) := by
        simp only [mul_assoc]
      rw [h2]
      exact N.mul_mem hg h1
    rw [heq] at hmem
    exact ⟨u, v, huv, elMat g u u * (a * elMat (g⁻¹) v v) - a,
      sub_ne_zero_of_ne ha, hmem⟩

end Diagonal

/-! ## The off-diagonal branch -/

section OffDiagonal

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- **Root detection, off-diagonal branch.**  If some `g ∈ N` has an inverse
with a nonzero off-diagonal entry, and the coefficient ring can split the
obstruction (`hsplit`), then `N` contains a nonzero elementary root.

The four distinctness constraints of the landed double-commutator theorem
`exists_colMatrix_mem_of_mem` are met with column index `q = l`, and the
scalar obstruction `b * g_{lk} * a` is exactly what `hsplit` kills. -/
theorem exists_elGen_mem_of_offDiag_inv
    (hcard : 3 ≤ Fintype.card ι)
    (hsplit : ∀ c d : R, d ≠ 0 → ∃ a b : R, b * c * a = 0 ∧ a * (d * b) ≠ 0)
    (N : Subgroup (elementaryGroup ι R)) [N.Normal]
    (g : elementaryGroup ι R) (hg : g ∈ N) {l p : ι} (hlp : l ≠ p)
    (hd : elMat (g⁻¹) l p ≠ 0) :
    ∃ (i j : ι) (hij : i ≠ j) (x : R), x ≠ 0 ∧ elGen i j hij x ∈ N := by
  obtain ⟨k, hkl, -⟩ := exists_third_index hcard l p
  obtain ⟨a, b, hobs, hw⟩ := hsplit (elMat g l k) (elMat (g⁻¹) l p) hd
  obtain ⟨M, hM, hval⟩ :=
    exists_colMatrix_mem_of_mem N hg hkl (Ne.symm hlp) hlp (Ne.symm hkl) a b hobs
  have hcol : ∃ x : ι, elMat g x k * (a * (elMat (g⁻¹) l p * b)) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hw
    have h1 : ∑ t, elMat (g⁻¹) k t * elMat g t k = 1 := by
      have h := congrFun (congrFun (elMat_inv_mul g) k) k
      rwa [Matrix.mul_apply, Matrix.one_apply, if_pos (rfl : k = k)] at h
    calc a * (elMat (g⁻¹) l p * b)
        = (∑ t, elMat (g⁻¹) k t * elMat g t k) *
            (a * (elMat (g⁻¹) l p * b)) := by rw [h1, one_mul]
      _ = ∑ t, elMat (g⁻¹) k t *
            (elMat g t k * (a * (elMat (g⁻¹) l p * b))) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun t _ => mul_assoc _ _ _
      _ = 0 := Finset.sum_eq_zero fun t _ => by rw [hcon t, mul_zero]
  obtain ⟨x, hx⟩ := hcol
  obtain ⟨i, hix, hil⟩ := exists_third_index hcard x l
  obtain ⟨c, hmem, hc⟩ := exists_elGen_mem_of_colMatrix_mem N hM hval hix hil 1
  refine ⟨i, l, hil, c, hc ?_, hmem⟩
  rw [one_mul]
  exact hx

end OffDiagonal

/-! ## The ring obligation, discharged by a Leavitt family -/

section Split

variable {R : Type*} [Ring R]

/-- **The ring obligation of the off-diagonal branch.**  In a ring with
two-sided division that carries a binary Leavitt family, for every `c` and every
nonzero `d` there are coefficients `a, b` annihilating `c` in the order
`b * c * a` while keeping `a * (d * b)` nonzero.

For `c ≠ 0` pick a sandwich `α c β = 1` and take `a = β s₁`, `b = t₀ α`.  Then
`b c a = t₀ (α c β) s₁ = t₀ s₁ = 0` by the Leavitt relation `t₀ s₁ = 0`, while
`a d b = β s₁ d t₀ α = 0` would give `s₁ d t₀ = 0` after re-sandwiching, hence
`d = t₁ (s₁ d t₀) s₀ = 0` by `t₁ s₁ = 1` and `t₀ s₀ = 1`. -/
theorem exists_split_annihilator (L : LeavittFamily R)
    (hdiv : ∀ x : R, x ≠ 0 → ∃ a b : R, a * x * b = 1)
    (c d : R) (hd : d ≠ 0) :
    ∃ a b : R, b * c * a = 0 ∧ a * (d * b) ≠ 0 := by
  by_cases hc : c = 0
  · refine ⟨1, 1, ?_, ?_⟩
    · rw [hc, mul_zero, zero_mul]
    · rw [one_mul, mul_one]
      exact hd
  · obtain ⟨al, be, hab⟩ := hdiv c hc
    refine ⟨be * L.s1, L.t0 * al, ?_, ?_⟩
    · calc L.t0 * al * c * (be * L.s1)
          = L.t0 * (al * c * be) * L.s1 := by noncomm_ring
        _ = L.t0 * 1 * L.s1 := by rw [hab]
        _ = 0 := by rw [mul_one, L.t0_s1]
    · intro hzero
      apply hd
      have h1 : L.s1 * d * L.t0 = 0 := by
        calc L.s1 * d * L.t0
            = al * c * be * (L.s1 * d * L.t0) * (al * c * be) := by
              rw [hab, one_mul, mul_one]
          _ = al * c * (be * L.s1 * (d * (L.t0 * al))) * (c * be) := by
              noncomm_ring
          _ = 0 := by rw [hzero, mul_zero, zero_mul]
      calc d = L.t1 * L.s1 * d * (L.t0 * L.s0) := by
            rw [L.t1_s1, L.t0_s0, one_mul, mul_one]
        _ = L.t1 * (L.s1 * d * L.t0) * L.s0 := by noncomm_ring
        _ = 0 := by rw [h1, mul_zero, zero_mul]

end Split

/-! ## Root detection -/

section Detection

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- **Root detection.**  For at least three indices and a coefficient ring with
two-sided division, no nontrivial central units, and a binary Leavitt family,
every nontrivial normal subgroup of `EL_ι(R)` contains a nonzero elementary
root.  This is the statement the manuscript imports from Preusser's
normal-subgroup theorem; here it is proved. -/
theorem rootDetection_of_leavittFamily
    (hcard : 3 ≤ Fintype.card ι) (L : LeavittFamily R)
    (hdiv : ∀ x : R, x ≠ 0 → ∃ a b : R, a * x * b = 1)
    (hcentral : ∀ lam : R, (∀ x : R, lam * x = x * lam) →
      (∃ mu : R, lam * mu = 1 ∧ mu * lam = 1) → lam = 1) :
    RootDetection ι R := by
  haveI : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  intro N hN hbot
  haveI : N.Normal := hN
  have hex : ¬ ∀ z ∈ N, z = 1 := fun h =>
    hbot ((Subgroup.eq_bot_iff_forall N).mpr h)
  push Not at hex
  obtain ⟨g, hg, hgne⟩ := hex
  by_cases hdiag : ∀ u v : ι, u ≠ v → elMat (g⁻¹) u v = 0
  · have hgdiag : ∀ u v : ι, u ≠ v → elMat g u v = 0 := by
      intro u v huv
      have h := elMat_inv_offDiag (g⁻¹) hdiag huv
      rwa [inv_inv] at h
    exact exists_elGen_mem_of_diagonal hcentral N g hg hgne hgdiag
  · push Not at hdiag
    obtain ⟨l, p, hlp, hd⟩ := hdiag
    exact exists_elGen_mem_of_offDiag_inv hcard
      (exists_split_annihilator L hdiv) N g hg hlp hd

/-- **Simplicity of `EL_ι(R)`**, from root detection and the landed reduction
`isSimpleGroup_of_rootDetection`. -/
theorem isSimpleGroup_of_leavittFamily
    (hcard : 3 ≤ Fintype.card ι) (L : LeavittFamily R)
    (hdiv : ∀ x : R, x ≠ 0 → ∃ a b : R, a * x * b = 1)
    (hcentral : ∀ lam : R, (∀ x : R, lam * x = x * lam) →
      (∃ mu : R, lam * mu = 1 ∧ mu * lam = 1) → lam = 1)
    (hnt : Nontrivial (elementaryGroup ι R)) :
    IsSimpleGroup (elementaryGroup ι R) :=
  isSimpleGroup_of_rootDetection hcard hdiv hnt
    (rootDetection_of_leavittFamily hcard L hdiv hcentral)

end Detection

/-! ## The binary Leavitt algebra: Proposition `prop:simple` -/

section Binary

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Root detection for `EL_ι(L_{𝔽₂}(1,2))`, with every hypothesis discharged. -/
theorem rootDetection_binaryLeavitt (hcard : 3 ≤ Fintype.card ι) :
    RootDetection ι (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) :=
  rootDetection_of_leavittFamily hcard (BinaryLeavitt.family (ZMod 2))
    (fun _ hx => BinaryLeavitt.exists_mul_mul_eq_one (ZMod 2) hx)
    (fun lam hlam hinv => by
      obtain ⟨mu, h1, h2⟩ := hinv
      exact congrArg Units.val
        (BinaryLeavitt.central_units_trivial ⟨lam, mu, h1, h2⟩ hlam))

/-- **Proposition `prop:simple`.**  `EL_ι(L_{𝔽₂}(1,2))` is simple for at least
three indices.  Nothing is assumed beyond the index count. -/
theorem isSimpleGroup_elementaryGroup_binaryLeavitt
    (hcard : 3 ≤ Fintype.card ι) :
    IsSimpleGroup
      (elementaryGroup ι (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))) := by
  haveI : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  refine isSimpleGroup_of_rootDetection hcard
    (fun _ hx => BinaryLeavitt.exists_mul_mul_eq_one (ZMod 2) hx) ?_
    (rootDetection_binaryLeavitt hcard)
  exact ⟨⟨elGen i j hij 1, 1,
    LeavittMark.elGen_ne_one_of_ne_zero i j hij one_ne_zero⟩⟩

end Binary

end RootDetectionBinary
end GroupApproximation
