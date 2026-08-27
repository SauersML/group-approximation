import GroupApproximation.Sofic.MaxDisplacement
import GroupApproximation.Sofic.MoverGeneration

/-!
# The action-form estimate layer, assembled

`Sofic.MaxDisplacement` has the three estimates of the action-form collapse
criterion as separate lemmas -- inversion cost, the word bound, the argmax
pigeonhole -- and `Sofic.MoverGeneration` has the generation statement.  What
was missing is the assembly: the criterion does not use them one at a time, it
uses them over *one* letter set, the stabiliser of the basepoint together with
a finite symmetric mover family, and the whole point of Fournier-Facio's
refinement is that this set needs no distinguished element.

Three steps, in the order the criterion consumes them.

* `dist_smul_le_of_stabilizer_union_movers` -- every letter of that set moves
  the basepoint by at most `k + e`, where `k` bounds the movers.  The
  stabiliser letters contribute displacement zero, which is what lets the
  bookkeeping subgroup be enlarged to the *full* stabiliser for free: folding a
  generator that fixes the basepoint into `H` costs nothing in the estimate.
* `exists_dist_smul_le_of_finite_generation` -- consequently every element of a
  finitely generated `Γ` has displacement at most `r (k + 2e)` for a word
  length `r` depending only on the element.  This is the estimate `δ(g) ≤ C_g k`
  of the criterion, with the max-displacement normalization already in place:
  `k` is a bound on the mover family as a whole, not on one designated mover.
* `exists_mem_forall_le_infinite` -- and the argmax over that family is
  constant along an infinite set of stages, so the top-scale mover can be
  chosen once for the whole subsequence.  Its normalized displacement there is
  `k / k = 1` (`normalized_argmax_eq_one`), which is the quantity the
  spectral-gap contradiction consumes.

Nothing here is analytic and nothing here is about MF-ness.  The remaining
input of the criterion is the analytic core, which enters
`BlockAmplificationRepair.not_isOperatorMF_of_no_multiMarked` as the hypothesis
`hkill`; the naive "the argmax defect dies along the argmax subsequence" is
false in a `c₀`-corona and is exactly what the finite block amplification in
that file replaces.  This file supplies the combinatorial half in the shape
that hypothesis expects, and claims nothing about the other half.
-/

namespace GroupApproximation
namespace MaxDisplacement

universe u v

variable {Γ : Type u} [Group Γ] {X : Type v} [MulAction Γ X] {d : X → X → ℝ}

/-! ## The letter set: full stabiliser, plus a symmetric finite mover family -/

/-- The letter set is symmetric: the stabiliser is a subgroup, and the mover
family has been symmetrized by hand. -/
theorem inv_mem_stabilizer_union_movers (x₀ : X) (M : Finset Γ) {s : Γ}
    (hs : s ∈ (MulAction.stabilizer Γ x₀ : Set Γ) ∪
      ((M : Set Γ) ∪ (M : Set Γ)⁻¹)) :
    s⁻¹ ∈ (MulAction.stabilizer Γ x₀ : Set Γ) ∪
      ((M : Set Γ) ∪ (M : Set Γ)⁻¹) := by
  rcases hs with hstab | hmem | hinvmem
  · exact Or.inl (SetLike.mem_coe.mpr
      (Subgroup.inv_mem _ (SetLike.mem_coe.mp hstab)))
  · exact Or.inr (Or.inr (Set.mem_inv.mpr (by rwa [inv_inv])))
  · exact Or.inr (Or.inl (Set.mem_inv.mp hinvmem))

/-- **Every letter is bounded by the mover scale.**  A stabiliser letter has
displacement zero; a mover has displacement at most `k` by hypothesis; the
inverse of a mover costs one invariance error more (Lemma 5.1).

The first case is the one that matters for the refinement: it says the full
stabiliser can be used as the bookkeeping subgroup at no cost, so a generating
set may be split into movers and non-movers without choosing anything. -/
theorem dist_smul_le_of_stabilizer_union_movers
    (hrefl : ∀ x : X, d x x = 0) (hsymm : ∀ x y : X, d x y = d y x)
    {e k : ℝ} (he : 0 ≤ e) (hk : 0 ≤ k)
    (hinv : AlmostLeftInvariant (G := Γ) d e)
    (x₀ : X) (M : Finset Γ) (hM : ∀ m ∈ M, d x₀ (m • x₀) ≤ k) :
    ∀ s ∈ (MulAction.stabilizer Γ x₀ : Set Γ) ∪ ((M : Set Γ) ∪ (M : Set Γ)⁻¹),
      d x₀ (s • x₀) ≤ k + e := by
  rintro s (hstab | hmem | hinvmem)
  · have hfix : s • x₀ = x₀ :=
      MulAction.mem_stabilizer_iff.mp (SetLike.mem_coe.mp hstab)
    rw [hfix, hrefl x₀]
    linarith
  · have h := hM s (Finset.mem_coe.mp hmem)
    linarith
  · have hm : s⁻¹ ∈ M := Finset.mem_coe.mp (Set.mem_inv.mp hinvmem)
    have h := dist_inv_smul_le hsymm hinv x₀ s⁻¹
    rw [inv_inv] at h
    have h2 := hM _ hm
    linarith

/-! ## The word estimate over the whole group -/

/-- **The estimate the criterion uses.**  Over the stabiliser-plus-movers
letter set, every element has displacement at most a word length times
`k + 2e`.  The constant depends on the element only, and `k` is a bound on the
*family*, so no mover is distinguished. -/
theorem exists_dist_smul_le_of_closure
    (hrefl : ∀ x : X, d x x = 0) (hsymm : ∀ x y : X, d x y = d y x)
    (htri : ∀ x y z : X, d x z ≤ d x y + d y z)
    {e k : ℝ} (he : 0 ≤ e) (hk : 0 ≤ k)
    (hinv : AlmostLeftInvariant (G := Γ) d e)
    (x₀ : X) (M : Finset Γ) (hM : ∀ m ∈ M, d x₀ (m • x₀) ≤ k) {g : Γ}
    (hg : g ∈ Subgroup.closure ((MulAction.stabilizer Γ x₀ : Set Γ) ∪
      ((M : Set Γ) ∪ (M : Set Γ)⁻¹))) :
    ∃ r : ℕ, d x₀ (g • x₀) ≤ (r : ℝ) * ((k + e) + e) :=
  dist_smul_le_of_mem_closure hrefl htri hinv x₀ _
    (dist_smul_le_of_stabilizer_union_movers hrefl hsymm he hk hinv x₀ M hM)
    (fun _ hs => inv_mem_stabilizer_union_movers x₀ M hs) hg

/-- **The same estimate from a finite generating set alone.**  Split the
generators by whether they move the basepoint: the non-movers land in the
stabiliser, the movers form the finite family, and Corollary 4.2 says the two
together still generate.  Only the moving generators need a displacement
bound. -/
theorem exists_dist_smul_le_of_finite_generation
    (hrefl : ∀ x : X, d x x = 0) (hsymm : ∀ x y : X, d x y = d y x)
    (htri : ∀ x y z : X, d x z ≤ d x y + d y z)
    {e k : ℝ} (he : 0 ≤ e) (hk : 0 ≤ k)
    (hinv : AlmostLeftInvariant (G := Γ) d e)
    (x₀ : X) (S : Finset Γ) (hS : Subgroup.closure (S : Set Γ) = ⊤)
    (hSk : ∀ s ∈ S, s • x₀ ≠ x₀ → d x₀ (s • x₀) ≤ k) (g : Γ) :
    ∃ r : ℕ, d x₀ (g • x₀) ≤ (r : ℝ) * ((k + e) + e) := by
  classical
  set M : Finset Γ := S.filter (fun s => s • x₀ ≠ x₀) with hMdef
  have hgen : Subgroup.closure ((MulAction.stabilizer Γ x₀ : Set Γ) ∪
      ((M : Set Γ) ∪ (M : Set Γ)⁻¹)) = ⊤ := by
    refine top_unique ?_
    rw [← hS]
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    by_cases h : x • x₀ = x₀
    · exact Subgroup.subset_closure (Or.inl (SetLike.mem_coe.mpr
        (MulAction.mem_stabilizer_iff.mpr h)))
    · refine Subgroup.subset_closure (Or.inr (Or.inl ?_))
      rw [hMdef]
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hx, h⟩)
  refine exists_dist_smul_le_of_closure hrefl hsymm htri he hk hinv x₀ M ?_ ?_
  · intro m hm
    rw [hMdef] at hm
    have hm' := Finset.mem_filter.mp hm
    exact hSk m hm'.1 hm'.2
  · rw [hgen]
    exact Subgroup.mem_top g

/-! ## One top-scale mover for the whole subsequence -/

omit [Group Γ] in
/-- **Lemma 5.3, assembled.**  Choose an argmax mover at every stage; since the
family is finite, one member is the argmax at infinitely many stages, and along
those stages it realizes the maximal displacement of the whole family.

This is what makes the normalization `k_n := max_i d_n(x₀, γ_i x₀)` usable: the
element carrying normalized mass `1` at the top scale can be fixed once, rather
than varying with the stage. -/
theorem exists_mem_forall_le_infinite (M : Finset Γ) (hMne : M.Nonempty)
    (D : ℕ → Γ → ℝ) :
    ∃ a ∈ M, {n : ℕ | ∀ m ∈ M, D n m ≤ D n a}.Infinite := by
  classical
  haveI : Fintype {x : Γ // x ∈ M} := FinsetCoe.fintype M
  choose a ha hmax using fun n : ℕ => exists_max_mover M hMne (D n)
  obtain ⟨b, hb⟩ :=
    exists_infinite_constant_argmax (fun n : ℕ => (⟨a n, ha n⟩ : {x : Γ // x ∈ M}))
  refine ⟨(b : Γ), b.2, hb.mono ?_⟩
  intro n hn
  have hab : a n = (b : Γ) := congrArg Subtype.val hn
  intro m hm
  have := hmax n m hm
  rwa [hab] at this

end MaxDisplacement
end GroupApproximation
