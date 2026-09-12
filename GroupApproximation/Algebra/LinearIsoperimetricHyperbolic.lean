import GroupApproximation.Algebra.BowditchSlim
import GroupApproximation.Algebra.DiscreteStokesArea
import GroupApproximation.Algebra.HyperbolicSlimFourPoint

/-!
# Gromov's theorem: a linear isoperimetric inequality makes a group hyperbolic

A finitely generated presentation with relators of bounded length and a linear
isoperimetric inequality presents a hyperbolic group.  The route has no van Kampen
diagrams and no planarity:

1. **Area bounds the discrete integral** (`Algebra/DiscreteStokesArea.lean`): along a
   closed word of length `ℓ`, the integral of `φ dψ` for functions moving by at most
   one along each letter is at most `K ℓ L²`.  So the letters of the presented group
   satisfy the linear Stokes inequality (`linearStokes_presentedLetters`).
2. **The quadrangle bound gives Bowditch's H4** (`Algebra/BowditchH4.lean`), at
   `r = 3 C + 1`, `L = 15 r`.
3. **H4 gives centres and slim triangles** (Bowditch's Lemmas 6.2.1--6.2.3 and
   Proposition 6.2.4: `Algebra/BowditchFellowTraveller.lean`,
   `Algebra/BowditchCorner.lean`, `Algebra/BowditchCentreAssembly.lean`,
   `Algebra/BowditchSlim.lean`).
4. **Slim triangles give the four-point condition**
   (`Hyperbolic.isHyperbolicGroup_of_isSlimTriangles`).
-/

namespace GroupApproximation
namespace DiscreteStokes

open WordMetric SmallCancellationRouter

universe u v

/-- The letters of a presented group: the images of the generators and their
inverses. -/
noncomputable def presentedLetters {α : Type u} [Fintype α] (R : Set (FreeGroup α)) :
    Finset (PresentedGroup R) := by
  classical
  exact Finset.univ.image (letterVal fun a => (PresentedGroup.of a : PresentedGroup R))

theorem mem_presentedLetters {α : Type u} [Fintype α] {R : Set (FreeGroup α)}
    {s : PresentedGroup R} :
    s ∈ presentedLetters R ↔
      ∃ x : α × Bool, letterVal (fun a => (PresentedGroup.of a : PresentedGroup R)) x = s := by
  classical
  unfold presentedLetters
  simp only [Finset.mem_image, Finset.mem_univ, true_and]

/-- The letters of a presented group form a symmetric generating set. -/
theorem isSymmetricGeneratingSet_presentedLetters {α : Type u} [Fintype α]
    (R : Set (FreeGroup α)) :
    IsSymmetricGeneratingSet
      ((presentedLetters R : Finset (PresentedGroup R)) : Set (PresentedGroup R)) := by
  refine ⟨?_, ?_⟩
  · intro s hs
    obtain ⟨⟨a, bb⟩, rfl⟩ := mem_presentedLetters.mp (Finset.mem_coe.mp hs)
    exact Finset.mem_coe.mpr (mem_presentedLetters.mpr ⟨(a, !bb), letterVal_not _ a bb⟩)
  · rw [eq_top_iff, ← PresentedGroup.closure_range_of R]
    apply Subgroup.closure_mono
    rintro s ⟨a, rfl⟩
    exact Finset.mem_coe.mpr (mem_presentedLetters.mpr ⟨(a, true), rfl⟩)

/-- A path of letters of a presented group is read off a free word. -/
theorem exists_freeWord {α : Type u} [Fintype α] {R : Set (FreeGroup α)} :
    ∀ (l : List (PresentedGroup R)), (∀ x ∈ l, x ∈ presentedLetters R) →
      ∃ w : List (α × Bool),
        w.map (letterVal fun a => (PresentedGroup.of a : PresentedGroup R)) = l
  | [], _ => ⟨[], rfl⟩
  | x :: l, hl => by
      obtain ⟨y, hy⟩ := mem_presentedLetters.mp (hl x (List.mem_cons.mpr (Or.inl rfl)))
      obtain ⟨w, hw⟩ := exists_freeWord l (fun z hz => hl z (List.mem_cons_of_mem _ hz))
      exact ⟨y :: w, by rw [List.map_cons, hy, hw]⟩

/-- The integral along the path of group elements is the integral along the free
word. -/
theorem wordSum_trueLetters_map {α : Type u} {Q : Type v} [Group Q] (f : α → Q)
    (φ ψ : Q → ℤ) :
    ∀ (b : Q) (w : List (α × Bool)),
      wordSum (id : Q → Q) φ ψ b (trueLetters (w.map (letterVal f))) = wordSum f φ ψ b w
  | _, [] => rfl
  | b, x :: w => by
      show edgeTerm φ ψ b (b * letterVal (id : Q → Q) (letterVal f x, true)) +
          wordSum (id : Q → Q) φ ψ (b * letterVal (id : Q → Q) (letterVal f x, true))
            (trueLetters (w.map (letterVal f))) =
        edgeTerm φ ψ b (b * letterVal f x) + wordSum f φ ψ (b * letterVal f x) w
      rw [letterVal_true, id_eq, wordSum_trueLetters_map f φ ψ _ w]

/-- **The linear Stokes inequality for the letters of a presented group** with relators
of length at most `L` and a linear isoperimetric inequality at constant `K`. -/
theorem linearStokes_presentedLetters {α : Type u} [Fintype α] [DecidableEq α]
    {R : Set (FreeGroup α)} {K L : ℕ} (hbound : ∀ r ∈ R, FreeGroup.norm r ≤ L)
    (hiso : LinearIsoperimetric R K) :
    LinearStokes ((presentedLetters R : Finset (PresentedGroup R)) : Set (PresentedGroup R))
      (K * L ^ 2) := by
  intro φ ψ hφ hψ l hl b hprod
  obtain ⟨w, rfl⟩ := exists_freeWord l (fun x hx => Finset.mem_coe.mp (hl x hx))
  have hφ' : LipschitzOnLetters (fun a => (PresentedGroup.of a : PresentedGroup R)) φ :=
    fun g x => hφ g _ (Finset.mem_coe.mpr (mem_presentedLetters.mpr ⟨x, rfl⟩))
  have hψ' : LipschitzOnLetters (fun a => (PresentedGroup.of a : PresentedGroup R)) ψ :=
    fun g x => hψ g _ (Finset.mem_coe.mpr (mem_presentedLetters.mpr ⟨x, rfl⟩))
  have h := abs_wordSum_le_of_linearIsoperimetric hbound hiso hφ' hψ' b w hprod
  rw [wordSum_trueLetters_map, List.length_map]
  calc |wordSum (fun a => (PresentedGroup.of a : PresentedGroup R)) φ ψ b w|
      ≤ (K : ℤ) * (w.length : ℤ) * (L : ℤ) ^ 2 := h
    _ = ((K * L ^ 2 : ℕ) : ℤ) * (w.length : ℤ) := by
        push_cast
        ring

/-- **Gromov's theorem for presented groups.**  A presentation over a finite
alphabet with relators of bounded length and a linear isoperimetric inequality
presents a hyperbolic group. -/
theorem isHyperbolicGroup_presentedGroup_of_linearIsoperimetric {α : Type} [Fintype α]
    [DecidableEq α] (R : Set (FreeGroup α)) (hbound : ∃ L : ℕ, ∀ r ∈ R, FreeGroup.norm r ≤ L)
    {K : ℕ} (hiso : LinearIsoperimetric R K) :
    Hyperbolic.IsHyperbolicGroup (PresentedGroup R) := by
  obtain ⟨L, hL⟩ := hbound
  have hS := isSymmetricGeneratingSet_presentedLetters R
  have hH4 := bowditchH4_of_linearStokes hS (linearStokes_presentedLetters hL hiso)
  exact Hyperbolic.isHyperbolicGroup_of_isSlimTriangles hS
    (isSlimTriangles_of_bowditchH4 hS (Nat.succ_pos _) hH4)

end DiscreteStokes
end GroupApproximation

#audit_axioms GroupApproximation.DiscreteStokes.isSymmetricGeneratingSet_presentedLetters
#audit_axioms GroupApproximation.DiscreteStokes.wordSum_trueLetters_map
#audit_axioms GroupApproximation.DiscreteStokes.linearStokes_presentedLetters
#audit_axioms GroupApproximation.DiscreteStokes.isHyperbolicGroup_presentedGroup_of_linearIsoperimetric
