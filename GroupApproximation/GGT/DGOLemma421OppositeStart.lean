import GroupApproximation.GGT.DGOLemma421Proof

/-!
# Moving an opposite-side match to its component start

The finite-absorption output in the DGO quadrilateral records the coset factor
at the end of the opposite component.  Since a component span lies in the
same peripheral subgroup, multiplying by the inverse span moves that identity
to the component start.  This is the algebraic bridge needed by the corrected
start-coset form of Lemma 4.21(b).
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- An opposite-side end match yields a start match in the same peripheral
coset. -/
theorem exists_start_coset_of_opposite_end_match
    (D : RelGenSet G Λ) {lam : Λ}
    {word : List (RelLetter G Λ)}
    (hlet : ∀ a ∈ word, D.IsLetter a)
    {A : G} {i j : ℕ}
    (hcomp : IsComp lam word i j)
    (h : G) (hh : h ∈ D.fam lam)
    (heq : A * h = vertex (1 : G) word j) :
    ∃ h' : G, h' ∈ D.fam lam ∧
      A * h' = vertex (1 : G) word i := by
  let span : G :=
    (vertex (1 : G) word i)⁻¹ * vertex (1 : G) word j
  have hspan : span ∈ D.fam lam := by
    exact span_mem_fam_of_isComp D 1 hlet hcomp
  refine ⟨h * span⁻¹, mul_mem hh (inv_mem hspan), ?_⟩
  calc
    A * (h * span⁻¹) = (A * h) * span⁻¹ := by rw [mul_assoc]
    _ = vertex (1 : G) word j * span⁻¹ := by rw [heq]
    _ = vertex (1 : G) word i := by
      dsimp [span]
      group

end OsinComponents
end GGT
end GroupApproximation
