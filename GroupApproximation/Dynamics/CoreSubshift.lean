import GroupApproximation.Dynamics.RetainedSubshift
import GroupApproximation.Dynamics.SubshiftLanguageStabilization
import GroupApproximation.Meta.AxiomGuard

/-!
# The symbolic core `Y_0`

sec:chain-core, proof of lem:chain-core-models.  "Put `Y_0 = ⋂_r Z_r`."  "All its words belong to
`X`, so `Y_0 ⊆ X`."  "At each fixed length the decreasing finite languages of `Z_r` stabilize to the
language of `Y_0`."  "It is precisely the set of points all of whose finite words give cyclic edges
in the word graphs of `X`."

## Main results
* `coreSubshift X`: the set `Y_0`.
* `mem_coreSubshift_iff`: `Y_0` is the set of points all of whose words give cyclic edges.
* `isClosed_coreSubshift`, `mapsTo_shift_coreSubshift`: `Y_0` is a subshift.
* `coreSubshift_subset`: `Y_0 ⊆ X`.
* `exists_language_retainedSubshift_eq`: the languages of `Z_r` stabilize to the language of `Y_0`.
-/

namespace GroupApproximation.ChainCore

open Set SymbolicDynamics.FullShift GroupApproximation.WordGraph

variable {A : Type*}

/-- sec:chain-core: the symbolic core `Y_0 = ⋂ r, Z_r`. -/
def coreSubshift (X : Set (ℤ → A)) : Set (ℤ → A) :=
  ⋂ r, retainedSubshift X r

/-- sec:chain-core: `Y_0` is precisely the set of points all of whose finite words give cyclic edges
in the word graphs of `X`. -/
theorem mem_coreSubshift_iff {X : Set (ℤ → A)} {x : ℤ → A} :
    x ∈ coreSubshift X ↔ ∀ (r : ℕ) (i : ℤ), IsCyclicEdge X r (word x i (r + 1)) := by
  simp only [coreSubshift, retainedSubshift, mem_iInter, mem_setOf_eq]

theorem coreSubshift_subset_retainedSubshift (X : Set (ℤ → A)) (r : ℕ) :
    coreSubshift X ⊆ retainedSubshift X r :=
  iInter_subset _ r

theorem isClosed_coreSubshift [TopologicalSpace A] [DiscreteTopology A] (X : Set (ℤ → A)) :
    IsClosed (coreSubshift X) :=
  isClosed_iInter fun r => isClosed_retainedSubshift X r

theorem mapsTo_shift_coreSubshift (X : Set (ℤ → A)) (n : ℤ) :
    MapsTo (shift n) (coreSubshift X) (coreSubshift X) := by
  intro x hx
  simp only [coreSubshift, mem_iInter] at hx ⊢
  exact fun r => mapsTo_shift_retainedSubshift X r n (hx r)

/-- sec:chain-core: all words of `Y_0` belong to `X`, so `Y_0 ⊆ X`. -/
theorem coreSubshift_subset [TopologicalSpace A] {X : Set (ℤ → A)} (hXc : IsClosed X)
    (hX : ∀ n : ℤ, MapsTo (shift n) X X) : coreSubshift X ⊆ X := by
  intro x hx
  rw [mem_coreSubshift_iff] at hx
  refine mem_of_forall_finset_agree hXc fun U => ?_
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ i ∈ U, i.natAbs ≤ N :=
    ⟨U.sup Int.natAbs, fun i hi => Finset.le_sup hi⟩
  obtain ⟨y, hy, hyx⟩ := exists_realize_of_word_mem_language hX (hx (2 * N) (-(N : ℤ))).1
  refine ⟨y, hy, fun i hi => ?_⟩
  have hiN := hN i hi
  obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ i + N by omega)
  have h := hyx j (by omega)
  rwa [show -(N : ℤ) + (j : ℤ) = i by omega] at h

theorem language_eq_image (X : Set (ℤ → A)) (n : ℕ) :
    language X n = (fun x : ℤ → A => word x 0 n) '' X :=
  rfl

/-- sec:chain-core: at each fixed length the decreasing finite languages of `Z_r` stabilize to the
language of `Y_0`. -/
theorem exists_language_retainedSubshift_eq [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    (X : Set (ℤ → A)) (n : ℕ) :
    ∃ R, ∀ r, R ≤ r → language (retainedSubshift X r) n = language (coreSubshift X) n := by
  simp only [language_eq_image, coreSubshift]
  exact exists_image_eq_image_iInter_of_antitone (continuous_pi fun _ => continuous_apply _)
    (retainedSubshift_antitone X) (isClosed_retainedSubshift X)

#audit_axioms mem_coreSubshift_iff
#audit_axioms isClosed_coreSubshift
#audit_axioms mapsTo_shift_coreSubshift
#audit_axioms coreSubshift_subset
#audit_axioms exists_language_retainedSubshift_eq

end GroupApproximation.ChainCore
