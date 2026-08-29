import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# A Hilbert space with a countable total family has a `Type 0` Hilbert basis

Mathlib's `exists_hilbertBasis` produces a Hilbert basis indexed by a *subset of
the space*, so for `E : Type u` the index lives in `Type u`.  That is useless for
a universe descent, which is the only reason this module exists: the GNS sum of a
separable C-star algebra lives in the algebra's universe, and the amalgam
machinery it has to feed wants a Hilbert space in `Type 0`.

Mathlib has no separable-Hilbert-space theory to appeal to — `SeparableSpace`
does not occur anywhere in `Mathlib/Analysis/InnerProductSpace/` at the pinned
revision — but it does have Gram--Schmidt, and Gram--Schmidt indexed by `ℕ`
gives an index in `Type 0` for free.  The input is a *sequence* `f : ℕ → E`
whose span has trivial orthogonal complement; no linear independence is asked
for, which matters because the sequences that arise are enumerations of dense
sets and are wildly dependent.  Gram--Schmidt then returns zero at the redundant
indices, and `gramSchmidtNormed_orthonormal'` is already stated on the subtype
of indices where it does not, which is exactly the subtype needed:

    `{i : ℕ | gramSchmidtNormed ℂ f i ≠ 0} : Type` .

`countableGramSchmidtBasis` assembles that into a `HilbertBasis` over that
subtype, and `HilbertBasis.repr` then presents `E` as `ℓ²` over it — a space in
`Type 0` whatever universe `E` came from.

The one step not already in Mathlib is that dropping the zero vectors does not
change the span, `span_gramSchmidtNormed_nonzero` below; with it the hypothesis
travels along `span_gramSchmidtNormed_range` and `span_gramSchmidt` to the span
of the original sequence.
-/

namespace GroupApproximation
namespace CStarHilbertCountableBasis

open Submodule
open InnerProductSpace

open scoped InnerProductSpace

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Dropping the vectors Gram--Schmidt kills does not change the span.**  The
discarded vectors are zero, and zero is in every submodule. -/
theorem span_gramSchmidtNormed_nonzero (f : ℕ → E) :
    span ℂ (Set.range fun i : {i : ℕ | gramSchmidtNormed ℂ f i ≠ 0} ↦
        gramSchmidtNormed ℂ f i)
      = span ℂ (Set.range (gramSchmidtNormed ℂ f)) := by
  refine le_antisymm (span_mono ?_) (span_le.2 ?_)
  · rintro _ ⟨i, rfl⟩
    exact ⟨i.1, rfl⟩
  · rintro _ ⟨i, rfl⟩
    by_cases h : gramSchmidtNormed ℂ f i = 0
    · rw [h]
      exact zero_mem _
    · exact subset_span ⟨⟨i, h⟩, rfl⟩

variable [CompleteSpace E]

/-- **A countable total sequence yields a Hilbert basis indexed in `Type 0`.**
No linear independence is required of `f`: Gram--Schmidt returns zero at the
redundant indices and those are discarded, which is what makes this usable on an
enumeration of a dense set. -/
def countableGramSchmidtBasis (f : ℕ → E)
    (hf : (span ℂ (Set.range f))ᗮ = ⊥) :
    HilbertBasis {i : ℕ | gramSchmidtNormed ℂ f i ≠ 0} ℂ E :=
  HilbertBasis.mkOfOrthogonalEqBot (gramSchmidtNormed_orthonormal' f) <| by
    rw [span_gramSchmidtNormed_nonzero, span_gramSchmidtNormed_range,
      span_gramSchmidt]
    exact hf

/-- **The descent.**  A Hilbert space carrying a countable total sequence is
isometrically isomorphic to `ℓ²` over a subtype of `ℕ`, and that target lives in
`Type 0` however large the universe of `E` is.

This is the statement the universe descent needs; the index is exposed so that a
consumer can see it is small. -/
theorem exists_typeZero_linearIsometryEquiv (f : ℕ → E)
    (hf : (span ℂ (Set.range f))ᗮ = ⊥) :
    ∃ ι : Type, Nonempty (E ≃ₗᵢ[ℂ] lp (fun _ : ι ↦ ℂ) 2) :=
  ⟨{i : ℕ | gramSchmidtNormed ℂ f i ≠ 0},
    ⟨(countableGramSchmidtBasis f hf).repr⟩⟩

omit [CompleteSpace E] in
/-- **Triviality of the orthogonal complement from a spanning family**, in the
form the C-star side produces it: it is enough that every vector orthogonal to
each `f n` is zero. -/
theorem orthogonal_span_eq_bot_of_forall (f : ℕ → E)
    (h : ∀ x : E, (∀ n, ⟪f n, x⟫_ℂ = 0) → x = 0) :
    (span ℂ (Set.range f))ᗮ = ⊥ := by
  refine eq_bot_iff.2 fun x hx ↦ Submodule.mem_bot ℂ |>.2 (h x fun n ↦ ?_)
  exact (Submodule.mem_orthogonal _ x).mp hx (f n) (subset_span ⟨n, rfl⟩)

end

end CStarHilbertCountableBasis
end GroupApproximation
