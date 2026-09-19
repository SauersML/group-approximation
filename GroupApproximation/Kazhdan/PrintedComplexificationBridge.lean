import GroupApproximation.Kazhdan.KazhdanComplex

/-!
# The printed complexification step of `prop:literal-base-T`

After the editorial pass of 2026-08-16 the manuscript's proof of
`\begin{proposition}\label{prop:literal-base-T}` is two sentences, of which the
second is the only one with mathematical content:

> For an orthogonal representation `ρ` on a real Hilbert space `H_ℝ`, the
> complexification `H_ℝ ⊗_ℝ ℂ` carries the unitary representation `ρ⊗1`, whose
> invariant vectors and displacement norms are those of `ρ` in each of the two
> real coordinates; a Kazhdan pair for the unitary formulation is therefore one
> for the orthogonal formulation.

The final clause is `IsKazhdanPairComplex.toReal`, at the same control set and
the same tolerance.  The two clauses that justify it — *invariant vectors* and
*displacement norms* are coordinatewise — had no declaration: `mapHom` occurs
in the corpus only inside the body of `toReal`, and only at the embedded vector
`mk x 0`, where the imaginary coordinate is zero.  The printed sentence asserts
both facts for a *general* vector of the complexification, and that is what
`mapHom_fixed_iff` and `norm_mapHom_sub_sq` state.

`printedComplexificationStep` is the sentence itself: for every orthogonal
representation on a real Hilbert space the two coordinatewise facts hold, and a
complex Kazhdan pair is a real one.

The proposition's other sentence — that property `(T)` for `ℤ³⋊SL₃(ℤ)` is
classical, with a citation — is provenance, not a Lean obligation.  The
certificate for the base remains
`LiteralBaseP13PropertyTBridge.manuscriptBaseHasKazhdanPropertyT`, which proves
both formulations intrinsically and takes no literature input.  Nothing in this
file is conditional and nothing here has a hypothesis standing in for the
citation.
-/

namespace GroupApproximation
namespace PrintedComplexificationBridge

universe u v

variable {G : Type u} [Group G]

section Coordinatewise

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **"whose invariant vectors ... are those of `ρ` in each of the two real
coordinates."**  A vector of the complexification is fixed by `ρ⊗1` at `g`
exactly when both of its real coordinates are fixed by `ρ` at `g`. -/
theorem mapHom_fixed_iff (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (g : G)
    (v : Complexification E) :
    Complexification.mapHom ρ g v = v ↔
      ρ g v.re = v.re ∧ ρ g v.im = v.im := by
  constructor
  · intro h
    constructor
    · have hre := congrArg Complexification.re h
      simpa using hre
    · have him := congrArg Complexification.im h
      simpa using him
  · intro h
    apply Complexification.ext
    · simpa using h.1
    · simpa using h.2

/-- **"whose ... displacement norms are those of `ρ` in each of the two real
coordinates."**  The squared displacement of `v` under `ρ⊗1` splits as the sum
of the squared displacements of its two real coordinates under `ρ`. -/
theorem norm_mapHom_sub_sq (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (g : G)
    (v : Complexification E) :
    ‖Complexification.mapHom ρ g v - v‖ ^ 2
      = ‖ρ g v.re - v.re‖ ^ 2 + ‖ρ g v.im - v.im‖ ^ 2 := by
  rw [Complexification.norm_sq]
  simp only [Complexification.re_sub, Complexification.im_sub,
    Complexification.mapHom_apply, Complexification.re_mk,
    Complexification.im_mk]

end Coordinatewise

/-- **The printed complexification step, as one statement.**  Both
coordinatewise clauses, for every orthogonal representation on every real
Hilbert space of the ambient universe, together with the conclusion the
manuscript draws from them: a Kazhdan pair for the unitary formulation is a
Kazhdan pair for the orthogonal formulation, with the same control set `Q` and
the same tolerance `ε`. -/
theorem printedComplexificationStep {Q : Finset G} {ε : ℝ}
    (h : IsKazhdanPairComplex.{u, v} G Q ε) :
    (∀ (F : Type v) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
        (ρ : G →* (F ≃ₗᵢ[ℝ] F)) (g : G) (v : Complexification F),
        (Complexification.mapHom ρ g v = v ↔
            ρ g v.re = v.re ∧ ρ g v.im = v.im) ∧
          ‖Complexification.mapHom ρ g v - v‖ ^ 2
            = ‖ρ g v.re - v.re‖ ^ 2 + ‖ρ g v.im - v.im‖ ^ 2) ∧
      IsKazhdanPair.{u, v} G Q ε := by
  refine ⟨?_, h.toReal⟩
  intro F _ _ ρ g v
  exact ⟨mapHom_fixed_iff ρ g v, norm_mapHom_sub_sq ρ g v⟩

end PrintedComplexificationBridge
end GroupApproximation
