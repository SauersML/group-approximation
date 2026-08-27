import GroupApproximation.Analysis.CStarSeminormCompletion
import GroupApproximation.Analysis.CStarNormFromRepresentation
import GroupApproximation.Analysis.MaximalCStarAnyUniverse

/-!
# `Cmax(H)` has its universal property for a target in **every** universe

Proof-ledger rows `MC.02`, `PRE.19` and `PA.12`.  `prop:maximal-cstar` of
`non_mf_groups_exist.tex` reads

> The canonical map `h ↦ u_h` is injective, and for every unital C*-algebra `B`
> and every homomorphism `ρ : H → U(B)`, there is a unique unital
> *-homomorphism `Cmax(H) → B` with `u_h ↦ ρ(h)` for every `h ∈ H`.

with no qualification on `B` — an earlier revision restricted it to a universe
containing `H`, and that clause has been deleted.

`Analysis/MaximalGroupCStar.manuscriptUniverseRelativeMaximalGroupCStar`
quantifies over `B : Type u` at the universe of `H`, and so under-certifies the
print.  `Analysis/MaximalCStarAnyUniverse` closed the *uniqueness* half at every
universe outright, and closed existence at every universe under the hypothesis
that `ρ` factors through a C*-algebra at the universe of `H`.  This file
discharges that hypothesis for **every** `ρ`, so
`manuscriptMaximalGroupCStarUniversalProperty` below is the printed proposition
with the universes of `H` and `B` independent.

## How the universe of `B` is erased

The obstruction was that `Cmax(G)` is a bounded product indexed by
representations with carriers in one fixed universe, so a representation
somewhere else is not a coordinate.  The factorization does not try to shrink
`B`.  It goes through the **seminorm** `x ↦ ‖ρ̃(x)‖_B` that `ρ` puts on the
group ring, where `ρ̃` is the ⋆-homomorphism `GroupRingStar.unitaryLift ρ`
extending `ρ` to `ℂ[G]`.  A seminorm on `ℂ[G]` is a function `ℂ[G] → ℝ` — it
remembers nothing about where `B` lives — and `Analysis/CStarSeminormCompletion`
turns it back into a C*-algebra by killing its null ideal and completing.  Since
`ℂ[G]` lies at the universe of `G`, so does the result.

So the factoring datum is

* `B₀ = SeminormCompletion (repSeminorm ρ)`, at the universe of `G`;
* `ρ₀ : G → U(B₀)`, the images of the group elements, unitary because the
  group elements are unitary in `ℂ[G]` and every arrow of the route is a
  ⋆-homomorphism;
* `j : B₀ → B`, the extension of `ρ̃` across the completion, which exists
  because `ρ̃` is *isometric* for this seminorm by construction.

Nothing about `B` is used except that it is a C*-algebra.  This is the route
that `Analysis/CStarNormFromRepresentation` and `Analysis/CStarCompletionHom`
were written for, and their docstrings name it.

## What this does not settle

That the Lean `MaximalGroupCStar` is the *printed* object — the completion of
`ℂ[H]` in the supremum of the norms of its unitary representations — is a
separate statement, proved in `Analysis/MaximalCStarPrintedCompletion` by
building that completion and exhibiting a ⋆-isomorphism.  What is settled here
is that the Lean object satisfies the printed universal property verbatim,
which is what every consumer of `prop:maximal-cstar` uses.
-/

namespace GroupApproximation

open scoped CStarAlgebra
open CStarTensor CStarRepresentationNorm

noncomputable section

universe u v

/-! ## From a ⋆-homomorphism on the group ring to a unitary representation -/

/-- **A ⋆-homomorphism out of the group ring restricts to a unitary
representation of the group.**  The group elements are unitary in `ℂ[G]` and a
⋆-homomorphism preserves unitarity, so the only content is that the restriction
is multiplicative, which is `single g 1 * single h 1 = single (gh) 1`. -/
def unitaryHomOfStarAlgHom {G : Type u} [Group G] {C : Type v} [Ring C]
    [StarRing C] [Algebra ℂ C] (iota : MonoidAlgebra ℂ G →⋆ₐ[ℂ] C) :
    G →* unitary C where
  toFun g := ⟨iota (MonoidAlgebra.single g (1 : ℂ)),
    map_mem_unitary iota (single_mem_unitary g)⟩
  map_one' := by
    apply Subtype.ext
    show iota (MonoidAlgebra.single (1 : G) (1 : ℂ)) = 1
    rw [← MonoidAlgebra.one_def, map_one]
  map_mul' g h := by
    apply Subtype.ext
    show iota (MonoidAlgebra.single (g * h) (1 : ℂ))
      = iota (MonoidAlgebra.single g (1 : ℂ)) * iota (MonoidAlgebra.single h (1 : ℂ))
    rw [← map_mul, MonoidAlgebra.single_mul_single, one_mul]

@[simp] theorem unitaryHomOfStarAlgHom_apply {G : Type u} [Group G] {C : Type v}
    [Ring C] [StarRing C] [Algebra ℂ C] (iota : MonoidAlgebra ℂ G →⋆ₐ[ℂ] C)
    (g : G) :
    (unitaryHomOfStarAlgHom iota g : C) = iota (MonoidAlgebra.single g (1 : ℂ)) :=
  rfl

/-! ## The C⋆-algebra at the universe of `G` that a representation factors
through -/

section Factorization

variable {G : Type u} [Group G] {B : Type v} [CStarAlgebra B]

/-- **The envelope of a unitary representation**: the group ring, normed by
`‖ρ̃(·)‖_B` and completed.  It lies at the universe of `G` however large the
universe of `B` is, because `ℂ[G]` does. -/
abbrev representationEnvelope (rho : G →* unitary B) : Type u :=
  SeminormCompletion (isCStarSeminorm_repSeminorm rho)

/-- The canonical unitary representation of `G` in its envelope. -/
def envelopeUnitaryHom (rho : G →* unitary B) :
    G →* unitary (representationEnvelope rho) :=
  unitaryHomOfStarAlgHom (toSeminormCompletion (isCStarSeminorm_repSeminorm rho))

/-- **The factoring ⋆-homomorphism `envelope → B`.**  The norm of the envelope
is by construction the norm of the image in `B`, so `ρ̃` is isometric for it and
the extension across the completion needs no estimate. -/
def envelopeFactor (rho : G →* unitary B) :
    representationEnvelope rho →⋆ₐ[ℂ] B :=
  seminormCompletionLift (isCStarSeminorm_repSeminorm rho)
    (GroupRingStar.unitaryLift (R := ℂ) rho) fun _ ↦ le_rfl

/-- The factorization is a factorization: it carries the canonical unitaries to
the values of `ρ`. -/
theorem envelopeFactor_unitary (rho : G →* unitary B) (g : G) :
    envelopeFactor rho (envelopeUnitaryHom rho g : representationEnvelope rho)
      = (rho g : B) := by
  have hlift := seminormCompletionLift_apply (isCStarSeminorm_repSeminorm rho)
    (GroupRingStar.unitaryLift (R := ℂ) rho) (fun _ ↦ le_rfl)
    (MonoidAlgebra.single g (1 : ℂ))
  rw [GroupRingStar.unitaryLift_single, one_smul] at hlift
  exact hlift

end Factorization

/-! ## The universal property, unrestricted -/

/-- **The universal property of `Cmax(G)` for a target in an arbitrary
universe.**  Every unitary representation of `G` on a C*-algebra `B` — with the
universe of `B` unrelated to that of `G` — extends uniquely across the canonical
generators.

Existence is the factorization of this file fed to
`maximalGroupCStar_existsUnique_lift_of_factors`; uniqueness is
`maximalGroupCStar_lift_unique`, which never needed a hypothesis. -/
theorem maximalGroupCStar_existsUnique_lift_allUniverses (G : Type u) [Group G]
    {B : Type v} [CStarAlgebra B] (rho : G →* unitary B) :
    ∃! f : MaximalGroupCStar G →⋆ₐ[ℂ] B,
      ∀ g : G, f (maximalGroupCStarGenerator G g) = (rho g : B) :=
  maximalGroupCStar_existsUnique_lift_of_factors G rho (envelopeUnitaryHom rho)
    (envelopeFactor rho) (envelopeFactor_unitary rho)

/-- **`prop:maximal-cstar`, verbatim.**

* the canonical map `h ↦ u_h` is injective;
* for **every** unital C*-algebra `B`, in **every** universe, and every
  `ρ : G → U(B)`, there is a unique unital ⋆-homomorphism `Cmax(G) → B`
  carrying `u_g` to `ρ(g)`.

The universes `u` of the group and `v` of the target are independent variables,
which is what distinguishes this from
`manuscriptUniverseRelativeMaximalGroupCStar`, and it is the whole content of
proof-ledger row `MC.02`. -/
theorem manuscriptMaximalGroupCStarUniversalProperty :
    ∀ (G : Type u) [Group G],
      Function.Injective (maximalGroupCStarUnitaryHom G) ∧
        ∀ (B : Type v) [CStarAlgebra B] (rho : G →* unitary B),
          ∃! f : MaximalGroupCStar G →⋆ₐ[ℂ] B,
            ∀ g : G,
              f (maximalGroupCStarGenerator G g) = (rho g : B) := by
  intro G _
  exact ⟨maximalGroupCStarUnitaryHom_injective G,
    fun _ _ rho ↦ maximalGroupCStar_existsUnique_lift_allUniverses G rho⟩

end

end GroupApproximation
