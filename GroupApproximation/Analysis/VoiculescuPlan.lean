import GroupApproximation.Analysis.CalkinCStarAlgebra

/-!
# Voiculescu's theorem: the plan, and its first leaf

LITERATURE INPUT: K. R. Davidson, *C\*-algebras by Example*, Fields Institute
Monographs 6, §II.5 (Arveson's quasicentral approximate units, Glimm's lemma,
Voiculescu's theorem); D. Voiculescu, *A non-commutative Weyl--von Neumann
theorem*, Rev. Roumaine Math. Pures Appl. 21 (1976).

Voiculescu's theorem is the bottom of the `conjugateWordNorming` debt.  Every
other ingredient of Shulman's Theorem 16 is now in the repository or reduced to
a named statement:

* Theorem 4, in the direction Theorem 10 ends with —
  `Analysis/StarStrongLimitNorm.isMFAlgebra_of_starStrongLift`;
* the Calkin algebra as a C\*-algebra — `Analysis/CalkinCStarAlgebra`;
* Stinespring's dilation theorem — `Analysis/CStarStinespringHom`;
* Arveson's extension theorem at a `B(H)` target — `Analysis/ArvesonBHTarget`,
  modulo its one named limit step.

This module records what a Voiculescu lane has to build, in the order it has to
build it, and carries the first leaf as a named statement.  Nothing here is
cited by anything: it is a work order.

## The endpoint

The lane's endpoint is *not* a new statement.  It is
`ShulmanSymmetricDouble.CompatibleTargetPairStatement`, already in the tree:
from faithful `α : A → D` and `β : B → D` agreeing on `γ : C → D`, produce a
compatible pair `(σ_A, σ_B)` of representations of `D` whose induced map on the
symmetric double detects the amalgam.  Enders--Shulman build that pair as

    `γ = (q ∘ Ad(1 ⊕ u) ∘ σ_A^{⊕∞}) * (q ∘ σ_B^{⊕∞})` ,

and `u` is exactly what Voiculescu supplies: a unitary making the two legs agree
on `C` *in the Calkin algebra*.  So the lane's job is the absorption theorem, in
the form

> **(V)** Let `A` be a separable unital C\*-algebra, `H` a separable Hilbert
> space, and `σ : A → B(H)` a unital representation with `σ(A) ∩ K(H) = 0`.
> Then for every unital representation `ρ` of `A` on a separable Hilbert space,
> `σ` and `σ ⊕ ρ` are unitarily equivalent modulo the compacts.

and its standard corollary, that any two unital faithful essential
representations of a separable unital C\*-algebra on a separable Hilbert space
have unitarily equivalent images in `Q(H)`.  That corollary is what makes
`σ_A ∘ φ_A` and `σ_B ∘ φ_B` agree on `ι_A(C)`.

## The chain, leaf by leaf

Each item is a separate module, and each is a theorem about `B(H)` and the
compacts alone — no amalgams, no coronas.

**(V1) Arveson's quasicentral approximate units.**  For a separable
C\*-subalgebra `A ⊆ B(H)`, the compacts have an approximate unit that is
asymptotically central for `A`:

```
∃ e : ℕ → (H →L[ℂ] H),
  (∀ n, IsCompactOperator (e n)) ∧ (∀ n, IsSelfAdjoint (e n)) ∧
  (∀ n, ‖e n‖ ≤ 1) ∧
  (∀ k, Tendsto (fun n ↦ ‖e n * S k - S k * e n‖) atTop (𝓝 0)) ∧
  (∀ T, IsCompactOperator T → Tendsto (fun n ↦ ‖T - e n * T‖) atTop (𝓝 0))
```

for any countable `S : ℕ → B(H)` generating `A`.  This is
`QuasicentralApproximateUnitStatement` below, the one leaf this module carries.
`Analysis/CStarIdealApproximateUnit` already builds an increasing approximate
unit for every closed star-stable two-sided ideal, and
`Analysis/CalkinCStarAlgebra` puts the compacts in that shape, so what is left is
*quasicentrality*.  Arveson's argument for it is convexity, not analysis: the
convex hull of an approximate unit still is one, the set of commutator defects
`(‖[u, S k]‖)ₖ` has `0` in its weak closure, and a convex set has the same weak
and norm closures, so `0` is in its norm closure.  The Lean inputs are
Mathlib's `Convex`, the Hahn--Banach separation already used elsewhere in this
repository (`Analysis/StateExtension`), and the existing approximate unit.

**(V2) Glimm's lemma.**  For a separable `A ⊆ B(H)` with `A ∩ K(H) = 0`, every
state of `A` is approximated by vector states at vectors orthogonal to any given
finite-dimensional subspace:

```
∀ (φ : state of A) (F : Finset A) (ε > 0) (P : finite-rank projection),
  ∃ ξ : H, ‖ξ‖ = 1 ∧ P ξ = 0 ∧ ∀ a ∈ F, ‖⟪ξ, a ξ⟫ - φ a‖ < ε
```

This is where `A ∩ K(H) = 0` is used, and it is the analytic heart: the
hypothesis says the image of `A` in the Calkin algebra is faithful, so states of
`A` are limits of vector states along vectors escaping every finite-dimensional
subspace.  Davidson proves it from (V1) plus the fact that a state of a
C\*-algebra is a weak\* limit of vector states.

**(V3) The one-step approximation.**  From (V1) and (V2): given finite `F ⊆ A`,
`ε > 0`, a finite-rank projection `P`, and a unital representation `ρ` of `A` on
a finite-dimensional space `K₀`, there is an isometry `V : K₀ → H` with

```
V* V = 1,  ‖V* σ(a) V - ρ(a)‖ < ε  for a ∈ F,  and  P V = 0 .
```

Vectors from (V2) at the states `a ↦ ⟪e_i, ρ(a) e_i⟫` give the columns of `V`;
(V1) makes the off-diagonal terms small.  This is the step where Voiculescu's
theorem is actually proved, and it is finite-dimensional.

**(V4) Assembly.**  Iterate (V3) along a dense sequence of `A` and a summable
sequence of tolerances, with mutually orthogonal ranges, and sum the isometries.
The resulting `V` intertwines `σ` and `σ ⊕ ρ` modulo compacts.  This is
bookkeeping with orthogonal families and `lp` sums, of the kind
`Analysis/ShulmanFillCoronaJoin` already does for matrix blocks.

**(V5) The Calkin corollary.**  Two unital faithful essential representations of
a separable unital C\*-algebra on a separable Hilbert space have unitarily
equivalent images in `Q(H)`: apply (V) twice and compose.  With
`Analysis/CalkinCStarAlgebra` this is now expressible.

## Order of work, and what each step costs

(V1) is convexity and can be done next; it needs no new Hilbert-space theory.
(V2) needs the weak\* approximation of states by vector states, which the
repository has for the GNS construction (`Analysis/CStarStateGNS`) but not in
this form.  (V3) and (V4) are the bulk.  (V5) is a corollary.

An honest estimate: (V1) is one module, (V2) two, (V3) and (V4) together the
largest single piece in this lane, and none of it can be checked until builds
resume.

This module is in the root import list.  It was authored while builds were
suspended and has not been elaborated.
-/

namespace GroupApproximation
namespace Voiculescu

open Filter Topology

noncomputable section

/-- **(V1) Arveson's quasicentral approximate unit for the compacts.**  For any
countable family `S` of operators — in the application, a family generating a
separable subalgebra — the compacts have a self-adjoint contractive approximate
unit whose commutators with every `S k` vanish asymptotically.

This is the first leaf of the Voiculescu lane, and the only one this module
carries.  Its proof is Arveson's convexity argument, not an analytic estimate:
the convex hull of an approximate unit is one, and a convex set has the same
weak and norm closures. -/
def QuasicentralApproximateUnitStatement : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : ℕ → (H →L[ℂ] H)),
      ∃ e : ℕ → (H →L[ℂ] H),
        (∀ n, IsCompactOperator (e n)) ∧
        (∀ n, IsSelfAdjoint (e n)) ∧
        (∀ n, ‖e n‖ ≤ 1) ∧
        (∀ k, Tendsto (fun n ↦ ‖e n * S k - S k * e n‖) atTop (𝓝 0)) ∧
        (∀ T : H →L[ℂ] H, IsCompactOperator T →
          Tendsto (fun n ↦ ‖T - e n * T‖) atTop (𝓝 0))

end

end Voiculescu
end GroupApproximation
