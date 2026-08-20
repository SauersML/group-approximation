# KK-theory, the UCT, Dadarlat–Eilers, order-zero maps and the Kirchberg–Rørdam
# corona — and Tikuisis–White–Winter over them

**Authored 2026-08-19. UNCOMPILED and UNWIRED.** Thirteen new modules under
`GroupApproximation/Analysis/`, none imported from `GroupApproximation.lean`;
see "Before anything is graded".

## The ask, and what it turned into

*Formalize unconditionally KK-theory, the UCT, Dadarlat–Eilers, order-zero maps
and the Kirchberg–Rørdam corona theory, then Tikuisis–White–Winter.*

Two of those five are constructible here and are **constructed and proved**;
two are constructible in part; one is not constructible at all, and neither is
TWW. The wave draws that line explicitly rather than blurring it, and it moves
the line in one place that matters: **the UCT is no longer an uninterpreted
parameter of this development — it is a definition.**

| target | status |
|---|---|
| order-zero maps | **proved**: definition, `⋆`-hom case, composition stability, `⋆`-preservation, the supported (`h·π`) picture with complete positivity in full, the cone deformation |
| Kirchberg–Rørdam corona | **proved**: Kirchberg's `ε`-test in full; countable saturation of `ℓ∞(Mₖ)/c₀`; corona-multiplicativity ⇒ asymptotic multiplicativity |
| KK-theory | **axiomatized** (`KasparovTheory`), with every downstream consequence proved from the axioms; no inhabitant, and none possible without Hilbert C⋆-modules |
| the UCT | **defined** (`SatisfiesUCT` = KK-equivalence to a commutative algebra, Rosenberg–Schochet's characterization), with the closure theorems proved |
| Dadarlat–Eilers | **statement** typed over `KasparovTheory`; the direct-sum machinery it is stated over is proved |
| TWW | **derived**, not assumed: `TikuisisWhiteWinterTheorem` is produced from finer inputs in two independent ways, and its last step (corona ⇒ quasidiagonal trace) is proved outright |

## The modules

Layered, each importing only the ones above it.

1. `Analysis/CStarCPStarTarget.lean` — the three `⋆`-preservation lemmas for
   completely positive maps, ported from a `B(H)` target to an arbitrary
   C⋆-target. The originals are pinned by signature, so they are re-proved
   rather than widened.
2. `Analysis/CStarOrderZero.lean` — `IsPositiveElem` (order-instance-free, as
   in `CStarExactness`), `IsOrthogonalityPreserving`, `IsOrderZero`.
   `⋆`-homomorphisms are order zero; order zero survives composition with a
   `⋆`-homomorphism on either side; order-zero maps are `⋆`-preserving, so the
   orthogonality clause is symmetric although it is not stated symmetrically.
3. `Analysis/CStarOrderZeroSupport.lean` — `OrderZeroSupport`, the map
   `a ↦ root² · π a`, and the **constructive half of Winter–Zacharias**:
   the product formula `φa·φb = root⁴·π(ab)`, complete positivity (witness
   `Pᵢⱼ = root · π Nᵢⱼ`, computed entrywise), contractivity, and the cone
   deformation `root ↦ t·root` from `φ` to `0`.
   *Presenting the square root rather than `h` is load-bearing*: splitting `h`
   across the two factors of `star P * P` is what makes complete positivity
   provable without a functional-calculus square root, which would drag in an
   order instance this development does not carry.
4. `Analysis/KirchbergRordamEpsilonTest.lean` — **Kirchberg's `ε`-test**
   (Kirchberg–Rørdam 2014, Lemma 3.1), proved: block bounds (`stepBound`),
   collection of finitely many `∀ᶠ` conditions, and the diagonal.
5. `Analysis/KirchbergRordamCorona.lean` — the `ε`-test at the matrix corona:
   vanishing in the corona is vanishing in the limit; **countable saturation**
   (finitely-many-at-a-time approximate solvability ⇒ simultaneous exact
   solvability); and the two directions in which a corona identity is read
   back on representing sequences.
6. `Analysis/KirchbergRordamOrderZeroLift.lean` — the two order-zero
   **inputs**: Winter–Zacharias' structure theorem (stated with an ambient
   algebra, because the supporting `⋆`-homomorphism lands in a multiplier
   algebra and *not* in the target) and KR's order-zero lifting, stated **only
   for the matrix corona**.
7. `Analysis/KKTheoryKasparov.lean` — `SepCStarAlgebra`, `Homotopic`,
   `KasparovTheory`. Proved from the axioms: KK-equivalence is reflexive,
   symmetric, transitive; mutually inverse `⋆`-homomorphisms give a
   KK-equivalence; **homotopy equivalent algebras are KK-equivalent**.
8. `Analysis/KKTheoryKGroups.lean` — `KZero T A := KK(ℂ, A)`, the comparison
   map `gamma` as an `AddMonoidHom`, its functoriality, and **KK-equivalent
   algebras have isomorphic K-theory**.
9. `Analysis/UniversalCoefficientTheorem.lean` — `SatisfiesUCT`; commutative
   algebras satisfy it; it is closed under KK-equivalence, isomorphism and
   homotopy equivalence; `ℂ` satisfies it; a UCT algebra has the K-theory of a
   commutative algebra. Rosenberg–Schochet's *sequence* form is stated as an
   input in the one degree that is expressible, and **nothing consumes it**.
10. `Analysis/DadarlatEilers.lean` — `Amplifier` and `oplus`, with
    multiplicativity, unitality, `⋆`-preservation, additivity, linearity, the
    algebra-map clause and orthogonality preservation all proved; then
    `DadarlatEilersInput`.
11. `Analysis/TikuisisWhiteWinterProof.lean` — `TikuisisWhiteWinterTheorem` at
    the defined UCT, the proof that it implies
    `QuasidiagonalMF.TikuisisWhiteWinterInput (uctPredicate T)`, and the group
    route re-proved with Tu's theorem as an obligation about a *bundled
    algebra* rather than about an abstract predicate.
12. `Analysis/QuasidiagonalCoronaCriterion.lean` — `CoronaModel`, and
    **proved**: a unital c.p. family whose induced map into `ℓ∞/c₀` is
    multiplicative *on the nose*, with converging normalized traces, is a
    `QuasidiagonalTraceModel`. This is the last step of the Annals argument,
    and it is where `tendsto_norm_sub_mul_of_corona_mul` is spent.
13. `Analysis/TikuisisWhiteWinterDerivation.lean` — **`TikuisisWhiteWinterTheorem`
    is no longer assumed.** It is derived twice: from `CoronaEmbeddingInput`
    (the Annals argument in the corona form it is *proved* in, with the
    translation back to asymptotic language supplied by 12), and from
    `NuclearAmenableTraceInput` + `TikuisisWhiteWinterCoreInput` (Connes–
    Haagerup plus the local amenable-trace form, through the diagonal argument
    already proved in `QuasidiagonalTraceLocal`). Group endpoints re-derived
    with no TWW binder and with the ucp binder discharged by
    `Quasidiagonal.ucpContractive`.

    The two UCT predicates are **not** interchangeable: `uctPredicate` is
    universal over C⋆-structures because it must be *produced* to feed the old
    input; `uctExists` is existential because it must be *consumed* from a core
    input. Each is used in exactly one direction.

## The one real gain, stated precisely

`Analysis/TikuisisWhiteWinter.lean` says, in its own docstring, that the UCT
"enters as a predicate parameter `UCT`, exactly as `NuclearReduced` does",
and that "no honest definition can be given here". A `UCT : Type u → Prop`
appearing exactly twice — once as a hypothesis of the TWW input, once as the
conclusion of the Tu input — is **unfalsifiable bookkeeping**: the pair of
statements is satisfied by the constantly-true predicate, so the composite
theorem asserts nothing about the UCT at all.

After this wave the same route runs with `SatisfiesUCT`, which is a definition
with proved content (closure under KK-equivalence, `ℂ` in the class, K-theory
transported). The composite is still conditional on TWW — nothing here proves
TWW — but the *hypothesis* is now a specific mathematical statement instead of
a free variable.

## What is irreducible, and where it now sits

After the derivation wave, what is finally assumed is: the Annals argument in
**one of two finer forms** — `CoronaEmbeddingInput`, or
`NuclearAmenableTraceInput` + `TikuisisWhiteWinterCoreInput` — plus
`KasparovTheory` (Kasparov), Lance and Tu. `TikuisisWhiteWinterTheorem` itself
is derived, not postulated.

Three further inputs are stated and **consumed by nothing**:
`DadarlatEilersInput` (Dadarlat–Eilers 2002), `WinterZachariasInput`
(Winter–Zacharias 2009), `CoronaOrderZeroLiftInput` (Kirchberg–Rørdam 2014).
They are what a proof of the remaining Annals input would consume. They are stated because they are what a proof of TWW would consume,
which is what makes "the irreducibility is here" a checkable claim rather than
a rhetorical one.

Against them, what this development now proves unconditionally and would
supply to such a proof: countable saturation of the corona; the supported
picture of order-zero maps; the KK-consequences of the Kasparov axioms; the
direct-sum machinery of stable uniqueness; and the local-to-global step
already in `Analysis/QuasidiagonalTraceLocal.lean`.

## Design decisions that must not be "simplified" away

* **Positivity is spelled `∃ x, a = star x * x`**, never `0 ≤ a`, throughout
  the order-zero layer — matching `CStarExactness.IsCompletelyPositive`,
  because the concrete algebras here are `StarSubalgebra`s of `B(H)` and carry
  no `PartialOrder`.
* **`OrderZeroSupport` carries the square root, not the support.** See 3.
* **The KR lifting input is stated for the matrix corona only.** Order-zero
  maps do not lift along an arbitrary surjection; an input asserting that they
  do would be *false*, and would make everything downstream vacuous rather
  than conditional.
* **`IsBilinear` is a predicate, not a field of `KasparovTheory`.** A field
  would have to be stated before the group-structure field is available as an
  instance. It is assumed only by the two K-theoretic theorems that need it.
* **`uctPredicate` quantifies over the C⋆-structures a type may carry.** A
  `Type u → Prop` cannot see a structure; the universal form is the one that
  makes `TikuisisWhiteWinterInput` *easier* to produce, which is the direction
  needed. The group route avoids the type-level predicate entirely.
* **No conclusion has an input structure as its head.** Every endpoint is
  `IsQuasidiagonalTrace` or `IsOperatorMF`, group by group — the discharge
  fixpoint of `scripts/check_non_mf_unconditional.py` must not swallow these.

## Before anything is graded

None of these modules has been compiled: the session that wrote them was
instructed not to build. They are **not** imported from
`GroupApproximation.lean`, deliberately — wiring an uncompiled module into the
root breaks the build for every concurrent session.

First-build repair list, in suspicion order:

1. `CStarOrderZeroSupport.star_choiWitness_mul_choiWitness_apply` — the long
   `rw` chain through `star_mul`/`← map_star`/`hom_mul_root_mul`; the
   orientation of `← map_star` and the first match of each `mul_assoc` are the
   likely failures.
2. `KirchbergRordamEpsilonTest.epsilon_test` — `Nat.find_min` with `m := j-1`,
   and whether `set j := Nat.find (hex n)` leaves `omega` able to see
   `hjdef`.
3. `KirchbergRordamCorona.ofContractionSeq` — whether `⟨f, hf⟩` is accepted
   for `lp _ ∞` and whether `memℓp_infty_iff` is the current spelling
   (`Sofic/MFTraceCoronaBridge.lean:194` uses it, so it should be).
4. `KKTheoryKGroups` — `AddMonoidHom.mk'` (no precedent in this repository),
   and the `AddEquiv` structure-instance field names.
5. `TikuisisWhiteWinterProof.tikuisisWhiteWinterInput_of_theorem` — the defeq
   between the instance found for the anonymous `CStarAlgebra A` binder and
   `SepCStarAlgebra.algebra ⟨A, instA, hsep⟩`.
6. `QuasidiagonalCoronaCriterion.CoronaModel` — whether the instance parameter
   `[∀ n, Nonempty (space n)]` is enough for the corona's C⋆-structure to
   elaborate in the `corona_mul` field type, and whether `Matrix ↥(space n) …`
   and `(fun n => (space n).carrier)` stay defeq through `seq_apply`.
7. `KirchbergRordamOrderZeroLift.CoronaOrderZeroLiftInput` — the C⋆-instances
   on `BoundedMatrixSequence`/`NormMatrixCStarCorona` are passed as explicit
   anonymous binders precisely so that a missing global instance is not a
   failure; if it fails it is the binder order.

`grep` for `sorry` returns nothing, and that proves nothing — see
`authoring-lean-without-a-compiler`.
