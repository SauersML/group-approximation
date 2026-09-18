import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RubinRecognitionSeparation
import GroupApproximation.Meta.AxiomGuard

/-!
# Rubin recognition, part 2: `RigidPolarRecognitionStatement` is FALSE

Census row `2e7c7d9ab149` (no tex line), lane `sk-flip-19` (Rubin route).

## LOUD CORRECTION

`RigidPolarRecognitionStatement` (RubinPolarReduce.lean) says that in `[[S]]`, for every Cantor
minimal `S`, every rigid polar is `F_O` for an open `O`.  **It is FALSE.**  So the reductions
`rigidPolarOpenTransport_of_rigidPolarRecognition`,
`rigidPolarRegularCharacterization_of_rigidPolarRecognition` and
`manuscriptSentence_flipConjugateConverse_of_rigidPolarRecognition` have a false hypothesis.
The true isolated gap is still `RigidPolarOpenTransportStatement`.

The conjugation clauses of `IsRigidPolar` only ask that `P ⊓ gPg⁻¹ ≠ ⊥`.  That holds whenever
`P` contains `F_A` for a clopen `A` that no element of `[[S]]` can move off itself.  Such an `A`
exists when `S` has two ergodic invariant measures.

### Counterexample on paper

1. Let `S` be a Cantor minimal homeomorphism with two distinct ergodic invariant measures
   `μ₁, μ₂` (non-uniquely-ergodic Cantor minimal systems exist, e.g. Toeplitz subshifts).
   Both measures are non-atomic and mutually singular.  Clopen sets generate the Borel
   σ-algebra, so there are clopen sets `A'` and `V' = A'ᶜ` with `μ₁ A' > 0.9` and
   `μ₂ V' > 0.9`.
2. Take `n = 3` and a small clopen `W₀` with `W₀, S W₀, S² W₀` pairwise disjoint and
   `μᵢ (⋃ Sⁱ W₀) < 0.1` for both measures.  Let `B = ⋃ Sⁱ W₀`, `A = A' \ B` and `V = V' \ B`.
   So `X = A ⊔ V ⊔ B`, `μ₁ A > 1/2` and `μ₂ V > 1/2`.
3. Two subgroups live on the tower `B`:
   - `Sym₃`, the tower permutations `Sⁱ w ↦ S^{σ i} w`;
   - `D`, the diagonal copy of `F_{W₀}`: `d_h (Sⁱ w) = Sⁱ (h w)`.
4. Put `P = F_A × D` and `Q = F_V × Sym₃`.  Then:
   - `C(Sym₃) = F_{A ∪ V} × D`.  A centralising element preserves each `W_i ∪ W_j`, which is
     the moved set of a transposition.  Since `n ≥ 3` it preserves each level, and commuting with
     the transpositions makes it diagonal.
   - `C(D) ∩ F_B = Sym₃`.  A centralising element `c` preserves `B = ⋃ movedSet D` and fixes the
     same points of `D`.  So it maps each fibre `{Sⁱ w}` to itself by a locally constant
     permutation `π_w`.  `π` is invariant under `F_{W₀}`, which moves points between any two
     nonempty clopen subsets of `W₀`, so `π` is constant.
   - Hence `C(Q) = F_{Vᶜ} ∩ C(Sym₃) = P` and `C(P) = F_{Aᶜ} ∩ C(D) = Q`.  `P ⊓ Q = ⊥`, because
     `D` preserves levels and `Sym₃` has no nontrivial level-preserving element.
5. Every `g ∈ [[S]]` preserves `μ₁`.  So `A ∩ gA ≠ ∅` and `F_{A ∩ gA} ≤ P ⊓ gPg⁻¹` is
   nontrivial.  In the same way `F_{V ∩ gV} ≤ Q ⊓ gQg⁻¹` via `μ₂`.
   `isRigidPolar_of_centralizer_eq_of_persistent` (below) then shows that `P` is a rigid polar.
6. `D ≤ P` moves every point of `W₀`, while `F_{W₀} ⊄ P`.  So `P` is not `F_O` for any `O`.
   Formally, `Sym₃ ≤ C(P)` overlaps `D ≤ P` on `B`, and
   `not_rigidPolarRecognition_of_centralizer_eq_of_persistent` applies.

A formal refutation needs a concrete non-uniquely-ergodic Cantor minimal system, which the corpus
does not have, and the centraliser computations of step 4.  Below, every algebraic and topological
step after that input is formal.

Candidate repair (UNVERIFIED, not authored): add the clause "for all `g`,
`P ⊓ C(P ⊓ gPg⁻¹)` is conjugate-dichotomous".  It is `Φ`-invariant, holds for `F_U` with `U`
clopen, and fails for the `P` above, because it isolates `D`.  No proof of recognition for it is
known.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

section RecognitionFalseGroup

variable {G : Type*} [Group G]

theorem rubinConjSubgroup_mono (g : G) {A B : Subgroup G} (h : A ≤ B) :
    rubinConjSubgroup g A ≤ rubinConjSubgroup g B :=
  fun _ hx => h (mem_rubinConjSubgroup.1 hx)

/-- `A ≤ P` and `A ⊓ gAg⁻¹ ≠ ⊥` give `P ⊓ gPg⁻¹ ≠ ⊥`. -/
theorem inf_rubinConjSubgroup_ne_bot_of_le {A P : Subgroup G} (hAP : A ≤ P) (g : G)
    (hA : A ⊓ rubinConjSubgroup g A ≠ ⊥) : P ⊓ rubinConjSubgroup g P ≠ ⊥ := by
  intro hbot
  apply hA
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  exact (Subgroup.eq_bot_iff_forall _).1 hbot x
    (Subgroup.mem_inf.2 ⟨hAP (Subgroup.mem_inf.1 hx).1,
      rubinConjSubgroup_mono g hAP (Subgroup.mem_inf.1 hx).2⟩)

/-- Mutually centralising subgroups with trivial meet, each containing a subgroup that meets all
of its conjugates, form a rigid polar. -/
theorem isRigidPolar_of_centralizer_eq_of_persistent {P Q A V : Subgroup G}
    (hQ : Subgroup.centralizer (P : Set G) = Q) (hP : Subgroup.centralizer (Q : Set G) = P)
    (hPQ : P ⊓ Q = ⊥) (hAP : A ≤ P) (hVQ : V ≤ Q)
    (hA : ∀ g : G, A ⊓ rubinConjSubgroup g A ≠ ⊥)
    (hV : ∀ g : G, V ⊓ rubinConjSubgroup g V ≠ ⊥) :
    IsRigidPolar P := by
  refine ⟨?_, ?_, fun g => Or.inl ?_, fun g => Or.inl ?_⟩
  · rw [hQ, hP]
  · rw [hQ]
    exact hPQ
  · exact inf_rubinConjSubgroup_ne_bot_of_le hAP g (hA g)
  · rw [hQ]
    exact inf_rubinConjSubgroup_ne_bot_of_le hVQ g (hV g)

end RecognitionFalseGroup

section RecognitionFalseTop

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [TotallyDisconnectedSpace X] [PerfectSpace X]

/-- If `O` is open and meets its translate `g O`, then `F_O ⊓ g F_O g⁻¹ ≠ ⊥`. -/
theorem rubinRigidSubgroup_inf_conj_ne_bot {T : X ≃ₜ X} (hT : IsMinimalHomeo T) {O : Set X}
    (hO : IsOpen O) (g : topologicalFullGroup T)
    (hne : (O ∩ ((g : X ≃ₜ X)⁻¹ : X ≃ₜ X) ⁻¹' O).Nonempty) :
    rubinRigidSubgroup T O ⊓ rubinConjSubgroup g (rubinRigidSubgroup T O) ≠ ⊥ := by
  rw [rubinConjSubgroup_rubinRigidSubgroup]
  intro hbot
  obtain ⟨σ, hσ, hσOW, x, hx⟩ :=
    exists_supportedIn_ne_one hT (hO.inter (hO.preimage ((g : X ≃ₜ X)⁻¹).continuous)) hne
  have hmem : (⟨σ, hσ⟩ : topologicalFullGroup T) ∈
      rubinRigidSubgroup T O ⊓ rubinRigidSubgroup T (((g : X ≃ₜ X)⁻¹ : X ≃ₜ X) ⁻¹' O) :=
    Subgroup.mem_inf.2 ⟨hσOW.mono Set.inter_subset_left, hσOW.mono Set.inter_subset_right⟩
  have h1 : (⟨σ, hσ⟩ : topologicalFullGroup T) = 1 :=
    (Subgroup.eq_bot_iff_forall _).1 hbot _ hmem
  have h2 : σ = 1 := congrArg Subtype.val h1
  rw [h2] at hx
  exact hx rfl

end RecognitionFalseTop

section RecognitionFalseSystem

variable {Y : Type} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
  [TotallyDisconnectedSpace Y] [PerfectSpace Y] [Nonempty Y] [TopologicalSpace.MetrizableSpace Y]

/-- A rigid polar that overlaps its centraliser refutes recognition. -/
theorem not_rigidPolarRecognition_of_overlap {S : Y ≃ₜ Y} (hS : IsMinimalHomeo S)
    {P : Subgroup (topologicalFullGroup S)} (hPol : IsRigidPolar P)
    {p q : topologicalFullGroup S} (hp : p ∈ P)
    (hq : q ∈ Subgroup.centralizer (P : Set (topologicalFullGroup S)))
    (hpq : ¬ Disjoint (movedSet (p : Y ≃ₜ Y)) (movedSet (q : Y ≃ₜ Y))) :
    ¬ RigidPolarRecognitionStatement :=
  fun h => hpq (rigidPolarSupportSeparation_of_rigidPolarRecognition h Y S hS P hPol p hp q hq)

/-- Formal refutation of recognition from the configuration of the module docstring: mutually
centralising `P, Q` with trivial meet, containing rigid stabilisers of open sets that meet all
their translates, and with overlapping elements. -/
theorem not_rigidPolarRecognition_of_centralizer_eq_of_persistent {S : Y ≃ₜ Y}
    (hS : IsMinimalHomeo S) {P Q : Subgroup (topologicalFullGroup S)} {A V : Set Y}
    (hQ : Subgroup.centralizer (P : Set (topologicalFullGroup S)) = Q)
    (hP : Subgroup.centralizer (Q : Set (topologicalFullGroup S)) = P)
    (hPQ : P ⊓ Q = ⊥) (hA : IsOpen A) (hV : IsOpen V)
    (hAP : rubinRigidSubgroup S A ≤ P) (hVQ : rubinRigidSubgroup S V ≤ Q)
    (hAg : ∀ g : topologicalFullGroup S, (A ∩ ((g : Y ≃ₜ Y)⁻¹ : Y ≃ₜ Y) ⁻¹' A).Nonempty)
    (hVg : ∀ g : topologicalFullGroup S, (V ∩ ((g : Y ≃ₜ Y)⁻¹ : Y ≃ₜ Y) ⁻¹' V).Nonempty)
    {p q : topologicalFullGroup S} (hp : p ∈ P) (hq : q ∈ Q)
    (hpq : ¬ Disjoint (movedSet (p : Y ≃ₜ Y)) (movedSet (q : Y ≃ₜ Y))) :
    ¬ RigidPolarRecognitionStatement := by
  have hPol : IsRigidPolar P :=
    isRigidPolar_of_centralizer_eq_of_persistent hQ hP hPQ hAP hVQ
      (fun g => rubinRigidSubgroup_inf_conj_ne_bot hS hA g (hAg g))
      (fun g => rubinRigidSubgroup_inf_conj_ne_bot hS hV g (hVg g))
  have hq' : q ∈ Subgroup.centralizer (P : Set (topologicalFullGroup S)) := by
    rw [hQ]
    exact hq
  exact not_rigidPolarRecognition_of_overlap hS hPol hp hq' hpq

end RecognitionFalseSystem

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinConjSubgroup_mono
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.inf_rubinConjSubgroup_ne_bot_of_le
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.isRigidPolar_of_centralizer_eq_of_persistent
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinRigidSubgroup_inf_conj_ne_bot
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.not_rigidPolarRecognition_of_overlap
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.not_rigidPolarRecognition_of_centralizer_eq_of_persistent
