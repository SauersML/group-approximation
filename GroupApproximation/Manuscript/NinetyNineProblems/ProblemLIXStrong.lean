import GroupApproximation.Analysis.LIXEndpointStatement
import GroupApproximation.Analysis.CStarSimple
import GroupApproximation.Analysis.LIXLimitSimple
import GroupApproximation.Analysis.LIXLemmaTwoPropGeneric
import GroupApproximation.Manuscript.NinetyNineProblems.SquarefreeDvd
import GroupApproximation.Meta.AxiomGuard

/-!
# STW Problem LIX, strengthened: powers of the witness

`Manuscript/NinetyNineProblems/ProblemLIX.lean` answers the printed question: the
counterexample algebra carries a unitary `u ∉ U₀(A)` whose `diag (u, 1)` lies in `U₀(M₂(A))`,
so the kernel of `U(A)/U₀(A) → K₁(A)` is nonzero.  That says the kernel is nonzero and nothing
about its size.

This file states the size.  At rank `n` the tower carries a unitary `v` whose class dies at the
first stabilisation and whose powers leave `U₀(A)` unless the exponent is divisible by every
prime dividing `n`, so the order of `v` in `U(A)/U₀(A)` is divisible by the radical of `n` or
infinite.  At `n = 2` that is the existing answer read at `k = 1`.

## What is a theorem here and what is a hypothesis

Everything below is proved.  The two propositions the construction still owes are **named**,
so that the arrow each lane has to supply is a single citable name rather than a shape spread
over several modules:

* `ClimbedPowersOutside n` — the `k`-indexed Corollary 4 at the limit: one fixed unitary of
  `LIX.Gen.LIXLimit n` whose stabilisation is null-homotopic and whose `k`-th power stays
  outside `U₀` whenever some prime dividing `n` does not divide `k`.  Owner `sp-tower`, from
  `sp-powers`' homotopy `ũ ^ (k+1) ≃ ũ ∘ ψ_k` and the climb of `Analysis/LIXLemmaSixCor4`.
  It is stated at the LIMIT and with the unitary bound OUTSIDE the quantifier over `k`,
  because that is what the endpoint needs: a statement that re-quantifies the unitary for each
  exponent bounds no order.
* `LemmaTwoHoldsForSections n b` — Lemma 2 at every stage of the rank-`n` tower for a family
  of sections.  Owner `sp-oddside` (Step C with `k` zeros) and `sp-evenside` (Step D mod `p`),
  under `sp-design`'s uniform theorem.  The section family is a **parameter** rather than the
  named suspension `Σψ_k`, so that this file fixes the vocabulary without waiting for that
  name; the instance the programme wants is `b k = fun j m => bVec n (Σψ_k m)`.
* `Corollary4Powers n b` — the arrow between them, which is `sp-tower`'s deliverable.  It is a
  hypothesis of the `_data` forms below exactly as `LIX.lixLimit_hasK1InjWitness_of` was a
  hypothesis in `ProblemLIX.lean` while it landed, and for the same reason: the assembly is
  finished and stays green while the arrow arrives.

## The order instances

`diagOne` and `CStarMat 2 A` elaborate only under `[PartialOrder A]` and `[StarOrderedRing A]`,
and this tree carries **two** declarations of the spectral pair.
`GroupApproximation.instSpectralPartialOrder` / `instSpectralStarOrderedRing`
(`Analysis/LIXEndpointStatement.lean`) is the pair `HasK1InjWitness` is stated over and the one
that file's docstring tells a consumer to re-register;
`GroupApproximation.LIX.instSpectralPartialOrder` / `instSpectralStarOrderedRing`
(`Analysis/LIXLimitMatrixTransport.lean`) is a second, definitionally equal but distinct, term,
and it is what all eight rank-`n` files under `Analysis/` actually register.

This file registers the **`LIX` pair**, at priority 100000, matching those eight (ruling by
`sp-design`, 2026-09-10).  The reason is about the producer and not the consumer.  Consuming
`HasK1InjWitness` needs only definitional equality, which `exact` supplies whichever pair is in
scope, because `HasK1InjWitness` is a `def` whose body was fixed when it was elaborated.  But
`ClimbedPowersOutside` below is a statement someone else has to PROVE, in files that register
the `LIX` pair, and a proof that needs to `rw` or `simp` against it needs the instances to
match syntactically and not merely definitionally.  The producer's spelling is the one to
match.

The Palomar surface is immune to the choice either way: `Palomar/LIXStrongSolution.lean` writes
`letI : PartialOrder A := CStarAlgebra.spectralOrder A` inline, as the existing surface does,
and names neither pair.
-/

namespace GroupApproximation
namespace NinetyNineProblems

noncomputable section

attribute [local instance 100000] GroupApproximation.LIX.instSpectralPartialOrder
                                  GroupApproximation.LIX.instSpectralStarOrderedRing

/-! ## The witness condition, generalised to powers -/

variable (A : Type) [CStarAlgebra A]

/-- **The witness condition, generalised to powers.**  `A` carries a unitary `v` whose
stabilisation `diag (v, 1)` is null-homotopic in `U(M₂(A))` and whose powers leave `U₀(A)`
unless the exponent is divisible by every prime dividing `n`.

The power clause read at `k = 1` gives `HasK1InjWitness A`, because `2 ≤ n` supplies a prime
`p ∣ n` and `p ∣ 1` is false; at general `k` it says strictly more, so the implication
(`hasK1InjWitness_of_hasK1InjPowerWitness`) does not reverse.  The unitary is bound once,
outside the quantifier over `k`; that is the whole content, since a witness chosen per
exponent says nothing about any element's order. -/
def HasK1InjPowerWitness (n : ℕ) : Prop :=
  ∃ v : unitary A, diagOne v ∈ unitaryComponentOne (CStarMat 2 A) ∧
    ∀ k : ℕ, v ^ k ∈ unitaryComponentOne A → ∀ p : ℕ, p.Prime → p ∣ n → p ∣ k

variable {A}

/-- **The power witness contains the plain witness.**  Reading the power clause at `k = 1`
gives `v ∉ U₀(A)`, because `2 ≤ n` supplies a prime dividing `n` and no prime divides `1`
(`not_forall_prime_dvd_one`).

This is why the strengthened statements carry no `v ∉ U₀(A)` conjunct: it would be a
consequence of a clause they already have, and a redundant conjunct in an endpoint is a clause
a reader has to check is not doing work. -/
theorem hasK1InjWitness_of_hasK1InjPowerWitness {n : ℕ} (hn : 2 ≤ n)
    (h : HasK1InjPowerWitness A n) : HasK1InjWitness A := by
  obtain ⟨v, hdiag, hpow⟩ := h
  refine hasK1InjWitness_iff.mpr ⟨v, ?_, hdiag⟩
  intro hv
  refine not_forall_prime_dvd_one hn fun p hp hpn => ?_
  exact hpow 1 (by simpa using hv) p hp hpn

/-- **The power witness refutes `K₁`-injectivity**, through the plain witness. -/
theorem not_k1Inj_of_hasK1InjPowerWitness {n : ℕ} (hn : 2 ≤ n)
    (h : HasK1InjPowerWitness A n) : ¬ K1Inj A :=
  not_k1Inj_of_hasWitness (hasK1InjWitness_of_hasK1InjPowerWitness hn h)

/-- **The `n = 6` reading.**  Divisibility by every prime dividing `6` is divisibility by `6`,
so the witness at rank six has a power clause with a single conclusion, which is the form the
headline instance states. -/
theorem six_dvd_of_hasK1InjPowerWitness (h : HasK1InjPowerWitness A 6) :
    ∃ v : unitary A, diagOne v ∈ unitaryComponentOne (CStarMat 2 A) ∧
      ∀ k : ℕ, v ^ k ∈ unitaryComponentOne A → 6 ∣ k := by
  obtain ⟨v, hdiag, hpow⟩ := h
  exact ⟨v, hdiag, fun k hk => six_dvd_of_forall_prime_dvd fun p hp hp6 => hpow k hk p hp hp6⟩

/-- **The squarefree reading.**  For squarefree `N`, divisibility by every prime dividing `N`
is divisibility by `N` (`squarefree_dvd_of_forall_prime_dvd`).  Squarefreeness is exactly the
hypothesis this method supports: mod-`p` cohomology sees `p` and not `p²`. -/
theorem dvd_of_hasK1InjPowerWitness_of_squarefree {N : ℕ} (hsq : Squarefree N)
    (h : HasK1InjPowerWitness A N) :
    ∃ v : unitary A, diagOne v ∈ unitaryComponentOne (CStarMat 2 A) ∧
      ∀ k : ℕ, v ^ k ∈ unitaryComponentOne A → N ∣ k := by
  obtain ⟨v, hdiag, hpow⟩ := h
  exact ⟨v, hdiag, fun k hk =>
    squarefree_dvd_of_forall_prime_dvd hsq fun p hp hpN => hpow k hk p hp hpN⟩

/-! ## The two named propositions the construction still owes -/

/-- **The `k`-indexed Corollary 4 at rank `n`, at the limit.**  One fixed unitary of
`LIX.Gen.LIXLimit n` whose stabilisation is null-homotopic in `U(M₂)` and whose `k`-th power
lies outside `U₀` whenever some prime `p ∣ n` fails to divide `k`.

Owner `sp-tower`.  The chain is `sp-powers`' homotopy from the `(k+1)`-st power of the
renormalised seam generator to its precomposition with `ψ_k`, then the frames pulled back
along `Σψ_k`, then the climb of `Analysis/LIXLemmaSixCor4`'s `climb_genUnitary_notMem` at the
`k`-th power, then `LIX.Gen.lixLimit_hasK1InjWitness`'s tower argument.

Stated in the contrapositive — `¬ p ∣ k → v ^ k ∉ U₀` — because that is the direction the
bundle obstruction proves.  `hasK1InjPowerWitness_of_climbedPowersOutside` turns it into the
implication the endpoint states. -/
def ClimbedPowersOutside (n : ℕ) : Prop :=
  ∃ v : unitary (LIX.Gen.LIXLimit n),
    diagOne v ∈ unitaryComponentOne (CStarMat 2 (LIX.Gen.LIXLimit n)) ∧
      ∀ p : ℕ, p.Prime → p ∣ n → ∀ k : ℕ, ¬ p ∣ k →
        v ^ k ∉ unitaryComponentOne (LIX.Gen.LIXLimit n)

/-- **Lemma 2 at every stage of the rank-`n` tower, for a family of sections.**  At stage `j`
the section is `b j`, and the assertion is that the complement of `b j` and the complement of
the constant section are not Murray--von Neumann equivalent as continuous fields over
`M = S^{2n+1} × ∏_{i<j} ℂP^{dᵢ}` with `dᵢ = LIX.Gen.lixDD n j i = 2 ^ i · n`.

At `b j = CharClass.Gen.bVec n` this is `LIX.Gen.LemmaTwoHolds n`, the input of the rank-`n`
answer at `k = 1`.  The `k`-indexed instance is the programme note's `b = x ∘ Σψ_k`, which in
this vocabulary is

    b k j := fun m => LIX.Powers.joinPowNeg e₁ e₂ k (CharClass.Gen.bVec n m)

and `sp-design`'s `LemmaTwoHoldsPow n k` is exactly `LemmaTwoHoldsForSections n (b k)` for that
family.  **The composition order matters**: the suspension is applied to the SPHERE VECTOR
`bVec n m`, not to the base point `m`, because `b = x ∘ Σψ_k` means `b m = Σψ_k (x m)`.  The
other order is the slip that cost a correction in the programme note's §1.3.2.  `Σψ_k`
preserves the norm, so the zero-locus lemma still fires on the composed section; `sp-powers`
and `sp-tower` own the `norm_suspPsi` that says so, beside their definition of the family.

The section family is passed as DATA here rather than named, so that this file does not wait
for the name the shape layer gives `Σψ_k` or for the choice of the two vectors spanning its
plane.

Owners: `sp-oddside` for Step C with `k` zeros, `sp-evenside` for Step D mod `p`, under
`sp-design`'s uniform theorem at `p ∣ n`. -/
def LemmaTwoHoldsForSections (n : ℕ)
    (b : ∀ j : ℕ, CharClass.Gen.baseM n (LIX.Gen.lixDD n j) → Fin (n + 1) → ℂ) : Prop :=
  ∀ j : ℕ, LIX.Gen.LemmaTwoFor n (LIX.Gen.lixDD n j) (b j)

/-- **The arrow `sp-tower` owes**: Lemma 2 at every stage, for every exponent no prime dividing
`n` divides, gives the climbed power witness.

A named `Prop` rather than a hypothesis spelled out at each use, so that the day it becomes a
theorem the `_data` forms below lose an argument and nothing else changes. -/
def Corollary4Powers (n : ℕ)
    (b : ℕ → ∀ j : ℕ, CharClass.Gen.baseM n (LIX.Gen.lixDD n j) → Fin (n + 1) → ℂ) : Prop :=
  (∀ p : ℕ, p.Prime → p ∣ n → ∀ k : ℕ, ¬ p ∣ k → LemmaTwoHoldsForSections n (b k)) →
    ClimbedPowersOutside n

/-- **The contrapositive is the statement.**  A witness whose powers stay outside `U₀` when a
prime dividing `n` misses the exponent is a witness whose powers lying in `U₀` force every such
prime to divide the exponent.

The only step is `by_contra`, and it is a step: the bundle obstruction proves a nonvanishing
and the endpoint states a divisibility, and the two are the same fact only after this
exchange. -/
theorem hasK1InjPowerWitness_of_climbedPowersOutside (n : ℕ) (h : ClimbedPowersOutside n) :
    HasK1InjPowerWitness (LIX.Gen.LIXLimit n) n := by
  obtain ⟨v, hdiag, hout⟩ := h
  refine ⟨v, hdiag, fun k hk p hp hpn => ?_⟩
  by_contra hpk
  exact hout p hp hpn k hpk hk

/-! ## The development-side stronger theorem -/

/-- **The stronger theorem, in the development's vocabulary.**  For every `n ≥ 2` the
counterexample algebra at rank `n` is nontrivial, C⋆-simple and separable, and carries the
power witness.

`NeZero n` is derived from `2 ≤ n` rather than asked for: it is what
`Nontrivial (LIX.Gen.LIXLimit n)` and `LIX.Gen.lixLimit_isSimpleCStar` carry, and the
endpoint's hypothesis is the numeric one.

Simplicity and separability are theorems at every rank (`sp-tower`), so `ClimbedPowersOutside`
is the only argument. -/
theorem exists_simple_separable_hasK1InjPowerWitness_of (n : ℕ) (hn : 2 ≤ n)
    (h : ClimbedPowersOutside n) :
    ∃ (A : Type) (_ : CStarAlgebra A),
      Nontrivial A ∧ IsSimpleCStar A ∧ TopologicalSpace.SeparableSpace A ∧
        HasK1InjPowerWitness A n := by
  haveI : NeZero n := ⟨by omega⟩
  exact ⟨LIX.Gen.LIXLimit n, inferInstance, inferInstance,
    LIX.Gen.lixLimit_isSimpleCStar n, LIX.Gen.lixLimit_separableSpace n,
    hasK1InjPowerWitness_of_climbedPowersOutside n h⟩

/-- **The same with Mathlib's simplicity**, which is what the Palomar surface states.

`isSimpleCStar_iff_isSimpleRing` is the bridge, and it carries `[Nontrivial A]` because the two
notions genuinely disagree at the zero algebra: `IsSimpleCStar` holds there vacuously while
Mathlib's `IsSimpleOrder` extends `Nontrivial`. -/
theorem exists_isSimpleRing_separable_hasK1InjPowerWitness_of (n : ℕ) (hn : 2 ≤ n)
    (h : ClimbedPowersOutside n) :
    ∃ (A : Type) (_ : CStarAlgebra A),
      Nontrivial A ∧ IsSimpleRing A ∧ TopologicalSpace.SeparableSpace A ∧
        HasK1InjPowerWitness A n := by
  haveI : NeZero n := ⟨by omega⟩
  refine ⟨LIX.Gen.LIXLimit n, inferInstance, inferInstance, ?_,
    LIX.Gen.lixLimit_separableSpace n,
    hasK1InjPowerWitness_of_climbedPowersOutside n h⟩
  exact (isSimpleCStar_iff_isSimpleRing (LIX.Gen.LIXLimit n)).mp
    (LIX.Gen.lixLimit_isSimpleCStar n)

/-- **The stronger theorem over the topological input**, with `sp-tower`'s arrow still
explicit.

The `_data` suffix is `ProblemLIX.lean`'s: it marks a form whose last argument is an arrow a
lane owes, kept so that this file is green before that lane lands and so that the published
signature does not change when it does. -/
theorem exists_isSimpleRing_separable_hasK1InjPowerWitness_of_lemmaTwo_data (n : ℕ) (hn : 2 ≤ n)
    {b : ℕ → ∀ j : ℕ, CharClass.Gen.baseM n (LIX.Gen.lixDD n j) → Fin (n + 1) → ℂ}
    (hcor4 : Corollary4Powers n b)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → ∀ k : ℕ, ¬ p ∣ k → LemmaTwoHoldsForSections n (b k)) :
    ∃ (A : Type) (_ : CStarAlgebra A),
      Nontrivial A ∧ IsSimpleRing A ∧ TopologicalSpace.SeparableSpace A ∧
        HasK1InjPowerWitness A n :=
  exists_isSimpleRing_separable_hasK1InjPowerWitness_of n hn (hcor4 h)

/-- **The refutation of `K₁`-injectivity, at every rank.**  Implied by the stronger theorem and
recorded separately because it is the statement `ProblemLIX.lean` answers: at every rank the
algebra is a counterexample, and the ranks differ only in how much of the kernel they
exhibit. -/
theorem exists_simple_separable_not_k1Inj_of (n : ℕ) (hn : 2 ≤ n)
    (h : ClimbedPowersOutside n) :
    ∃ (A : Type) (_ : CStarAlgebra A),
      Nontrivial A ∧ IsSimpleCStar A ∧ TopologicalSpace.SeparableSpace A ∧ ¬ K1Inj A := by
  obtain ⟨A, inst, hnt, hsimp, hsep, hwit⟩ :=
    exists_simple_separable_hasK1InjPowerWitness_of n hn h
  exact ⟨A, inst, hnt, hsimp, hsep, not_k1Inj_of_hasK1InjPowerWitness hn hwit⟩

end

end NinetyNineProblems
end GroupApproximation

open GroupApproximation.NinetyNineProblems

#audit_axioms HasK1InjPowerWitness
#audit_axioms hasK1InjWitness_of_hasK1InjPowerWitness
#audit_axioms not_k1Inj_of_hasK1InjPowerWitness
#audit_axioms six_dvd_of_hasK1InjPowerWitness
#audit_axioms dvd_of_hasK1InjPowerWitness_of_squarefree
#audit_axioms ClimbedPowersOutside
#audit_axioms LemmaTwoHoldsForSections
#audit_axioms Corollary4Powers
#audit_axioms hasK1InjPowerWitness_of_climbedPowersOutside
#audit_axioms exists_simple_separable_hasK1InjPowerWitness_of
#audit_axioms exists_isSimpleRing_separable_hasK1InjPowerWitness_of
#audit_axioms exists_isSimpleRing_separable_hasK1InjPowerWitness_of_lemmaTwo_data
#audit_axioms exists_simple_separable_not_k1Inj_of
