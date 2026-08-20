import GroupApproximation.Analysis.CompressionTraceFolner
import GroupApproximation.Analysis.CompressionTraceLocallyFinite

/-!
# What is unconditional in Tikuisis--White--Winter, and what is not

The manuscript's `INT.11` prints *"all amenable groups are MF, by
quasidiagonality"* and cites Tikuisis, White, Winter, *Quasidiagonality of
nuclear C⋆-algebras*, Ann. of Math. (2) **185** (2017), 229--284:

> every faithful trace on a separable nuclear C⋆-algebra satisfying the
> universal coefficient theorem is quasidiagonal.

`Analysis.TikuisisWhiteWinter` typed that sentence and walked the route from it
to the printed group implication.  This wave removes from the route everything
that is not the theorem itself, and then shows that the elementary
construction cannot supply what is left.  This file is the summary; every
statement it makes is proved in the four modules it collects.

## Unconditional, in this repository

| step of the route | status |
|---|---|
| `C⋆_r(G)` separable | proved (`reducedGroupCStar_separableSpace`) |
| `τ_r` a faithful tracial state | proved (`canonicalFaithfulTracialState`) |
| `C⋆_r(G)` nuclear for amenable `G` (Lance) | proved (`isNuclearCStarAlgebra_reducedGroupCStar_of_isAmenable`) |
| the UCT for those algebras (Tu) | eliminated (`Analysis.TikuisisWhiteWinterAmenableClass`) |
| a ucp map into `M_k` is `⋆`-preserving and contractive | proved (`ucp_map_star`, `ucp_norm_le`) |
| a quasidiagonal trace is an MF trace | proved (`isMFTrace_of_isQuasidiagonalTrace`) |
| an MF canonical trace makes the group operator-MF | proved (`isOperatorMF_of_isMFTrace_canonicalMaximal`) |
| **the canonical trace of `C⋆_r(G)` is quasidiagonal for amenable `G`** | **this is the theorem** |

`isOperatorMF_of_isAmenable_of_canonicalTraceQuasidiagonal` states the route
with exactly one hypothesis left, and that hypothesis is the last row: for
countable amenable `G`, the canonical trace of `C⋆_r(G)` is quasidiagonal.
Nothing else about Tikuisis--White--Winter is used anywhere on the route ---
not the general separable nuclear UCT statement, not Lance, not Tu.

## Proved outright, at infinite-dimensional algebras

`isQuasidiagonalTrace_canonicalReduced_of_locallyFinite`: **for a countable
locally finite group the canonical trace of `C⋆_r(G)` is quasidiagonal**, with
no input.  This is the conclusion of Tikuisis--White--Winter at a class of
algebras where it is provable by hand, and it is the first inhabitant of
`Quasidiagonal.QuasidiagonalTraceModel` in this repository at anything other
than a matrix algebra.  It yields `IsOperatorMF` for those groups
(`isOperatorMF_of_locallyFinite_of_compression`), by the printed route rather
than by the LEF route of `Sofic.LocallyFiniteMF`, and the two share no step.

## The obstruction, made precise

The construction behind that theorem --- compression to a finite window of
`ℓ²(G)` --- is the elementary source of quasidiagonal models, and
`Analysis.CompressionTraceRigidity` shows it is rigid: the operator-norm
multiplicativity defect of a compression is `0` or at least `1`.  Hence
`compressionFamily_iff_locallyFinite`: compressions certify **exactly** the
locally finite groups.  Below, `not_exists_compressionFamily_of_injective_pow`
records the consequence at a single element of infinite order, and
`not_exists_compressionFamily_multiplicativeInt` at `ℤ` --- an amenable group,
so a group where Tikuisis--White--Winter asserts a conclusion that provably no
compression family witnesses.

That is the exact size of the remaining gap.  It is not slack in an estimate
and not bookkeeping: any proof of the last row must produce ucp maps that are
*not* compressions, and the known one is Tikuisis--White--Winter, whose input
is the classification theory of nuclear C⋆-algebras.  **No part of that theory
is formalized here, nothing below assumes it, and no declaration in this
repository inhabits `QuasidiagonalMF.TikuisisWhiteWinterInput`.**

## And what amenability *does* deliver

`Analysis.CompressionTraceFolner` measures the same defect in the normalized
Hilbert--Schmidt norm and finds it equal to the Følner ratio of the window.  So
for every countable amenable group the compressions *are* asymptotically
multiplicative --- in the `2`-norm.
`exists_compression_ucp_traceExact_hsSmall_opNormOne` below collects the whole
accounting at one group and one matrix: unital, completely positive, trace
exact, `2`-norm defect arbitrarily small, operator-norm defect at least `1`.
The theorem being cited is precisely the passage from the fourth of those to
the fifth.

## Manuscript status

`INT.11` and `CY.12c` keep their grades: they remain literature inputs.  What
changes is the size of the input --- one statement about one trace on one
algebra per group, instead of a general theorem plus Lance plus Tu --- and the
fact that the elementary alternative is now refuted rather than merely
unproved.
-/

namespace GroupApproximation
namespace Quasidiagonal

open Filter ReducedGroupCStarTrace
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

variable {G : Type u} [Group G]

/-! ## The route, with one hypothesis -/

/-- **`INT.11` over its irreducible core.**

Every countable amenable group is operator-MF, granted only this: for a
countable amenable group the canonical trace of its reduced C⋆-algebra is
quasidiagonal.  That hypothesis is the conclusion of Tikuisis--White--Winter at
the algebras and the trace this route feeds it; everything else on the route is
a theorem of this repository.

The hypothesis is stated as an explicit premise and the conclusion group by
group, rather than as a producer of a typed input structure, for the reason
recorded in `Analysis.AmenableMFInput`: a producer from bare `∀`-premises
enters the discharge fixpoint of `scripts/check_non_mf_unconditional.py` and
would silently mark the open input as inhabited. -/
theorem isOperatorMF_of_isAmenable_of_canonicalTraceQuasidiagonal
    (hqd : ∀ (H : Type u) [Group H] [Countable H],
      Amenability.IsAmenable H → IsQuasidiagonalTrace (canonicalReducedTrace H))
    (G : Type u) [Group G] [Countable G]
    (hA : Amenability.IsAmenable G) : IsOperatorMF G :=
  QuasidiagonalMF.isOperatorMF_of_isQuasidiagonalCanonicalTrace ucpContractive G
    (hqd G hA)

/-- The contrapositive, in the shape `sec:consequences` uses. -/
theorem not_isAmenable_of_not_isOperatorMF_of_canonicalTraceQuasidiagonal
    (hqd : ∀ (H : Type u) [Group H] [Countable H],
      Amenability.IsAmenable H → IsQuasidiagonalTrace (canonicalReducedTrace H))
    (G : Type u) [Group G] [Countable G] (hMF : ¬ IsOperatorMF G) :
    ¬ Amenability.IsAmenable G :=
  fun hA ↦ hMF (isOperatorMF_of_isAmenable_of_canonicalTraceQuasidiagonal hqd G hA)

/-! ## Local finiteness is a genuine restriction -/

/-- A group with an element of infinite order is not locally finite: a finite
subgroup containing that element would contain all of its powers. -/
theorem not_isLocallyFiniteGroup_of_injective_pow {g : G}
    (hg : Function.Injective fun n : ℕ ↦ g ^ n) :
    ¬ IsLocallyFiniteGroup G := by
  classical
  intro hlf
  obtain ⟨H, hHfin, hmem⟩ := hlf {g}
  haveI : Finite H := hHfin
  have hgH : g ∈ H := hmem g (Finset.mem_singleton_self g)
  have hinj : Function.Injective
      (fun n : ℕ ↦ (⟨g ^ n, pow_mem hgH n⟩ : H)) := by
    intro a b hab
    exact hg (congrArg Subtype.val hab)
  haveI : Finite ℕ := Finite.of_injective _ hinj
  exact not_finite ℕ

/-- The generator of `ℤ`, written multiplicatively, has infinite order. -/
theorem injective_pow_ofAdd_one :
    Function.Injective fun n : ℕ ↦ (Multiplicative.ofAdd (1 : ℤ)) ^ n := by
  intro a b hab
  have hab' : (Multiplicative.ofAdd (1 : ℤ)) ^ a
      = (Multiplicative.ofAdd (1 : ℤ)) ^ b := hab
  have h : ((Multiplicative.ofAdd (1 : ℤ)) ^ a).toAdd
      = ((Multiplicative.ofAdd (1 : ℤ)) ^ b).toAdd := by rw [hab']
  rw [toAdd_pow, toAdd_pow, toAdd_ofAdd] at h
  exact_mod_cast h

/-- `ℤ` is not locally finite. -/
theorem not_isLocallyFiniteGroup_multiplicativeInt :
    ¬ IsLocallyFiniteGroup (Multiplicative ℤ) :=
  not_isLocallyFiniteGroup_of_injective_pow injective_pow_ofAdd_one

/-! ## The elementary construction does not reach the printed sentence -/

/-- **No compression family for a group with an element of infinite order.**

By `isLocallyFiniteGroup_of_isAsymptoticallyMultiplicative`, an asymptotically
multiplicative compression family forces local finiteness; an element of
infinite order forbids it.  So for such a group the compression construction
does not merely fail to be known to work --- it provably does not work. -/
theorem not_exists_compressionFamily_of_injective_pow {g : G}
    (hg : Function.Injective fun n : ℕ ↦ g ^ n) :
    ¬ ∃ F : CompressionFamily G,
        (∀ n : ℕ, 0 < F.size n) ∧ F.IsAsymptoticallyMultiplicative := by
  rintro ⟨F, hpos, hmul⟩
  exact not_isLocallyFiniteGroup_of_injective_pow hg
    (isLocallyFiniteGroup_of_isAsymptoticallyMultiplicative F
      (Filter.Eventually.of_forall hpos) hmul)

/-- **The gap, at one group.**  `ℤ` is amenable, so Tikuisis--White--Winter
asserts that the canonical trace of `C⋆_r(ℤ)` is quasidiagonal; no compression
family witnesses it.  Whatever proves the last row of the route, it is not the
construction that proves the locally finite case. -/
theorem not_exists_compressionFamily_multiplicativeInt :
    ¬ ∃ F : CompressionFamily (Multiplicative ℤ),
        (∀ n : ℕ, 0 < F.size n) ∧ F.IsAsymptoticallyMultiplicative :=
  not_exists_compressionFamily_of_injective_pow injective_pow_ofAdd_one

/-! ## The whole accounting, at one group and one matrix -/

/-- **`INT.11`, taken apart.**

Let `G` be a countable amenable group with an element `g` of infinite order ---
`ℤ` is the smallest example, and every group the printed sentence quantifies
over that is not locally finite has one.  Then for every accuracy `ε` there is
a compression `φ_e` of `C⋆_r(G)` to a `k × k` matrix algebra with

* `φ_e` unital,
* `φ_e` completely positive,
* `tr ∘ φ_e = τ` **exactly**, at every element of the algebra,
* multiplicativity defect at `(λ_{g⁻¹}, λ_g)` below `ε` in the normalized
  Hilbert--Schmidt norm,
* and that same defect of operator norm at least `1`.

Four of the five clauses of `Quasidiagonal.QuasidiagonalTraceModel` are
therefore met by an explicit elementary construction, uniformly in the
accuracy; the fifth is met in the `2`-norm and missed in the operator norm by
the largest margin a contraction allows.  That difference is what
Tikuisis--White--Winter supplies, and nothing in this repository supplies it. -/
theorem exists_compression_ucp_traceExact_hsSmall_opNormOne
    (hG : Amenability.IsAmenable G) {g : G}
    (hg : Function.Injective fun n : ℕ ↦ g ^ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (e : Fin k → G), 0 < k ∧
      compressionMap e 1 = 1 ∧
      IsCompletelyPositiveOnMatrices (naturalFiniteModel k)
        ⇑(compressionMap e) ∧
      (∀ a : ReducedGroupCStar G,
        normTrace (naturalFiniteModel k) (compressionMap e a)
          = canonicalReducedTrace G a) ∧
      hsNormSq (naturalFiniteModel k) (inverseDefect e g) < ε ∧
      1 ≤ ‖inverseDefect e g‖ := by
  obtain ⟨k, e, hkpos, heinj, hhs, hop⟩ :=
    exists_compression_hsNormSq_lt_and_one_le_norm hG hg hε
  exact ⟨k, e, hkpos, compressionMap_one heinj,
    isCompletelyPositiveOnMatrices_compressionMap e,
    fun a ↦ normTrace_compressionMap hkpos e a, hhs, hop⟩

/-! ## The unconditional headline, restated -/

/-- **`INT.11`, unconditionally, on the locally finite subclass of the amenable
groups**, together with the intermediate statement the printed words *by
quasidiagonality* name.

No input of any kind: the hypothesis of
`isOperatorMF_of_isAmenable_of_canonicalTraceQuasidiagonal` is discharged here
rather than assumed, by the construction of
`Analysis.CompressionTraceLocallyFinite`. -/
theorem isQuasidiagonalTrace_and_isOperatorMF_of_locallyFinite (G : Type u)
    [Group G] [Countable G] (hG : IsLocallyFiniteGroup G) :
    IsQuasidiagonalTrace (canonicalReducedTrace G) ∧ IsOperatorMF G :=
  ⟨isQuasidiagonalTrace_canonicalReduced_of_locallyFinite G hG,
    isOperatorMF_of_locallyFinite_of_compression G hG⟩

end

end Quasidiagonal
end GroupApproximation
