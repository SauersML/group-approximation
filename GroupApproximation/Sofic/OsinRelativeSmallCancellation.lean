import GroupApproximation.Algebra.FreeProductConjugacy
import Mathlib.Tactic.Linarith
import GroupApproximation.Algebra.FreeProductFactorQuotient

/-!
# Small cancellation over `U * H`: the peripheral factor stays embedded, and
torsion stays where it was

Osin, *Small cancellations over relatively hyperbolic groups and embedding
theorems* (Ann. of Math. **172** (2010) 1–39), Theorems 2.4 and 2.4.5: if `Γ`
is hyperbolic relative to a collection of peripheral subgroups and `R` is a
symmetrized set of words satisfying the relative small-cancellation condition,
then in `Γ / ⟪R⟫`

* every peripheral subgroup still embeds, and
* every element of finite order is conjugate to the image of an element of
  finite order of a peripheral subgroup —

so a quotient of a torsion-free group with torsion-free peripherals is again
torsion-free.  Fournier-Facio (arXiv:2608.02025, §2) applies this to the pair
`(U * H, U)`, where `U` is a universal finitely presented torsion-free group
and `H` is a torsion-free hyperbolic Kazhdan group: the free product is
hyperbolic relative to `U` precisely because the complementary factor `H` is
hyperbolic, and the small-cancellation quotient is the Kazhdan envelope of
`U`.  Row `LI.12b` of the proof ledger points at exactly that step, and
`Sofic.SmallCancellationKazhdanEnvelope` records its conclusion list as a
typed input.

**This file replaces the two conclusions of that input by theorems.**  What is
formalized is the free-product case: `Γ = ∗ᵢ Gᵢ`, peripheral structure the
family of factors, pieces and lengths measured in syllables.  That is
Lyndon--Schupp, *Combinatorial Group Theory*, Ch. V §§9–11 — the classical
predecessor Osin's relative theory generalizes, and the case the
Fournier-Facio application is stated over.  The router's own docstring already
anticipated it: "the relative refinement replaces letters by
`Monoid.CoprodI` syllables" (`Sofic.SmallCancellationRouter.GreendlingerGate`).

## What is proved here, with nothing assumed

* `factorMap_injective_of_cyclicallyReduced` — **the peripheral factor stays
  embedded.**  A nontrivial element of a factor spells a word of syllable
  length one, and the Greendlinger length bound makes every nontrivial element
  of the relator subgroup longer than half of some relator.  Cyclically reduced
  relators have two syllables or more (`two_le_wlen`), so no separate length
  hypothesis is needed.  This is the whole of the embedding clause, for *every*
  factor, not only the peripheral one.
* `isPowerTorsionFree_of_torsionIntoFactors` — **the quotient stays
  torsion-free**, given the torsion classification, the embedding clause, and
  torsion-free factors.  Torsion-freeness of the factors is spent exactly
  once, on the element the classification produces.
* `osin_conclusion` — the two clauses together, in the shape the ledger row
  asks for.
* `wlen_le_sylLength_conj` — **the Greendlinger bound for a single conjugate,
  proved outright and with a sharp constant.**  A conjugate of a cyclically
  reduced relator is at least as long as the relator, never merely longer than
  half of it.  This needs no small-cancellation hypothesis: it is
  `FreeProductCyclic.length_le_sylLength_conj`, and behind that the fact that
  `|uⁿ| = n·|u|` for a cyclically reduced `u` while conjugation moves length by
  at most `2|c|`.  It is the one-conjugate case of the open implication below,
  and it is closed.
* `factorMap_not_injective_of_singleton`, `factorMap_not_injective_letterWord`
  — **the length hypothesis is sharp, and the failure is exhibited.**  A
  relator of one syllable is a nontrivial element of a factor and dies in the
  quotient, so "cyclically reduced" is not a convenience: no weaker hypothesis
  carries the embedding clause.
* `factorMap_injective_of_retraction` — **an unconditional embedding
  criterion** covering an infinite family of quotients with no small
  cancellation anywhere in sight: if every relator dies under the retraction
  onto the peripheral factor, the peripheral factor is a retract of the
  quotient.  Small cancellation is not the only way to keep a factor.
* `torsionIntoFactors_of_eq_bot` and `torsionIntoFactors_factorNormal` —
  the classification, proved.  The first is the empty relator family, where
  the quotient *is* `U * H` and the statement is the free-product torsion
  theorem of `Algebra.FreeProductCyclicWord` — sharpened in
  `Algebra.FreeProductConjugacy` to an equivalence
  (`isOfFinOrder_iff_conj_factor`): the torsion of a free product is exactly
  the torsion of its factors, spread over conjugates.  The second is a
  nondegenerate family: all relators drawn from inside the factors, where
  `Algebra.FreeProductFactorQuotient` identifies the quotient with a free
  product of quotient factors and the same theorem applies again.  So neither
  hypothesis of `osin_conclusion` is a name with nothing behind it, and
  `isCyclicallyReduced_pairWord` inhabits the third.

## What is not proved, stated exactly

Exactly one implication, in two readings:

    MetricSmallCancellation R (1/6) → GreendlingerLengthBound R
    MetricSmallCancellation R (1/6) → TorsionIntoFactors (relatorSubgroup R)

**As displayed, both are FALSE — corrected 2026-08-21.**  Three hypotheses are
missing, each with a witness recorded in `Sofic/GreendlingerRelativeTransfer`:
`R` must be symmetrized (a one-element family has no pieces at all, so the
metric condition holds vacuously); no relator may be a proper power (the
symmetrized family of `(xy)^7` over `ℤ * ℤ` has no pieces either, and the image
of `xy` has order seven, so the torsion reading fails); and the constant must
drop below `1/6` against long relators, for the fragment reason set out at the
end of this docstring.  The length reading fails too, over `ℤ * ℤ/3` with the
relator `e·b⁻¹`.  What follows describes the combinatorial core that remains
open once those hypotheses are supplied; the repaired statements live in
`Sofic/GreendlingerRelativeTransfer`.

The core is open for expressions with **two or more** conjugate factors.  The
one-factor case
is `wlen_le_sylLength_conj` above, and it is proved; what the general case
needs is the count that says the cancellations between different conjugates
cannot all be large, and that count is not soft.  Two independent checks that
it is not: the syllable-length methods that close the one-factor case are
conjugacy-invariant, and a product of two conjugates can be arbitrarily short
without the metric condition; and the free-group form of the same statement,
`SmallCancellationRouter.GreendlingerGate`, is open there too, along two
independent routes that share no machinery.

* The **descent** route (`Sofic/Greendlinger*`) carries minimal expressions,
  palindromic normal forms, pieces and a located conclusion with slack, and
  bottoms out — see `Sofic/GreendlingerChunks` — at a bound on a *chain* of
  segments along one rotation, "which is what the curvature count over a
  reduced diagram supplies and what no single re-expression move can".
* The **rewriting** route (`Sofic/GreendlingerDehn`) reads Dehn's algorithm as
  a rewriting system and needs only that reducibility survives free reduction.
  That route is now carried to a single configuration.  `Sofic/Greendlinger‐
  DehnCritical` replaces the rule by the symmetric `DehnSwap` relation and
  settles the critical pairs one at a time; `Sofic/GreendlingerDehnFree`
  discharges the free half outright, and `Sofic/GreendlingerDehnSwap` the swap
  half, the two together by one induction on word length.  What survives is one
  statement, `PieceOverlapRight` (its mirror image follows from it by the
  system's mirror symmetry): two *distinct* relators
  overlapping in a piece, with the part of the step's occurrence beyond the
  overlap at most half of its relator — the one regime in which neither word can
  be made shorter, so the descent on length stalls.  Everything else, including
  every configuration in which the two relators coincide, is a theorem
  (`greendlingerConclusion_of_pieceOverlap`).

Both routes end at the same crossing, and it is a van Kampen argument: that is
the whole of what is open here.

Nothing above is a structure or a hypothesis package.  `Greendlinger‐
Conclusion`, `GreendlingerLengthBound` and `TorsionIntoFactors` are predicates
on a relator family, each with proved instances, so nothing in this file is a
typed literature input and no statement here is conditional on a citation.

One honest caveat about the definitions, **corrected 2026-08-21 — the first
version of this paragraph had the direction backwards.**  Pieces are measured
in whole syllables (`IsPiece`, `MetricSmallCancellation`).  Over a free product
a piece can also be a *fragment* of a syllable — `u = u₁u₂` with only `u₁`
shared — and Lyndon--Schupp handle that with semi-reduced words, counting the
fragment as a full syllable of the piece.  So the classical family of pieces
strictly contains the whole-syllable one, and constraining fewer pieces is a
**weaker** demand: the condition defined here is weaker than classical
`C'(1/6)`, not stronger.

Truncating a classical piece to its complete syllables leaves a whole-syllable
piece, so the gap is exactly one syllable and whole-syllable `C'(lam)` yields
classical `C'(lam + 1/|r|)` and no better.  The consequence for the implication
above is that it needs `lam` strictly below `1/6` together with a relator-length
bound — `lam · |r| + 1 ≤ (1/6) · |r|`, so `|r| ≥ 1 / (1/6 - lam)`; at
`lam = 1/6` no length works.  `Sofic/GreendlingerRelativeTransfer` carries the
repaired statements, with `FragmentSlack` as the named condition.

The caveat concerns only the unproved implication: every theorem in this file
takes the Greendlinger conclusion as given, and those are unaffected.
-/

namespace GroupApproximation
namespace OsinSmallCancellation

open Monoid Monoid.CoprodI

/-! ## 1.  The quotient, and the map from a factor -/

section Quotient

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]

/-- The image of a factor in a quotient of the free product. -/
def factorMap (K : Subgroup (CoprodI G)) [K.Normal] (i : ι) :
    G i →* CoprodI G ⧸ K :=
  (QuotientGroup.mk' K).comp CoprodI.of

@[simp] theorem factorMap_apply (K : Subgroup (CoprodI G)) [K.Normal] (i : ι)
    (x : G i) :
    factorMap K i x = QuotientGroup.mk' K (CoprodI.of x) := rfl

/-- **Osin's torsion clause, relativized to a free product**: every element of
finite order in the quotient is conjugate to the image of an element of a
factor.

The order of the factor element is not a field of the statement because it is
a consequence of it: if `q = c * factorMap i x * c⁻¹` and `q ^ n = 1` then
`(factorMap i x) ^ n = 1`, which is what
`isPowerTorsionFree_of_torsionIntoFactors` reads off. -/
def TorsionIntoFactors (K : Subgroup (CoprodI G)) [K.Normal] : Prop :=
  ∀ (q : CoprodI G ⧸ K) (n : ℕ), 0 < n → q ^ n = 1 →
    q = 1 ∨ ∃ (i : ι) (x : G i) (c : CoprodI G ⧸ K),
      q = c * factorMap K i x * c⁻¹

/-- **The torsion clause, spent.**  A quotient in which torsion conjugates
into the factors, in which the factors embed, and whose factors are
torsion-free, is torsion-free. -/
theorem isPowerTorsionFree_of_torsionIntoFactors {K : Subgroup (CoprodI G)}
    [K.Normal] (htor : TorsionIntoFactors K)
    (hinj : ∀ i, Function.Injective (factorMap K i))
    (hfree : ∀ i, IsPowerTorsionFree (G i)) :
    IsPowerTorsionFree (CoprodI G ⧸ K) := by
  intro q n hn hq
  rcases htor q n hn hq with h | ⟨i, x, c, rfl⟩
  · exact h
  · have h3 : c * (factorMap K i x) ^ n * c⁻¹ = 1 := by
      rw [← FreeProductCyclic.conj_pow_eq]
      exact hq
    have h2 : (factorMap K i x) ^ n = 1 :=
      FreeProductCyclic.eq_one_of_conj_eq_one h3
    have h5 : x ^ n = 1 := by
      apply hinj i
      rw [map_pow, h2, map_one]
    rw [hfree i x n hn h5]
    simp

/-- **The empty relator family**: the quotient is the free product itself, and
the classification is the free-product torsion theorem. -/
theorem torsionIntoFactors_of_eq_bot {K : Subgroup (CoprodI G)} [K.Normal]
    (hK : K = ⊥) : TorsionIntoFactors K := by
  classical
  intro q n hn hq
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (N := K) q
  have hg : g ^ n = 1 := by
    have h2 : QuotientGroup.mk' K (g ^ n) = 1 := by rw [map_pow]; exact hq
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', hK,
      Subgroup.mem_bot] at h2
    exact h2
  rcases FreeProductCyclic.torsion_conj_into_factor hn hg with
    h | ⟨i, x, c, -, rfl⟩
  · left; rw [h, map_one]
  · refine Or.inr ⟨i, x, QuotientGroup.mk' K c, ?_⟩
    simp only [map_mul, map_inv, factorMap_apply]

/-- **A nondegenerate family**: all relators drawn from inside the factors.
The quotient is a free product of quotient factors
(`FreeProductFactorQuotient.equivQuotients`), so the classification is again
the free-product torsion theorem — transported. -/
theorem torsionIntoFactors_factorNormal (N : ∀ i, Subgroup (G i))
    [∀ i, (N i).Normal] :
    TorsionIntoFactors (FreeProductFactorQuotient.factorNormal N) := by
  classical
  intro q n hn hq
  have hy : (FreeProductFactorQuotient.equivQuotients N q) ^ n = 1 := by
    rw [← map_pow, hq, map_one]
  rcases FreeProductCyclic.torsion_conj_into_factor hn hy with
    h | ⟨i, xbar, c, -, hyc⟩
  · left
    apply (FreeProductFactorQuotient.equivQuotients N).injective
    rw [h, map_one]
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xbar
    refine Or.inr ⟨i, x, (FreeProductFactorQuotient.equivQuotients N).symm c, ?_⟩
    have hq' : q = (FreeProductFactorQuotient.equivQuotients N).symm
        (FreeProductFactorQuotient.equivQuotients N q) :=
      ((FreeProductFactorQuotient.equivQuotients N).symm_apply_apply q).symm
    -- `equivQuotients.symm` is `ofQuotients` and `factorMap` is `mk ∘ of`,
    -- both definitionally, so the computation lemma has the right type already
    have hmid : (FreeProductFactorQuotient.equivQuotients N).symm
        (CoprodI.of (QuotientGroup.mk x : G i ⧸ N i))
        = factorMap (FreeProductFactorQuotient.factorNormal N) i x :=
      FreeProductFactorQuotient.ofQuotients_of N x
    rw [hq', hyc, map_mul, map_mul, map_inv, hmid]

end Quotient

/-! ## 2.  Relators, pieces, and the relative small-cancellation condition -/

section Relators

variable {ι : Type*} [DecidableEq ι] {G : ι → Type*} [∀ i, Group (G i)]
  [∀ i, DecidableEq (G i)]

/-- **Syllable length** of a relator. -/
def wlen (w : Word G) : ℕ := w.toList.length

/-- **A relator is cyclically reduced** when its first and last syllables lie
in different factors — equivalently, when it is spelled by a `NeWord` whose
two end indices differ.  This is the standard hypothesis on a symmetrized
small-cancellation family, and over a free product it is exactly what makes
the relator's conjugates long. -/
def IsCyclicallyReduced (r : Word G) : Prop :=
  ∃ (i j : ι) (u : NeWord G i j), i ≠ j ∧ u.toWord = r

omit [DecidableEq ι] [(i : ι) → DecidableEq (G i)] in
/-- **A cyclically reduced relator has at least two syllables**, so the length
hypothesis of the embedding clause never has to be assumed separately. -/
theorem two_le_wlen {r : Word G} (hr : IsCyclicallyReduced r) : 2 ≤ wlen r := by
  obtain ⟨i, j, u, hij, hu⟩ := hr
  have hlist : u.toList = r.toList := congrArg Word.toList hu
  have h := FreeProductCyclic.two_le_length_of_ne hij u
  rw [hlist] at h
  exact h

/-- **The Greendlinger bound for a single conjugate, unconditionally.**

A conjugate of a cyclically reduced relator is at least as long as the
relator — not merely longer than half of it.  This is the one-conjugate case
of the Greendlinger conclusion, and it needs no small-cancellation hypothesis
at all: it is `FreeProductCyclic.length_le_sylLength_conj`, the statement that
a cyclically reduced word is shortest in its conjugacy class. -/
theorem wlen_le_sylLength_conj {r : Word G} (hr : IsCyclicallyReduced r)
    (c : CoprodI G) :
    wlen r ≤ FreeProductCyclic.sylLength (c * r.prod * c⁻¹) := by
  obtain ⟨i, j, u, hij, hu⟩ := hr
  have hlist : u.toList = r.toList := congrArg Word.toList hu
  have hprod : u.prod = r.prod := congrArg Word.prod hu
  have h := FreeProductCyclic.length_le_sylLength_conj hij u c
  rw [hlist, hprod] at h
  exact h

omit [DecidableEq ι] [(i : ι) → DecidableEq (G i)] in
/-- The same for a conjugate of the *inverse* of a relator: symmetrized
families contain both, and inversion preserves cyclic reducedness. -/
theorem isCyclicallyReduced_inv {r : Word G} (hr : IsCyclicallyReduced r) :
    ∃ s : Word G, IsCyclicallyReduced s ∧ s.prod = (r.prod)⁻¹ ∧ wlen s = wlen r := by
  obtain ⟨i, j, u, hij, hu⟩ := hr
  refine ⟨u.inv.toWord, ⟨j, i, u.inv, hij.symm, rfl⟩, ?_, ?_⟩
  · have h1 : u.inv.prod = (u.prod)⁻¹ := NeWord.inv_prod u
    have h2 : u.prod = r.prod := congrArg Word.prod hu
    rw [← h2]
    exact h1
  · have hlist : u.toList = r.toList := congrArg Word.toList hu
    have h := FreeProductCyclic.toList_length_inv u
    rw [hlist] at h
    exact h

/-- **Cyclically reduced relators exist**: two nontrivial syllables from
different factors spell one.  Nothing above is a hypothesis about an empty
class. -/
def pairWord {i j : ι} (hij : i ≠ j) {x : G i} {y : G j} (hx : x ≠ 1)
    (hy : y ≠ 1) : Word G :=
  ((NeWord.singleton x hx).append hij (NeWord.singleton y hy)).toWord

omit [DecidableEq ι] [(i : ι) → DecidableEq (G i)] in
theorem isCyclicallyReduced_pairWord {i j : ι} (hij : i ≠ j) {x : G i} {y : G j}
    (hx : x ≠ 1) (hy : y ≠ 1) : IsCyclicallyReduced (pairWord hij hx hy) :=
  ⟨i, j, (NeWord.singleton x hx).append hij (NeWord.singleton y hy), hij, rfl⟩

omit [DecidableEq ι] [(i : ι) → DecidableEq (G i)] in
@[simp] theorem wlen_pairWord {i j : ι} (hij : i ≠ j) {x : G i} {y : G j}
    (hx : x ≠ 1) (hy : y ≠ 1) : wlen (pairWord hij hx hy) = 2 := rfl

/-- The normal subgroup a relator family presents. -/
def relatorSubgroup (R : Set (Word G)) : Subgroup (CoprodI G) :=
  Subgroup.normalClosure (Word.prod '' R)

/-- Registered for the same reason as
`FreeProductFactorQuotient.factorNormal_normal`: instance search stops at the
`def`, and the quotient needs the instance to be a group. -/
instance relatorSubgroup_normal (R : Set (Word G)) :
    (relatorSubgroup R).Normal :=
  Subgroup.normalClosure_normal

/-- **A piece**: a common initial segment of two distinct relators of the
symmetrized family.  As over a free group, rotations being present in the
family makes prefixes catch occurrences at every position. -/
def IsPiece (R : Set (Word G)) (p : List (Σ i, G i)) : Prop :=
  ∃ r₁ ∈ R, ∃ r₂ ∈ R, r₁ ≠ r₂ ∧ p <+: r₁.toList ∧ p <+: r₂.toList

/-- **The relative metric condition `C'(λ)`**, syllables counted. -/
def MetricSmallCancellation (R : Set (Word G)) (lam : ℚ) : Prop :=
  ∀ p, IsPiece R p → ∀ r ∈ R, p <+: r.toList →
    (p.length : ℚ) < lam * (wlen r : ℚ)

omit [DecidableEq ι] [(i : ι) → DecidableEq (G i)] in
/-- **`C'(1/6)` in `ℕ`.**  Clearing the denominator once, exactly as
`Sofic.GreendlingerPiece.six_mul_length_lt_of_isPiece` does over a free
group, so that a future proof of the Greendlinger conclusion never leaves
`omega`'s reach. -/
theorem six_mul_length_lt_of_isPiece {R : Set (Word G)}
    (hmetric : MetricSmallCancellation R (1 / 6)) {p : List (Σ i, G i)}
    {r : Word G} (hp : IsPiece R p) (hr : r ∈ R) (hpre : p <+: r.toList) :
    6 * p.length < wlen r := by
  have h := hmetric p hp r hr hpre
  have h6 : (6 : ℚ) * (p.length : ℚ) < (wlen r : ℚ) := by linarith
  exact_mod_cast h6

/-- **The relative Greendlinger conclusion**: a nontrivial element of the
relator subgroup has, inside its normal form, a contiguous block making up
more than half of some relator read cyclically. -/
def GreendlingerConclusion (R : Set (Word G)) : Prop :=
  ∀ g : CoprodI G, g ≠ 1 → g ∈ relatorSubgroup R →
    ∃ r ∈ R, ∃ s : List (Σ i, G i),
      s <:+: (Word.equiv g).toList ∧ s <:+: r.toList ++ r.toList ∧
        s.length ≤ wlen r ∧ wlen r < 2 * s.length

/-- **The length form of the Greendlinger conclusion**, which is all the
embedding clause consumes: a nontrivial element of the relator subgroup is
longer than half of some relator.

Separating it from the subword form matters.  The subword form is what a
diagram argument produces; the length form is what the theorem needs, it is
strictly weaker, and — for a single conjugate — it is *provable outright*
(`wlen_le_sylLength_conj`), with the sharp constant `1` rather than `1/2`. -/
def GreendlingerLengthBound (R : Set (Word G)) : Prop :=
  ∀ g : CoprodI G, g ≠ 1 → g ∈ relatorSubgroup R →
    ∃ r ∈ R, wlen r < 2 * FreeProductCyclic.sylLength g

/-- The subword form implies the length form.  The Greendlinger block is a
subword of the normal form, so it is no longer than the normal form. -/
theorem greendlingerLengthBound_of_conclusion {R : Set (Word G)}
    (hG : GreendlingerConclusion R) : GreendlingerLengthBound R := by
  intro g hg hmem
  obtain ⟨r, hr, s, hs1, -, -, hlt⟩ := hG g hg hmem
  refine ⟨r, hr, ?_⟩
  have h1 : s.length ≤ (Word.equiv g).toList.length := hs1.sublist.length_le
  simp only [FreeProductCyclic.sylLength]
  omega

/-- Nontrivial elements of the relator subgroup are longer than half of some
relator. -/
theorem sylLength_lt_of_mem_relatorSubgroup {R : Set (Word G)}
    (hG : GreendlingerConclusion R) {g : CoprodI G} (hg : g ≠ 1)
    (hmem : g ∈ relatorSubgroup R) :
    ∃ r ∈ R, wlen r < 2 * FreeProductCyclic.sylLength g :=
  greendlingerLengthBound_of_conclusion hG g hg hmem

/-- **The peripheral factor stays embedded.**

A nontrivial element of a factor is a word of one syllable, so a relator of
two syllables or more is already too long to be more than half-contained in
it.  Nothing about the peripheral factor is special: this is every factor,
and the hypothesis is the length form, not the subword form. -/
theorem factorMap_injective_of_lengthBound {R : Set (Word G)}
    (hG : GreendlingerLengthBound R) (hlong : ∀ r ∈ R, 2 ≤ wlen r) (i : ι) :
    Function.Injective (factorMap (relatorSubgroup R) i) := by
  intro x y hxy
  by_contra hne
  have hxy1 : x * y⁻¹ ≠ 1 := fun h => hne (mul_inv_eq_one.mp h)
  have hof : CoprodI.of (x * y⁻¹) ≠ (1 : CoprodI G) := by
    intro h
    exact hxy1 (CoprodI.of_injective i (by rw [h, map_one]))
  have hmem : CoprodI.of (x * y⁻¹) ∈ relatorSubgroup R := by
    rw [← QuotientGroup.eq_one_iff]
    have h1 : factorMap (relatorSubgroup R) i (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    exact h1
  obtain ⟨r, hr, hlt⟩ := hG _ hof hmem
  have h1 := FreeProductCyclic.sylLength_of_le_one (x * y⁻¹)
  have h2 := hlong r hr
  omega

/-- The embedding clause with the standard small-cancellation hypothesis in
place of a bare length bound: **cyclically reduced relators are automatically
long enough**. -/
theorem factorMap_injective_of_cyclicallyReduced {R : Set (Word G)}
    (hG : GreendlingerLengthBound R)
    (hcyc : ∀ r ∈ R, IsCyclicallyReduced r) (i : ι) :
    Function.Injective (factorMap (relatorSubgroup R) i) :=
  factorMap_injective_of_lengthBound hG (fun r hr => two_le_wlen (hcyc r hr)) i

/-- The embedding clause from the subword form, for callers that have it. -/
theorem factorMap_injective {R : Set (Word G)} (hG : GreendlingerConclusion R)
    (hlong : ∀ r ∈ R, 2 ≤ wlen r) (i : ι) :
    Function.Injective (factorMap (relatorSubgroup R) i) :=
  factorMap_injective_of_lengthBound (greendlingerLengthBound_of_conclusion hG)
    hlong i

/-- The one-syllable relator spelling a nontrivial element of a factor. -/
def letterWord {i : ι} (x : G i) (hx : x ≠ 1) : Word G :=
  Word.cons x Word.empty (by simp [Word.fstIdx]) hx

omit [DecidableEq ι] [(i : ι) → DecidableEq (G i)] in
@[simp] theorem letterWord_toList {i : ι} (x : G i) (hx : x ≠ 1) :
    (letterWord x hx).toList = [⟨i, x⟩] := rfl

omit [DecidableEq ι] [(i : ι) → DecidableEq (G i)] in
@[simp] theorem wlen_letterWord {i : ι} (x : G i) (hx : x ≠ 1) :
    wlen (letterWord x hx) = 1 := rfl

omit [DecidableEq ι] [(i : ι) → DecidableEq (G i)] in
/-- **The two-syllable hypothesis of `factorMap_injective` is exactly right.**
A relator of a single syllable *is* a nontrivial element of a factor, and it
dies in the quotient, so the embedding clause fails for it.  There is no
weaker length hypothesis under which the clause could hold. -/
theorem factorMap_not_injective_of_singleton {R : Set (Word G)} {r : Word G}
    (hr : r ∈ R) {i : ι} {x : G i} (hx : r.toList = [⟨i, x⟩]) :
    ¬ Function.Injective (factorMap (relatorSubgroup R) i) := by
  intro hinj
  have hx1 : x ≠ 1 := r.ne_one ⟨i, x⟩ (by rw [hx]; simp)
  have hprod : r.prod = CoprodI.of x := by simp [Word.prod, hx]
  have hmem : CoprodI.of x ∈ relatorSubgroup R := by
    rw [← hprod]
    exact Subgroup.subset_normalClosure ⟨r, hr, rfl⟩
  have h1 : factorMap (relatorSubgroup R) i x = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hmem
  have h2 : factorMap (relatorSubgroup R) i x
      = factorMap (relatorSubgroup R) i 1 := by
    rw [h1, map_one]
  exact hx1 (hinj h2)

omit [DecidableEq ι] [(i : ι) → DecidableEq (G i)] in
/-- The failure is exhibited, not merely permitted: killing one nontrivial
element of a factor is a relator family, and it collapses that factor. -/
theorem factorMap_not_injective_letterWord {i : ι} (x : G i) (hx : x ≠ 1) :
    ¬ Function.Injective
      (factorMap (relatorSubgroup ({letterWord x hx} : Set (Word G))) i) :=
  factorMap_not_injective_of_singleton (Set.mem_singleton _)
    (letterWord_toList x hx)

/-- **Osin's conclusion pair over `U * H`.**  A small-cancellation quotient of
a free product of torsion-free groups keeps every factor — in particular the
peripheral one — embedded, and is torsion-free. -/
theorem osin_conclusion {R : Set (Word G)}
    (hcyc : ∀ r ∈ R, IsCyclicallyReduced r) (hG : GreendlingerLengthBound R)
    (htor : TorsionIntoFactors (relatorSubgroup R))
    (hfree : ∀ i, IsPowerTorsionFree (G i)) (i₀ : ι) :
    Function.Injective (factorMap (relatorSubgroup R) i₀) ∧
      IsPowerTorsionFree (CoprodI G ⧸ relatorSubgroup R) :=
  ⟨factorMap_injective_of_cyclicallyReduced hG hcyc i₀,
    isPowerTorsionFree_of_torsionIntoFactors htor
      (factorMap_injective_of_cyclicallyReduced hG hcyc) hfree⟩

/-- The same from the subword form of the Greendlinger conclusion. -/
theorem osin_conclusion_of_greendlinger {R : Set (Word G)}
    (hcyc : ∀ r ∈ R, IsCyclicallyReduced r) (hG : GreendlingerConclusion R)
    (htor : TorsionIntoFactors (relatorSubgroup R))
    (hfree : ∀ i, IsPowerTorsionFree (G i)) (i₀ : ι) :
    Function.Injective (factorMap (relatorSubgroup R) i₀) ∧
      IsPowerTorsionFree (CoprodI G ⧸ relatorSubgroup R) :=
  osin_conclusion hcyc (greendlingerLengthBound_of_conclusion hG) htor hfree i₀

/-! ### The degenerate relator families, discharged -/

omit [DecidableEq ι] [(i : ι) → DecidableEq (G i)] in
theorem relatorSubgroup_empty : relatorSubgroup (∅ : Set (Word G)) = ⊥ := by
  refine le_antisymm ?_ bot_le
  apply Subgroup.normalClosure_le_normal
  simp

theorem greendlingerConclusion_of_eq_bot {R : Set (Word G)}
    (hR : relatorSubgroup R = ⊥) : GreendlingerConclusion R := by
  intro g hg hmem
  rw [hR, Subgroup.mem_bot] at hmem
  exact absurd hmem hg

theorem greendlingerConclusion_empty :
    GreendlingerConclusion (∅ : Set (Word G)) :=
  greendlingerConclusion_of_eq_bot relatorSubgroup_empty

theorem greendlingerLengthBound_of_eq_bot {R : Set (Word G)}
    (hR : relatorSubgroup R = ⊥) : GreendlingerLengthBound R := by
  intro g hg hmem
  rw [hR, Subgroup.mem_bot] at hmem
  exact absurd hmem hg

theorem greendlingerLengthBound_empty :
    GreendlingerLengthBound (∅ : Set (Word G)) :=
  greendlingerLengthBound_of_eq_bot relatorSubgroup_empty

/-- **Nothing above is vacuous.**  For the empty relator family both clauses
hold, and their content is that `U * H` contains `U` and is torsion-free. -/
theorem osin_conclusion_empty (hfree : ∀ i, IsPowerTorsionFree (G i)) (i₀ : ι) :
    Function.Injective (factorMap (relatorSubgroup (∅ : Set (Word G))) i₀) ∧
      IsPowerTorsionFree (CoprodI G ⧸ relatorSubgroup (∅ : Set (Word G))) :=
  osin_conclusion (by simp) greendlingerLengthBound_empty
    (torsionIntoFactors_of_eq_bot relatorSubgroup_empty) hfree i₀

/-! ## 3.  An unconditional embedding criterion, with no small cancellation

Keeping the peripheral factor is not the exclusive property of
small-cancellation families.  If every relator dies under the retraction of
the free product onto the peripheral factor, that factor is a retract of the
quotient, hence embedded — and the argument is three lines with no word
combinatorics at all. -/

/-- The retraction of a free product onto one factor. -/
def retraction (i₀ : ι) : CoprodI G →* G i₀ :=
  CoprodI.lift (Pi.mulSingle i₀ (MonoidHom.id (G i₀)))

omit [(i : ι) → DecidableEq (G i)] in
@[simp] theorem retraction_of_same (i₀ : ι) (x : G i₀) :
    retraction i₀ (CoprodI.of x) = x := by
  simp only [retraction, CoprodI.lift_of, Pi.mulSingle_eq_same,
    MonoidHom.id_apply]

omit [(i : ι) → DecidableEq (G i)] in
/-- **A retraction criterion for the embedding clause.** -/
theorem factorMap_injective_of_retraction {R : Set (Word G)} (i₀ : ι)
    (hR : ∀ r ∈ R, retraction i₀ r.prod = 1) :
    Function.Injective (factorMap (relatorSubgroup R) i₀) := by
  have hle : relatorSubgroup R ≤ (retraction i₀).ker := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨r, hr, rfl⟩
    exact MonoidHom.mem_ker.mpr (hR r hr)
  intro x y hxy
  have h := congrArg
    (QuotientGroup.lift (relatorSubgroup R) (retraction i₀) hle) hxy
  simpa [factorMap] using h

end Relators

end OsinSmallCancellation
end GroupApproximation
