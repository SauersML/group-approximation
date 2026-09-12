import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientUnitsKappaProof
import GroupApproximation.Algebra.PeirceElementaryFactorization

/-!
# Item (a), the Steinberg displays, and `diag(v,1,…,1) ∈ EL_n(R)`

Printed sentences of the proof of `thm:mf-quotient-units` that the census
carried only in part.

## Item (a), one carrier per census sentence

The census splits printed item (a) at "Then", into

> (a) There are orthogonal idempotents `e_1, …, e_m` with sum `1`, `m ≥ 4`,
> such that `e_1, …, e_{m-1}` are pairwise equivalent and `e_m` is equivalent to
> an idempotent `f ≤ e_1`.

and

> Then `R` is the ring of `m × m` matrices over `T = e_1Re_1`, with identity
> `diag(1_T, …, 1_T, f)`, whose last column has entries in `Tf` and whose last
> row has entries in `fT`, and every unit `u` of `R` factors as `u = gvh` with
> `g` and `h` products of elementary matrices `e_{ij}(x)` of this matrix ring
> and `v = e_1 + (1-e_1)v(1-e_1)`.

`Algebra/PeirceElementaryFactorization.lean` proves both at once, as the single
closed proposition `PrintedItemA`.  That is the whole sentence and nothing here
improves on it; what this module adds is the split, so that each census key has
a carrier stating exactly its own sentence.

The split is not merely cosmetic in the second half.  `PrintedItemA` asserts the
matrix identification and the factorization *for the decomposition it builds*.
`manuscriptSentence_itemAMatrixRingAndFactorization` asserts them for **every**
decomposition meeting item (a)'s hypotheses, which is what the printed "Then"
says: the printed sentence is about any such `e_1, …, e_m`, not about one
chosen family.  It is `printedTwistedPeirceMatrixRing` for the ring and
`printedItemAShape` for the factorization, which are already stated at that
generality.

## The Steinberg displays (tex lines 1227--1233)

> for distinct `i, j ≤ m-1`,
> `e_{im}(x) = [e_{ij}(1), e_{jm}(x)]`, `e_{mj}(x) = [e_{mi}(x), e_{ij}(1)]`
> are products of an element of `EL_{m-1}(T)` and a conjugate of its inverse,
> so they lie in the normal subgroup `N` as well.

Both displayed identities and the printed conclusion are carried here.  The
identities are `elementaryUnit_commutator`, the general elementary commutator
relation `[x_{ij}(a), x_{jk}(b)] = x_{ik}(ab)`; the conclusion is that a normal
subgroup containing *one* of the two factors contains the commutator, which is
the printed reason read literally --- `⁅A,B⁆ = A · (B A⁻¹ B⁻¹)` when `A` is the
one in `N`, and `⁅A,B⁆ = (A B A⁻¹) · B⁻¹` when `B` is.

The two displays use opposite factors: the first has `e_{ij}(1)` on the left,
the second has it on the right.  Both are covered, so the printed "as well"
needs no separate argument.

### Why this is stated over an arbitrary ring rather than inside the twisted ring

`Algebra/PeirceTwistedMatrixRing.lean` builds the printed `m × m` matrix ring
over `T = e_1Re_1` with identity `diag(1_T, …, 1_T, f)` as the corner of
`M_ι(T)` at that diagonal matrix.  Everything below is stated for `M_ι(S)` over
an arbitrary ring `S`, and, in `steinbergCommutatorMemNormal`, for an arbitrary
ring outright.  That is not a weakening: the twisting constrains which `x` may
appear in the last row and column, and both the identity and the membership
conclusion hold for every `x` whatever, so the general statement contains the
twisted one.  The ring form applies to the twisted ring verbatim, with `1`
read as the printed `diag(1_T, …, 1_T, f)` and `a`, `b` the two square-zero
matrix units: the printed `e_{ij}(x)` is `1 + x E_{ij}`, and the three
hypotheses `a² = 0`, `b² = 0`, `ba = 0` are the matrix-unit relations
`E_{ij}E_{ij} = 0`, `E_{jm}E_{jm} = 0`, `E_{jm}E_{ij} = 0`.

## `diag(v,1,…,1) ∈ EL_n(R)` (tex line 1237)

> By the definition of `K_1`, `diag(v,1,…,1) ∈ EL_n(R)` for some `n ≥ 2`.

`KappaProof.exists_diagonal_mem_commutator` gives the same conclusion with the
commutator subgroup in place of `EL_n(R)`, at some rank `n > 0`.  The printed
`EL_n(R)` form follows, and this module derives it.  Two steps were missing:

* the rank has to be pushed up to at least `2`, which is `glStab` along
  `n ≤ max n 2` together with `glStab_one_eq_diagAt` at both ends;
* at rank at least `2` the two subgroups coincide --- `commutator = EL_n(R)`
  for a countable purely infinite simple ring is
  `MFQuotientMatrices.mfHomKernel_matrixUnits_eq`.

So the printed sentence holds as printed, `n ≥ 2` included.
-/

namespace GroupApproximation
namespace MFQuotientUnitsItemA

open MFQuotientUnits AlgebraicK RankNElimination
open scoped commutatorElement

/-! ## The Steinberg displays -/

section Steinberg

variable {S : Type*} [Ring S]

/-- **The printed reason, at a normal subgroup.**

> … are products of an element of `EL_{m-1}(T)` and a conjugate of its inverse,
> so they lie in the normal subgroup `N` as well.

A normal subgroup containing either factor contains the commutator: with `A` in
`N` the commutator is `A · (B A⁻¹ B⁻¹)`, and with `B` in `N` it is
`(A B A⁻¹) · B⁻¹`.  Stated for an arbitrary group, since that is all the
printed reason uses. -/
theorem commutator_mem_of_either {G : Type*} [Group G] (N : Subgroup G)
    [hN : N.Normal] (A B : G) (h : A ∈ N ∨ B ∈ N) : ⁅A, B⁆ ∈ N := by
  rcases h with hA | hB
  · have heq : A * B * A⁻¹ * B⁻¹ = A * (B * A⁻¹ * B⁻¹) := by group
    rw [commutatorElement_def, heq]
    exact N.mul_mem hA (hN.conj_mem _ (N.inv_mem hA) B)
  · have heq : A * B * A⁻¹ * B⁻¹ = (A * B * A⁻¹) * B⁻¹ := by group
    rw [commutatorElement_def, heq]
    exact N.mul_mem (hN.conj_mem _ hB A) (N.inv_mem hB)

/-- **The two printed Steinberg displays.**

> `e_{im}(x) = [e_{ij}(1), e_{jm}(x)]`, `e_{mj}(x) = [e_{mi}(x), e_{ij}(1)]`

Both identities, over an arbitrary ring and an arbitrary finite index type, for
every `x`.  In the printed application `i` and `j` are the two indices below
`m`, so `e_{ij}(1)` is the factor lying in `EL_{m-1}(T)`. -/
theorem manuscriptSentence_steinbergDisplays {ι : Type*} [Fintype ι]
    [DecidableEq ι] (i j m : ι) (hij : i ≠ j) (hjm : j ≠ m) (him : i ≠ m)
    (hmi : m ≠ i) (hmj : m ≠ j) (x : S) :
    ⁅elementaryUnit i j hij (1 : S), elementaryUnit j m hjm x⁆
        = elementaryUnit i m him x ∧
      ⁅elementaryUnit m i hmi x, elementaryUnit i j hij (1 : S)⁆
        = elementaryUnit m j hmj x := by
  constructor
  · simpa using elementaryUnit_commutator i j m hij hjm him (1 : S) x
  · simpa using elementaryUnit_commutator m i j hmi hij hmj x (1 : S)

/-- **The printed sentence in full**: the two displays, and the conclusion that
both lie in `N`.

The only hypothesis is that `N` is normal and contains `e_{ij}(1)`, the factor
the print locates in `EL_{m-1}(T)`; nothing is assumed about `e_{jm}(x)` or
`e_{mi}(x)`, which is exactly why the printed argument needs the commutator
form. -/
theorem manuscriptSentence_steinbergDisplaysMemNormal {ι : Type*} [Fintype ι]
    [DecidableEq ι] (i j m : ι) (hij : i ≠ j) (hjm : j ≠ m) (him : i ≠ m)
    (hmi : m ≠ i) (hmj : m ≠ j) (x : S)
    (N : Subgroup (Matrix ι ι S)ˣ) [N.Normal]
    (hone : elementaryUnit i j hij (1 : S) ∈ N) :
    ⁅elementaryUnit i j hij (1 : S), elementaryUnit j m hjm x⁆
        = elementaryUnit i m him x ∧
      ⁅elementaryUnit m i hmi x, elementaryUnit i j hij (1 : S)⁆
        = elementaryUnit m j hmj x ∧
      elementaryUnit i m him x ∈ N ∧ elementaryUnit m j hmj x ∈ N := by
  obtain ⟨h1, h2⟩ :=
    manuscriptSentence_steinbergDisplays (S := S) i j m hij hjm him hmi hmj x
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [← h1]
    exact commutator_mem_of_either N _ _ (Or.inl hone)
  · rw [← h2]
    exact commutator_mem_of_either N _ _ (Or.inr hone)

end Steinberg

/-- **The same, at the ring level**, which is the form that applies inside the
twisted `m × m` matrix ring of item (a).

`1` is the printed identity `diag(1_T, …, 1_T, f)` of that ring, `a` and `b`
are the two square-zero matrix units, and `1 + a * b` is the printed
`e_{im}(x)` or `e_{mj}(x)`.  `Peirce.OneAddIn N y` says some unit of `N` has
ring value `1 + y`, which is how the printed `e`'s are recognised without
choosing an inverse.  Stated at `Type` because `Peirce.oneAddIn_product` is. -/
theorem steinbergCommutatorMemNormal {S : Type} [Ring S] {N : Subgroup Sˣ}
    [N.Normal] {a b : S}
    (haa : a * a = 0) (hbb : b * b = 0) (hba : b * a = 0)
    (hmem : Peirce.OneAddIn N a ∨ Peirce.OneAddIn N b) :
    Peirce.OneAddIn N (a * b) :=
  Peirce.oneAddIn_product haa hbb hba hmem

/-! ## `diag(v,1,…,1) ∈ EL_n(R)` for some `n ≥ 2` -/

section Diagonal

variable (R : Type) [Ring R] [Countable R]

omit [Countable R] in
/-- Padding is functorial: stabilising twice is stabilising once.  The
`DirectedSystem` instance on the general linear groups proves the same thing;
it is restated here as a plain equation so it can be rewritten with. -/
theorem glStab_glStab {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (x : (Matrix (Fin a) (Fin a) R)ˣ) :
    glStab R b c hbc (glStab R a b hab x) = glStab R a c (hab.trans hbc) x := by
  apply Units.ext
  simp only [glStab_val]
  exact stabMatrix_stabMatrix hab _ _

omit [Countable R] in
/-- Padding carries `diag(u,1,…,1)` at one rank to `diag(u,1,…,1)` at any
larger rank: both are the image of the `1 × 1` matrix of `u`. -/
theorem glStab_diagAt {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hnm : n ≤ m)
    (u : Rˣ) :
    glStab R n m hnm (diagAt (⟨0, hn⟩ : Fin n) u) = diagAt (⟨0, hm⟩ : Fin m) u := by
  rw [← glStab_one_eq_diagAt n hn (by omega) u,
    glStab_glStab R (by omega : 1 ≤ n) hnm,
    glStab_one_eq_diagAt m hm (by omega) u]

/-- **The printed sentence.**

> By the definition of `K_1`, `diag(v,1,…,1) ∈ EL_n(R)` for some `n ≥ 2`.

`KappaProof.exists_diagonal_mem_commutator` produces the same statement with
the commutator subgroup and only `n > 0`.  Pushing the rank to `max n 2` and
using `commutator = EL_n(R)` at rank at least `2` gives the sentence as
printed. -/
theorem manuscriptSentence_diagInElementary
    (hR : IsPurelyInfiniteSimpleRing R) (v : Rˣ) (hv : kappa R v = 1) :
    ∃ (n : ℕ) (hn : 2 ≤ n),
      diagAt (⟨0, by omega⟩ : Fin n) v ∈ elementaryGroup (Fin n) R := by
  obtain ⟨n, hn, hdiag⟩ := KappaProof.exists_diagonal_mem_commutator R hR v hv
  refine ⟨max n 2, le_max_right n 2, ?_⟩
  have hmax : 0 < max n 2 := lt_of_lt_of_le hn (le_max_left n 2)
  have hstab := KappaProof.map_mem_commutator
    (glStab R n (max n 2) (le_max_left n 2)) hdiag
  rw [glStab_diagAt R hn hmax (le_max_left n 2) v] at hstab
  rw [← (MFQuotientMatrices.mfHomKernel_matrixUnits_eq R hR (max n 2)
    (le_max_right n 2)).2]
  exact hstab

/-- The printed sentence with the commutator form beside it, so that the two
readings of `diag(v,1,…,1)` are visible together. -/
theorem manuscriptSentence_diagInElementaryAndCommutator
    (hR : IsPurelyInfiniteSimpleRing R) (v : Rˣ) (hv : kappa R v = 1) :
    ∃ (n : ℕ) (hn : 2 ≤ n),
      diagAt (⟨0, by omega⟩ : Fin n) v ∈ elementaryGroup (Fin n) R ∧
        diagAt (⟨0, by omega⟩ : Fin n) v
          ∈ commutator (Matrix (Fin n) (Fin n) R)ˣ := by
  obtain ⟨n, hn, hmem⟩ := manuscriptSentence_diagInElementary R hR v hv
  refine ⟨n, hn, hmem, ?_⟩
  rw [(MFQuotientMatrices.mfHomKernel_matrixUnits_eq R hR n hn).2]
  exact hmem

end Diagonal

/-! ## The two sentences as closed propositions -/

/-- **The Steinberg-display sentence, closed.** -/
def PrintedSteinbergDisplays : Prop :=
  ∀ (S : Type) [Ring S] (ι : Type) [Fintype ι] [DecidableEq ι]
    (i j m : ι) (hij : i ≠ j) (hjm : j ≠ m) (him : i ≠ m) (hmi : m ≠ i)
    (hmj : m ≠ j) (x : S) (N : Subgroup (Matrix ι ι S)ˣ), N.Normal →
      elementaryUnit i j hij (1 : S) ∈ N →
        ⁅elementaryUnit i j hij (1 : S), elementaryUnit j m hjm x⁆
            = elementaryUnit i m him x ∧
          ⁅elementaryUnit m i hmi x, elementaryUnit i j hij (1 : S)⁆
            = elementaryUnit m j hmj x ∧
          elementaryUnit i m him x ∈ N ∧ elementaryUnit m j hmj x ∈ N

theorem manuscriptSteinbergDisplays : PrintedSteinbergDisplays := by
  intro S _ ι _ _ i j m hij hjm him hmi hmj x N hN hone
  letI := hN
  exact manuscriptSentence_steinbergDisplaysMemNormal i j m hij hjm him hmi hmj
    x N hone

/-- **The `diag(v,1,…,1) ∈ EL_n(R)` sentence, closed.** -/
def PrintedDiagInElementary : Prop :=
  ∀ (R : Type) [Ring R] [Countable R], IsPurelyInfiniteSimpleRing R →
    ∀ (v : Rˣ), kappa R v = 1 →
      ∃ (n : ℕ) (hn : 2 ≤ n),
        diagAt (⟨0, by omega⟩ : Fin n) v ∈ elementaryGroup (Fin n) R

theorem manuscriptDiagInElementary : PrintedDiagInElementary := by
  intro R _ _ hR v hv
  exact manuscriptSentence_diagInElementary R hR v hv

/-! ## Item (a), sentence by sentence -/

/-- **Printed item (a), first sentence.**

> There are orthogonal idempotents `e_1, …, e_m` with sum `1`, `m ≥ 4`, such
> that `e_1, …, e_{m-1}` are pairwise equivalent and `e_m` is equivalent to an
> idempotent `f ≤ e_1`.

Every clause: orthogonality, sum `1`, pairwise equivalence off the last index,
and the last index equivalent to a sub-idempotent of the first. -/
def PrintedItemADecomposition : Prop :=
  ∀ (R : Type) [Ring R], IsPurelyInfiniteSimpleRing R →
    ∀ m : ℕ, 4 ≤ m →
      ∃ (e : Fin m → R) (_ : ∀ i, IsIdempotentElem (e i)) (i₀ last : Fin m)
        (f : R), IsIdempotentElem f ∧ IdempotentLE f (e i₀) ∧ i₀ ≠ last ∧
        (∀ i j : Fin m, i ≠ j → e i * e j = 0) ∧ (∑ i, e i = 1) ∧
        (∀ i j : Fin m, i ≠ last → j ≠ last →
          IsEquivalentIdempotent R (e i) (e j)) ∧
        IsEquivalentIdempotent R (e last) f

theorem manuscriptSentence_itemADecomposition : PrintedItemADecomposition := by
  intro R _ hR m hm
  obtain ⟨e, hidem, i₀, last, f, hfi, hfle, hne, horth, hsum, hpair, hlast, -, -⟩ :=
    printedItemA R hR m hm
  exact ⟨e, hidem, i₀, last, f, hfi, hfle, hne, horth, hsum, hpair, hlast⟩

/-- **Printed item (a), second sentence.**

> Then `R` is the ring of `m × m` matrices over `T = e_1Re_1`, with identity
> `diag(1_T, …, 1_T, f)`, whose last column has entries in `Tf` and whose last
> row has entries in `fT`, and every unit `u` of `R` factors as `u = gvh` with
> `g` and `h` products of elementary matrices `e_{ij}(x)` of this matrix ring
> and `v = e_1 + (1-e_1)v(1-e_1)`.

Quantified over **every** decomposition meeting item (a)'s hypotheses, which is
what the printed "Then" means: the sentence is about any such `e_1, …, e_m`.
The three conjuncts are the printed `Tf` / `fT` support conditions, the printed
matrix identification, and the printed factorization. -/
def PrintedItemAMatrixRingAndFactorization : Prop :=
  ∀ (R : Type) [Ring R], IsPurelyInfiniteSimpleRing R →
    ∀ (m : ℕ), 4 ≤ m → ∀ (e : Fin m → R) (hidem : ∀ i, IsIdempotentElem (e i)),
      (∀ i j : Fin m, i ≠ j → e i * e j = 0) → (∑ i, e i = 1) →
      ∀ i₀ last : Fin m, i₀ ≠ last →
        (∀ i j : Fin m, i ≠ last → j ≠ last →
          IsEquivalentIdempotent R (e i) (e j)) →
        ∀ (f : R) (hfi : IsIdempotentElem f) (hfle : IdempotentLE f (e i₀)),
          IsEquivalentIdempotent R (e last) f →
            (∀ M : Matrix (Fin m) (Fin m) (Corner R (e i₀) (hidem i₀)),
                M ∈ cornerNonUnitalSubring
                    (twistedIdentity (hidem i₀) hfle last)
                    (isIdempotentElem_twistedIdentity (hidem i₀) hfi hfle last) ↔
                  ((∀ i, M i last * ⟨f, hfle.1, hfle.2⟩ = M i last) ∧
                    ∀ j, (⟨f, hfle.1, hfle.2⟩ : Corner R (e i₀) (hidem i₀))
                      * M last j = M last j)) ∧
              Nonempty (R ≃+*
                Corner (Matrix (Fin m) (Fin m) (Corner R (e i₀) (hidem i₀)))
                  (twistedIdentity (hidem i₀) hfle last)
                  (isIdempotentElem_twistedIdentity (hidem i₀) hfi hfle last)) ∧
              ∀ u : Rˣ, ∃ v : Rˣ,
                FactorsThrough (peirceElementarySubgroup e) u v ∧
                (v : R) = e i₀ + (1 - e i₀) * (v : R) * (1 - e i₀)

theorem manuscriptSentence_itemAMatrixRingAndFactorization :
    PrintedItemAMatrixRingAndFactorization := by
  intro R _ hR m hm e hidem horth hsum i₀ last hne hpair f hfi hfle hlast
  obtain ⟨hsupp, hiso⟩ :=
    printedTwistedPeirceMatrixRing R (Fin m) e hidem horth hsum i₀ last hne
      hpair f hfi hfle hlast
      (isIdempotentElem_twistedIdentity (hidem i₀) hfi hfle last)
  exact ⟨hsupp, hiso,
    printedItemAShape R hR m hm e hidem horth hsum i₀ last hne hpair f hfi hfle
      hlast⟩

/-- **Printed item (a), both sentences.**

Not a restatement of `PrintedItemA`: the second conjunct is quantified over
every decomposition meeting item (a)'s hypotheses, where `PrintedItemA` asserts
the same clauses for the one decomposition it builds. -/
def PrintedItemASentences : Prop :=
  PrintedItemADecomposition ∧ PrintedItemAMatrixRingAndFactorization

theorem manuscriptSentence_itemA : PrintedItemASentences :=
  ⟨manuscriptSentence_itemADecomposition,
    manuscriptSentence_itemAMatrixRingAndFactorization⟩

end MFQuotientUnitsItemA
end GroupApproximation

/-! ### Axiom audit -/

open GroupApproximation.MFQuotientUnitsItemA

#audit_axioms commutator_mem_of_either
#audit_axioms manuscriptSentence_steinbergDisplays
#audit_axioms manuscriptSentence_steinbergDisplaysMemNormal
#audit_axioms steinbergCommutatorMemNormal
#audit_axioms glStab_glStab
#audit_axioms glStab_diagAt
#audit_axioms manuscriptSentence_diagInElementary
#audit_axioms manuscriptSentence_diagInElementaryAndCommutator
#audit_closed_axioms GroupApproximation.MFQuotientUnitsItemA.manuscriptSteinbergDisplays
#audit_closed_axioms GroupApproximation.MFQuotientUnitsItemA.manuscriptDiagInElementary
#audit_closed_axioms
  GroupApproximation.MFQuotientUnitsItemA.manuscriptSentence_itemADecomposition
#audit_closed_axioms
  GroupApproximation.MFQuotientUnitsItemA.manuscriptSentence_itemAMatrixRingAndFactorization
#audit_closed_axioms GroupApproximation.MFQuotientUnitsItemA.manuscriptSentence_itemA
