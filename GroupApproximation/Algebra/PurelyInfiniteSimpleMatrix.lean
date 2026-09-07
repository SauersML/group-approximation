import GroupApproximation.Algebra.PurelyInfiniteSimpleRing
import Mathlib.RingTheory.SimpleRing.Matrix
import GroupApproximation.Meta.AxiomGuard

/-!
# Matrix rings over a purely infinite simple ring

`non_mf_groups_exist.tex`, inside the proof of `thm:mf-quotient-units`:

> The ring `M_n(R)` is again countable, purely infinite, and
> simple~\cite[Corollary~1.7]{AGP} …

This module proves that, over an arbitrary unital ring, in the printed
idempotent form of pure infiniteness that `Algebra/PurelyInfiniteSimpleRing.lean`
carries.  It is the proposition `MFQuotientUnits.AGPMatrixReduction`;
`Manuscript/OneSidedMFRadical/MFQuotientUnitsMatrixReduction.lean` discharges
that wrapper.

## The route, and what it avoids

Ara--Goodearl--Pardo derive Corollary 1.7 from their §1 development, whose
centrepiece is Proposition 1.5 — every nonzero idempotent of a purely infinite
simple ring is infinite.  **None of that is needed here.**  The two clauses come
apart:

* **Simple.**  Mathlib already has it: `IsSimpleRing.matrix`.
* **Purely infinite.**  Given `A ≠ 0`, pick a nonzero entry `a = A i j`.  Pure
  infiniteness of `R` gives an idempotent `e = a * r` in `aR` that is infinite in
  `R`.  Set `r' = r * a * r`.  Then `r'` is a *generalised inverse*,
  `r' * a * r' = r'` (`genInverse_mul_genInverse`), which is exactly the
  condition making

      `P = A * single j i r'`

  idempotent — and `P` lies in `A · M_n(R)` by construction.  Its `(i,i)` entry
  is `a * r' = e`, and `P` is *equivalent* to `single i i e` with the explicit
  pair `(P, single i i 1)`.  Since `e` is infinite in `R`, `single i i e` is
  infinite in `M_n(R)`, and an idempotent equivalent to an infinite one is
  infinite.

So the only general theory this needs is that **infiniteness is an invariant of
equivalence** (`IsInfiniteIdempotent.of_equivalent`), proved here by conjugating
the decomposition: from `p = x*y`, `q = y*x` and `q = f + g`, the elements
`x*f*y` and `x*g*y` split `p` the same way.  That lemma and the transitivity of
`IsEquivalentIdempotent` are the two pieces of idempotent theory the tree was
missing; both are stated for an arbitrary ring and are of general use.

The sandwich identity `single j i c * M * single j i d = single j i (c * M i j * d)`
is **not** proved here: Mathlib's `Matrix.single_mul_mul_single` already has it,
in the strictly more general four-index form, and as a `simp` lemma.

## Countability plays no part

`AGPMatrixReduction` carries `[Countable R]` because the printed sentence says
"again countable, purely infinite, and simple", but the countability half is
`Algebra/CountableMatrixUnits.lean`'s and no clause below uses it.
-/

namespace GroupApproximation
namespace MFQuotientUnits

/-! ### Equivalence of idempotents is transitive -/

section Transitivity

variable {R : Type*} [Ring R]

/-- Equivalence of idempotents is transitive.

The witnesses compose: from `p = x*y`, `q = y*x` and `q = u*v`, `f = v*u`, the
pair `(x*u, v*y)` works, because `x*u*v*y = x*q*y = (x*y)*(x*y) = p`. -/
theorem IsEquivalentIdempotent.trans {p q f : R}
    (hp : IsIdempotentElem p) (hf : IsIdempotentElem f)
    (h₁ : IsEquivalentIdempotent R p q) (h₂ : IsEquivalentIdempotent R q f) :
    IsEquivalentIdempotent R p f := by
  obtain ⟨x, y, hpx, hqy⟩ := h₁
  obtain ⟨u, v, hqu, hfv⟩ := h₂
  refine ⟨x * u, v * y, ?_, ?_⟩
  · have e₁ : x * u * (v * y) = x * (u * v) * y := by noncomm_ring
    rw [e₁, ← hqu, hqy]
    have e₂ : x * (y * x) * y = x * y * (x * y) := by noncomm_ring
    rw [e₂, ← hpx]
    exact hp.symm
  · have e₁ : v * y * (x * u) = v * (y * x) * u := by noncomm_ring
    rw [e₁, ← hqy, hqu]
    have e₂ : v * (u * v) * u = v * u * (v * u) := by noncomm_ring
    rw [e₂, ← hfv]
    exact hf.symm

end Transitivity

/-! ### Infiniteness is an invariant of equivalence -/

section Invariance

variable {R : Type*} [Ring R]

/-- **An idempotent equivalent to an infinite idempotent is infinite.**

With `p = x*y` and `q = y*x`, a decomposition `q = f + g` is carried to
`p = x*f*y + x*g*y`.  Every clause survives because `f*q = f` and `g*q = g`, so
the cross terms `f*q*g` and `g*q*f` vanish exactly as `f*g` and `g*f` do. -/
theorem IsInfiniteIdempotent.of_equivalent {p q : R}
    (hp : IsIdempotentElem p) (h : IsEquivalentIdempotent R p q)
    (hq : IsInfiniteIdempotent R q) : IsInfiniteIdempotent R p := by
  obtain ⟨x, y, hpx, hqy⟩ := h
  obtain ⟨f, g, hf, hg, hfg, hgf, hsum, hqf, hgne⟩ := hq
  -- `f` and `g` are fixed by `q` on both sides.
  have hfq : f * q = f := by rw [hsum, mul_add, hfg, add_zero]; exact hf
  have hgq : g * q = g := by rw [hsum, mul_add, hgf, zero_add]; exact hg
  have hqg : q * g = g := by rw [hsum, add_mul, hfg, zero_add]; exact hg
  have hfqf : f * q * f = f := by rw [hfq]; exact hf
  have hgqg : g * q * g = g := by rw [hgq]; exact hg
  have hfqg : f * q * g = 0 := by rw [hfq]; exact hfg
  have hgqf : g * q * f = 0 := by rw [hgq]; exact hgf
  -- The conjugated halves.
  have hFidem : IsIdempotentElem (x * f * y) := by
    show x * f * y * (x * f * y) = x * f * y
    have e₁ : x * f * y * (x * f * y) = x * (f * (y * x) * f) * y := by noncomm_ring
    rw [e₁, ← hqy, hfqf]
  have hGidem : IsIdempotentElem (x * g * y) := by
    show x * g * y * (x * g * y) = x * g * y
    have e₁ : x * g * y * (x * g * y) = x * (g * (y * x) * g) * y := by noncomm_ring
    rw [e₁, ← hqy, hgqg]
  refine ⟨x * f * y, x * g * y, hFidem, hGidem, ?_, ?_, ?_, ?_, ?_⟩
  · have e₁ : x * f * y * (x * g * y) = x * (f * (y * x) * g) * y := by noncomm_ring
    rw [e₁, ← hqy, hfqg, mul_zero, zero_mul]
  · have e₁ : x * g * y * (x * f * y) = x * (g * (y * x) * f) * y := by noncomm_ring
    rw [e₁, ← hqy, hgqf, mul_zero, zero_mul]
  · have e₁ : x * f * y + x * g * y = x * (f + g) * y := by noncomm_ring
    rw [e₁, ← hsum, hqy]
    have e₂ : x * (y * x) * y = x * y * (x * y) := by noncomm_ring
    rw [e₂, ← hpx]
    exact hp.symm
  · -- `p ~ q ~ f ~ x*f*y`
    have hFf : IsEquivalentIdempotent R (x * f * y) f := by
      refine ⟨x * f, f * y, ?_, ?_⟩
      · have e₀ : x * f * (f * y) = x * (f * f) * y := by noncomm_ring
        rw [e₀, hf]
      · have e₁ : f * y * (x * f) = f * (y * x) * f := by noncomm_ring
        rw [e₁, ← hqy, hfqf]
    exact IsEquivalentIdempotent.trans hp hFidem
      (IsEquivalentIdempotent.trans hp hf ⟨x, y, hpx, hqy⟩ hqf) hFf.symm
  · intro hzero
    apply hgne
    have e₁ : y * (x * g * y) * x = q * g * q := by rw [hqy]; noncomm_ring
    rw [hzero, mul_zero, zero_mul] at e₁
    rw [hqg, hgq] at e₁
    exact e₁.symm

end Invariance

/-! ### Transport of idempotent theory along `single i i` -/

section Single

variable {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem isIdempotentElem_single {e : R} (he : IsIdempotentElem e) (i : ι) :
    IsIdempotentElem (Matrix.single i i e : Matrix ι ι R) := by
  show Matrix.single i i e * Matrix.single i i e = Matrix.single i i e
  rw [Matrix.single_mul_single_same, he]

omit [Fintype ι] in
theorem single_ne_zero {g : R} (hg : g ≠ 0) (i : ι) :
    (Matrix.single i i g : Matrix ι ι R) ≠ 0 := by
  intro h
  exact hg (by simpa using congrArg (fun M : Matrix ι ι R => M i i) h)

theorem isEquivalentIdempotent_single {e f : R}
    (h : IsEquivalentIdempotent R e f) (i : ι) :
    IsEquivalentIdempotent (Matrix ι ι R)
      (Matrix.single i i e) (Matrix.single i i f) := by
  obtain ⟨x, y, hx, hy⟩ := h
  exact ⟨Matrix.single i i x, Matrix.single i i y,
    by rw [Matrix.single_mul_single_same, ← hx],
    by rw [Matrix.single_mul_single_same, ← hy]⟩

/-- An infinite idempotent of `R` stays infinite in the corner `single i i`. -/
theorem isInfiniteIdempotent_single {e : R} (h : IsInfiniteIdempotent R e)
    (i : ι) :
    IsInfiniteIdempotent (Matrix ι ι R) (Matrix.single i i e) := by
  obtain ⟨f, g, hf, hg, hfg, hgf, hsum, hequiv, hgne⟩ := h
  refine ⟨Matrix.single i i f, Matrix.single i i g,
    isIdempotentElem_single hf i, isIdempotentElem_single hg i, ?_, ?_, ?_,
    isEquivalentIdempotent_single hequiv i, single_ne_zero hgne i⟩
  · rw [Matrix.single_mul_single_same, hfg, Matrix.single_zero]
  · rw [Matrix.single_mul_single_same, hgf, Matrix.single_zero]
  · rw [← Matrix.single_add, ← hsum]

end Single

/-! ### The theorem -/

section Main

variable {R : Type*} [Ring R]

/-- `r * a * r` is a generalised inverse of `a` whenever `a * r` is idempotent:
`r' * a * r' = r'`.  This is what makes the matrix below idempotent. -/
theorem genInverse_mul_genInverse {a r : R} (he : IsIdempotentElem (a * r)) :
    r * a * r * a * (r * a * r) = r * a * r := by
  have e₁ : r * a * r * a * (r * a * r) = r * (a * r * (a * r)) * (a * r) := by
    noncomm_ring
  rw [e₁, he]
  have e₂ : r * (a * r) * (a * r) = r * (a * r * (a * r)) := by noncomm_ring
  rw [e₂, he]
  noncomm_ring

/-- **Ara--Goodearl--Pardo, Corollary 1.7**, in the printed idempotent form:
a matrix ring over a purely infinite simple ring is purely infinite simple. -/
theorem isPurelyInfiniteSimpleRing_matrix
    (hR : IsPurelyInfiniteSimpleRing R) (n : ℕ) (hn : 1 ≤ n) :
    IsPurelyInfiniteSimpleRing (Matrix (Fin n) (Fin n) R) := by
  haveI : IsSimpleRing R := hR.1
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine ⟨inferInstance, ?_⟩
  intro A hA
  -- A nonzero matrix has a nonzero entry.
  obtain ⟨i, j, hij⟩ : ∃ i j, A i j ≠ 0 := by
    by_contra hc
    refine hA ?_
    ext p q
    have hpq : ¬ (A p q ≠ 0) := fun h => hc ⟨p, q, h⟩
    simpa using hpq
  -- Pure infiniteness of `R` at that entry.
  obtain ⟨e, r, her, he, hinf⟩ := hR.exists_infiniteIdempotent hij
  have hear : IsIdempotentElem (A i j * r) := by rw [← her]; exact he
  refine ⟨A * Matrix.single j i (r * A i j * r),
    Matrix.single j i (r * A i j * r), rfl, ?_, ?_⟩
  · -- idempotent, because `r * A i j * r` is a generalised inverse
    show A * Matrix.single j i (r * A i j * r) * (A * Matrix.single j i (r * A i j * r))
      = A * Matrix.single j i (r * A i j * r)
    have e₁ : A * Matrix.single j i (r * A i j * r) *
        (A * Matrix.single j i (r * A i j * r))
        = A * (Matrix.single j i (r * A i j * r) * A *
            Matrix.single j i (r * A i j * r)) := by
      simp only [Matrix.mul_assoc]
    rw [e₁, Matrix.single_mul_mul_single, genInverse_mul_genInverse hear]
  · -- infinite, because it is equivalent to `single i i e`
    have hidem : IsIdempotentElem
        (A * Matrix.single j i (r * A i j * r)) := by
      show A * Matrix.single j i (r * A i j * r) *
          (A * Matrix.single j i (r * A i j * r))
        = A * Matrix.single j i (r * A i j * r)
      have e₁ : A * Matrix.single j i (r * A i j * r) *
          (A * Matrix.single j i (r * A i j * r))
          = A * (Matrix.single j i (r * A i j * r) * A *
              Matrix.single j i (r * A i j * r)) := by
        simp only [Matrix.mul_assoc]
      rw [e₁, Matrix.single_mul_mul_single, genInverse_mul_genInverse hear]
    have hcorner : A i j * (r * A i j * r) = e := by
      have : A i j * (r * A i j * r) = A i j * r * (A i j * r) := by noncomm_ring
      rw [this, hear, her]
    -- `P = P * single i i 1` and `single i i e = single i i 1 * P`
    have hright : A * Matrix.single j i (r * A i j * r)
        = A * Matrix.single j i (r * A i j * r) * Matrix.single i i (1 : R) := by
      rw [Matrix.mul_assoc, Matrix.single_mul_single_same, mul_one]
    have hleft : (Matrix.single i i e : Matrix (Fin n) (Fin n) R)
        = Matrix.single i i (1 : R) * (A * Matrix.single j i (r * A i j * r)) := by
      ext k l
      by_cases hk : k = i
      · by_cases hl : l = i
        · subst hk; subst hl
          simp [hcorner]
        · subst hk
          simp [hl, Ne.symm hl]
      · simp [hk, Ne.symm hk]
    exact IsInfiniteIdempotent.of_equivalent hidem
      ⟨A * Matrix.single j i (r * A i j * r), Matrix.single i i (1 : R),
        hright, hleft⟩
      (isInfiniteIdempotent_single hinf i)

end Main

end MFQuotientUnits
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.MFQuotientUnits.IsEquivalentIdempotent.trans
#audit_axioms GroupApproximation.MFQuotientUnits.IsInfiniteIdempotent.of_equivalent
#audit_axioms GroupApproximation.MFQuotientUnits.isInfiniteIdempotent_single
#audit_axioms GroupApproximation.MFQuotientUnits.genInverse_mul_genInverse
#audit_axioms GroupApproximation.MFQuotientUnits.isPurelyInfiniteSimpleRing_matrix
