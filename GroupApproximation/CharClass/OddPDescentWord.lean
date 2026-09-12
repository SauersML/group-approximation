-- `Finset.Iio` on `Fin p` needs `Fin.instLocallyFiniteOrder`
-- (`Mathlib/Order/Interval/Finset/Fin.lean` l.33 at pin `81a5d257`); the same
-- import `OddPTuple.lean` takes for `tupPre`.
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Parity

/-!
# The two-letter complex `E` and its `p`-fold tensor power, as words

`sp-design`'s descent for the degree-one normalisation constant of the odd-primary
Steenrod construction never leaves the two-letter complex

```text
    E⁰ = K·f ,   E¹ = K·g ,   δf = g ,   δg = 0 .
```

A chain map `E → C^*(X)` is *any* `0`-cochain `f`, for free, so the whole computation
is finite-dimensional linear algebra in the `2^p` words of `E^{⊗p}` and reaches the
singular tensor power only at the end, by functoriality.  This file is `E^{⊗p}`.

## The model, and why it is flat and ungraded

A word is a function `Fin p → Bool`, `true` standing for the degree-one letter `g` and
`false` for the degree-zero letter `f`; `eDeg` is the total degree.  Every operator of the
descent — the differential, the contraction, the cyclic shift, the norm — preserves
`E^{⊗p}` and is written here as an endomorphism of the **whole** module `EMod`, not of a
graded piece.  That is deliberate.  `OddPTuple.lean`'s `TupIdx X r k` carries the degree
because its differential has to be a `ChainComplex` morphism in Mathlib's sense; nothing
in this file does, and carrying `k` would put a degree cast on every composite of two
operators.  The grading is recovered by `eDeg`, and `eWedge_eDeg`/`ePart_eDeg` record how
each operator moves it.

## The signs are `OddPTuple.lean`'s, not new ones

`ePre` is `tupPre` for this alphabet: the total degree of the slots strictly before `a`,
which is the Koszul prefix sign of an operator applied in slot `a`.  This is the
inter-lane sign contract of `sp-steenrod`'s report §11a item 1 — the tensor differential
carries the **left** factor's degree — specialised to letters of degree `0` and `1`.  No
sign convention is introduced here.

## The two elementary operators

`eWedge a` inserts `g` in slot `a` (and is `0` if that slot already holds `g`); `ePart a`
deletes it.  In the exterior-algebra reading of `E^{⊗p}` — the re-description that makes
the descent computable generic in `p`, checked against `sp-design`'s word model on every
basis element at `p = 3, 5, 7` — these are `ξ_a ∧ (−)` and `∂/∂ξ_a`, the differential is
`eD = Σ_a eWedge a` (left multiplication by `σ = Σ_a ξ_a`) and the one-slot contraction is
`eH = ePart 0`.  `OddPDescentClifford.lean` proves the two relations that generate every
identity the descent needs.
-/

namespace GroupApproximation.CharClass

variable {p : ℕ}

/-! ## 1. Words -/

/-- The alphabet of `E`: `true` is the degree-one letter `g = δf`, `false` the
degree-zero letter `f`. -/
abbrev ELetter : Type := Bool

/-- The degree of a letter. -/
def eLetterDeg (b : ELetter) : ℕ := if b then 1 else 0

@[simp] theorem eLetterDeg_true : eLetterDeg true = 1 := rfl
@[simp] theorem eLetterDeg_false : eLetterDeg false = 0 := rfl

theorem eLetterDeg_le_one (b : ELetter) : eLetterDeg b ≤ 1 := by
  cases b <;> simp

/-- A basis word of `E^{⊗p}`: one letter per slot.  An `abbrev`, not a `def`: `rw`
checks type-correctness at `instances` transparency and will not unfold a plain `def`
(`OddPTuple.lean`'s second design rule). -/
abbrev EWord (p : ℕ) : Type := Fin p → ELetter

/-- The degree-`k` part is cut out by this; the module below is ungraded on purpose. -/
def eDeg (w : EWord p) : ℕ := ∑ j, eLetterDeg (w j)

/-- **The `p`-fold tensor power of `E`**, as a free `K`-module on the words. -/
abbrev EMod (K : Type) [CommRing K] (p : ℕ) : Type := EWord p →₀ K

/-- The Koszul prefix: the total degree of the slots strictly before `a`.  This is
`OddPTuple.lean`'s `tupPre` for the two-letter alphabet. -/
def ePre (w : EWord p) (a : Fin p) : ℕ := ∑ l ∈ Finset.Iio a, eLetterDeg (w l)

@[simp] theorem ePre_zero_of_card [NeZero p] (w : EWord p) :
    ePre w (0 : Fin p) = 0 := by
  have : (Finset.Iio (0 : Fin p)) = ∅ := by
    ext l; simp
  rw [ePre, this, Finset.sum_empty]

/-! ### The two prefix-update lemmas

Updating slot `a` leaves the prefix at every slot `l ≤ a` alone and changes it by the
degree difference at every slot `l > a`.  Isolated exactly as `OddPTupleSign.lean`
isolates them: the sign bookkeeping of the anticommutation relations is *all* of their
content, and inlining it makes the case split unreadable. -/

theorem ePre_update_of_le (w : EWord p) (a : Fin p) (x : ELetter) (l : Fin p)
    (h : l ≤ a) : ePre (Function.update w a x) l = ePre w l := by
  refine Finset.sum_congr rfl fun m hm => ?_
  have hma : m ≠ a := ne_of_lt (lt_of_lt_of_le (Finset.mem_Iio.mp hm) h)
  rw [Function.update_of_ne hma]

/-- The uniform form: past the updated slot, the prefix moves by exactly the degree
difference.  Both special cases used later are `omega` from this. -/
theorem ePre_update_of_lt (w : EWord p) (a : Fin p) (x : ELetter) (l : Fin p)
    (h : a < l) :
    ePre (Function.update w a x) l + eLetterDeg (w a)
      = ePre w l + eLetterDeg x := by
  have ha : a ∈ Finset.Iio l := Finset.mem_Iio.mpr h
  have hrest : ∀ m ∈ (Finset.Iio l).erase a,
      eLetterDeg (Function.update w a x m) = eLetterDeg (w m) := by
    intro m hm
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hm)]
  -- `Finset.add_sum_erase` reads `f a + ∑ erase = ∑ s`, so splitting a sum off is the
  -- BACKWARD rewrite (`OddPTupleSign.lean`'s comment; forward it hunts for a pattern on
  -- the other side of the goal and higher-order unification does not find it).
  have e1 : ePre (Function.update w a x) l
      = eLetterDeg x + ∑ m ∈ (Finset.Iio l).erase a, eLetterDeg (w m) := by
    rw [ePre, ← Finset.add_sum_erase _ _ ha, Function.update_self]
    exact congrArg (fun z => eLetterDeg x + z) (Finset.sum_congr rfl hrest)
  have e2 : ePre w l = eLetterDeg (w a) + ∑ m ∈ (Finset.Iio l).erase a, eLetterDeg (w m) :=
    (Finset.add_sum_erase _ _ ha).symm
  omega

/-! ## 2. The two elementary operators -/

variable (K : Type) [CommRing K]

/-- `ξ_a ∧ (−)` on a basis word: put `g` in slot `a`, with the Koszul prefix sign; `0`
if slot `a` already holds `g`.  Totalised, in `OddPTuple.lean`'s sense: the vanishing
case is inside the definition, so no sum downstream carries a side condition. -/
noncomputable def eWedgeGen (a : Fin p) (w : EWord p) : EMod K p :=
  if w a = true then 0
  else ((-1 : K) ^ ePre w a) • Finsupp.single (Function.update w a true) (1 : K)

/-- `∂/∂ξ_a` on a basis word: remove the `g` from slot `a`, with the same sign; `0` if
slot `a` holds `f`. -/
noncomputable def ePartGen (a : Fin p) (w : EWord p) : EMod K p :=
  if w a = true then
    ((-1 : K) ^ ePre w a) • Finsupp.single (Function.update w a false) (1 : K)
  else 0

/-- **Insertion of `g` in slot `a`.** -/
noncomputable def eWedge (a : Fin p) : EMod K p →ₗ[K] EMod K p :=
  Finsupp.linearCombination K (eWedgeGen K a)

/-- **Deletion of the `g` in slot `a`.** -/
noncomputable def ePart (a : Fin p) : EMod K p →ₗ[K] EMod K p :=
  Finsupp.linearCombination K (ePartGen K a)

@[simp] theorem eWedge_single (a : Fin p) (w : EWord p) :
    eWedge K a (Finsupp.single w (1 : K)) = eWedgeGen K a w := by
  rw [eWedge, Finsupp.linearCombination_single, one_smul]

theorem eWedgeGen_of_true {a : Fin p} {w : EWord p} (h : w a = true) :
    eWedgeGen K a w = 0 := if_pos h

theorem eWedgeGen_of_false {a : Fin p} {w : EWord p} (h : w a = false) :
    eWedgeGen K a w
      = ((-1 : K) ^ ePre w a) • Finsupp.single (Function.update w a true) (1 : K) :=
  if_neg (by simp [h])

theorem ePartGen_of_false {a : Fin p} {w : EWord p} (h : w a = false) :
    ePartGen K a w = 0 := if_neg (by simp [h])

theorem ePartGen_of_true {a : Fin p} {w : EWord p} (h : w a = true) :
    ePartGen K a w
      = ((-1 : K) ^ ePre w a) • Finsupp.single (Function.update w a false) (1 : K) :=
  if_pos h

@[simp] theorem ePart_single (a : Fin p) (w : EWord p) :
    ePart K a (Finsupp.single w (1 : K)) = ePartGen K a w := by
  rw [ePart, Finsupp.linearCombination_single, one_smul]

/-! ## 3. The extensionality principle used everywhere below

Two `K`-linear endomorphisms of `EMod` agree as soon as they agree on the basis words
with coefficient `1`; the general coefficient is a scalar multiple.  Stated once so that
no later proof repeats the `Finsupp.lhom_ext` dance. -/

theorem eWedge_smul_single (a : Fin p) (c : K) (w : EWord p) :
    eWedge K a (c • Finsupp.single w (1 : K)) = c • eWedgeGen K a w := by
  rw [map_smul, eWedge_single]

theorem ePart_smul_single (a : Fin p) (c : K) (w : EWord p) :
    ePart K a (c • Finsupp.single w (1 : K)) = c • ePartGen K a w := by
  rw [map_smul, ePart_single]

/-- Two signed multiples of a basis word collapse to one. -/
theorem eSign_smul_smul (m n : ℕ) (x : EMod K p) :
    ((-1 : K) ^ m) • (((-1 : K) ^ n) • x) = ((-1 : K) ^ (m + n)) • x := by
  rw [smul_smul, ← pow_add]

theorem eMod_ext {f g : EMod K p →ₗ[K] EMod K p}
    (h : ∀ w : EWord p, f (Finsupp.single w (1 : K)) = g (Finsupp.single w (1 : K))) :
    f = g := by
  refine Finsupp.lhom_ext fun w b => ?_
  have hb : (Finsupp.single w b : EMod K p) = b • Finsupp.single w (1 : K) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hb, map_smul, map_smul, h]

end GroupApproximation.CharClass
