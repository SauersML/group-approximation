import GroupApproximation.Leavitt.PreusserNormalizedByRowAnnihilator
import GroupApproximation.Leavitt.PreusserSandwichStep

/-!
# Preusser's Proposition 21 for a subgroup normalized by `EL_ι(R)`

`PreusserSandwich.transvectionLevel_entry` and
`PreusserSandwich.transvectionLevel_diagDiff` prove Preusser's Proposition 21
for elements of a **normal subgroup of `EL_ι(R)`**.  Preusser states it for an
arbitrary `σ ∈ GL_ι(R)`, the conclusion landing in any subgroup `H` containing
`σ` and normalized by `EL_ι(R)`.  This file proves that form.

Two things change relative to `Leavitt.PreusserSandwichStep`, and nothing else:

* the transvection level `TransLevel H X` is a membership statement about
  `elementaryUnit k l hkl (a * X * b)` in a subgroup of `GL_ι(R)`, rather than
  about `elGen k l hkl (a * X * b)` in a subgroup of `EL_ι(R)`;
* the Proposition 20 input is
  `PreusserNormalizedBy.elementaryUnit_mem_of_row_annihilator`, which is proved
  in `Leavitt.PreusserNormalizedByRowAnnihilator` rather than assumed, so the
  `hprop20` binder disappears and a cardinality binder `hcard` takes its place
  (Proposition 20 is where `3 ≤ card ι` is spent).

Everything between those two ends is Preusser's own argument, reused verbatim:
the exchange refinement `PreusserSandwich.exists_orthogonalRefinement`, the
two-point coefficient vectors `PreusserSandwich.twoPoint`, and the row/column
identity `∑_p σ_ip σ'_pi = 1` are all imported unchanged from the
normal-subgroup development.

Normality of `H` inside `EL_ι(R)` is used nowhere; part (ii) uses only that the
elementary conjugate `e_{ji}(c) σ e_{ji}(c)⁻¹` is again in `H`, which is
exactly what being normalized by `EL_ι(R)` says.
-/

namespace GroupApproximation
namespace PreusserNormalizedBy

open PreusserSandwich

open scoped BigOperators

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-! ### The transvection level of a subgroup of `GL_ι(R)` -/

/-- `X` lies in the transvection level of `H`: every elementary root
`e_{kl}(a * X * b)` lies in `H`. -/
def TransLevel (H : Subgroup (Matrix ι ι R)ˣ) (X : R) : Prop :=
  ∀ (k l : ι) (hkl : k ≠ l) (a b : R), elementaryUnit k l hkl (a * X * b) ∈ H

namespace TransLevel

variable {H : Subgroup (Matrix ι ι R)ˣ} {X Y : R}

/-- `0` is always in the transvection level: `e_{kl}(0) = 1`. -/
theorem zero : TransLevel H (0 : R) := by
  intro k l hkl a b
  have h0 : a * (0 : R) * b = 0 := by simp
  rw [h0, elementaryUnit_zero]
  exact H.one_mem

/-- The transvection level is closed under addition. -/
theorem add (hX : TransLevel H X) (hY : TransLevel H Y) :
    TransLevel H (X + Y) := by
  intro k l hkl a b
  have hd : a * (X + Y) * b = a * X * b + a * Y * b := by noncomm_ring
  rw [hd, ← elementaryUnit_mul]
  exact H.mul_mem (hX k l hkl a b) (hY k l hkl a b)

/-- The transvection level absorbs left multiplication. -/
theorem mul_left (hX : TransLevel H X) (c : R) : TransLevel H (c * X) := by
  intro k l hkl a b
  have hd : a * (c * X) * b = a * c * X * b := by noncomm_ring
  rw [hd]
  exact hX k l hkl (a * c) b

/-- The transvection level absorbs right multiplication. -/
theorem mul_right (hX : TransLevel H X) (c : R) : TransLevel H (X * c) := by
  intro k l hkl a b
  have hd : a * (X * c) * b = a * X * (c * b) := by noncomm_ring
  rw [hd]
  exact hX k l hkl a (c * b)

/-- The transvection level is closed under negation. -/
theorem neg (hX : TransLevel H X) : TransLevel H (-X) := by
  have h := hX.mul_left (-1)
  rwa [neg_one_mul] at h

/-- The transvection level is closed under subtraction. -/
theorem sub (hX : TransLevel H X) (hY : TransLevel H Y) :
    TransLevel H (X - Y) := by
  have h := hX.add hY.neg
  rwa [← sub_eq_add_neg] at h

/-- The transvection level is closed under finite sums. -/
theorem sum {κ : Type*} {s : Finset κ} {f : κ → R}
    (h : ∀ p ∈ s, TransLevel H (f p)) :
    TransLevel H (∑ p ∈ s, f p) := by
  refine Finset.sum_induction f (fun z => TransLevel H z) ?_ ?_ h
  · intro u v hu hv
    exact hu.add hv
  · exact TransLevel.zero

end TransLevel

/-! ### Proposition 20, as a transvection-level statement -/

/-- Preusser's Proposition 20 restated as a transvection-level statement.  Only
the associativity of `a * y * x i * b` separates the two. -/
theorem transLevel_of_rowAnnihilator (hcard : 3 ≤ Fintype.card ι)
    {H : Subgroup (Matrix ι ι R)ˣ}
    (hnorm : NormalizedBy H (elementaryGroup ι R))
    {u : (Matrix ι ι R)ˣ} (hu : u ∈ H) (i j : ι) (x : ι → R) (y : R)
    (hxj : x j = 1) (hann : y * (∑ p, glMat u i p * x p) = 0) :
    TransLevel H (y * x i) := by
  intro k l hkl a b
  have hb := elementaryUnit_mem_of_row_annihilator hcard hnorm hu i j x y hxj
    hann hkl a b
  have hd : a * (y * x i) * b = a * y * x i * b := by noncomm_ring
  rw [hd]
  exact hb

/-! ### Proposition 21(i): off-diagonal entries -/

/-- **Preusser's Proposition 21(i), in membership form**, for a subgroup of
`GL_ι(R)` normalized by `EL_ι(R)`.

Every off-diagonal entry of every element of `H` lies in the transvection level
of `H`.

The proof is Preusser's.  Exchange is applied to `∑_p σ_ip σ'_pi = 1`, giving
idempotents `e_p = σ_ip σ'_pi r_p` summing to `1`.  For `p ≠ i` the identity
`e_p (σ_ii - e_p σ_ii) = 0` feeds Proposition 20 along the vector with `1` in
slot `i` and `-σ'_pi r_p σ_ii` in slot `p`; the identity
`e_i (σ_ij - e_i σ_ij) = 0` feeds Proposition 20 along the vector with `1` in
slot `j` and `-σ'_ii r_i σ_ij` in slot `i`.  Adding the `2 · card ι` pieces of
`σ_ij = σ_ii (∑_p e_p) σ'_ii r_i σ_ij + (∑_{p ≠ i} e_p) σ_ij` finishes it. -/
theorem transLevel_entry (hcard : 3 ≤ Fintype.card ι)
    (hex : ExchangePrerequisite.HasFiniteRightExchangePartitions R)
    {H : Subgroup (Matrix ι ι R)ˣ}
    (hnorm : NormalizedBy H (elementaryGroup ι R))
    {g : (Matrix ι ι R)ˣ} (hg : g ∈ H) {i j : ι} (hij : i ≠ j) :
    TransLevel H (glMat g i j) := by
  have hrow : (∑ p, glMat g i p * glMat g⁻¹ p i) = 1 := by
    have h2 : (glMat g * glMat g⁻¹) i i = (1 : Matrix ι ι R) i i := by
      rw [glMat_mul_inv g]
    rwa [Matrix.mul_apply, Matrix.one_apply_eq] at h2
  obtain ⟨e, r, hidem, -, heq, hesum⟩ :=
    exists_orthogonalRefinement hex (fun p => glMat g i p * glMat g⁻¹ p i) hrow
  have heqi : e i = glMat g i i * glMat g⁻¹ i i * r i := heq i
  -- Preusser's step (5): for `p ≠ i` the idempotent `e p` is in the level.
  have hstep5 : ∀ p, p ≠ i → TransLevel H (e p) := by
    intro p hpi
    have hip : i ≠ p := Ne.symm hpi
    have heqp : e p = glMat g i p * glMat g⁻¹ p i * r p := heq p
    have hxi : twoPoint i p (1 : R)
        (-(glMat g⁻¹ p i * r p * glMat g i i)) i = 1 := twoPoint_fst hip _ _
    have hsum : (∑ m, glMat g i m *
          twoPoint i p (1 : R) (-(glMat g⁻¹ p i * r p * glMat g i i)) m)
        = glMat g i i - e p * glMat g i i := by
      rw [sum_mul_twoPoint (glMat g) i i p (1 : R)
        (-(glMat g⁻¹ p i * r p * glMat g i i)), heqp]
      noncomm_ring
    have hann : e p * (∑ m, glMat g i m *
          twoPoint i p (1 : R) (-(glMat g⁻¹ p i * r p * glMat g i i)) m)
        = 0 := by
      rw [hsum, mul_sub, ← mul_assoc (e p) (e p) (glMat g i i), (hidem p).eq,
        sub_self]
    have hres := transLevel_of_rowAnnihilator hcard hnorm hg i i
      (twoPoint i p (1 : R) (-(glMat g⁻¹ p i * r p * glMat g i i))) (e p)
      hxi hann
    rwa [hxi, mul_one] at hres
  -- Preusser's step (6): the `i`-th piece, corrected by `σ'_ii r_i σ_ij`.
  have hstep6 : TransLevel H (e i * (glMat g⁻¹ i i * r i * glMat g i j)) := by
    have hji : j ≠ i := Ne.symm hij
    have hxj : twoPoint j i (1 : R)
        (-(glMat g⁻¹ i i * r i * glMat g i j)) j = 1 := twoPoint_fst hji _ _
    have hxi : twoPoint j i (1 : R) (-(glMat g⁻¹ i i * r i * glMat g i j)) i
        = -(glMat g⁻¹ i i * r i * glMat g i j) := twoPoint_snd hji _ _
    have hsum : (∑ m, glMat g i m *
          twoPoint j i (1 : R) (-(glMat g⁻¹ i i * r i * glMat g i j)) m)
        = glMat g i j - e i * glMat g i j := by
      rw [sum_mul_twoPoint (glMat g) i j i (1 : R)
        (-(glMat g⁻¹ i i * r i * glMat g i j)), heqi]
      noncomm_ring
    have hann : e i * (∑ m, glMat g i m *
          twoPoint j i (1 : R) (-(glMat g⁻¹ i i * r i * glMat g i j)) m)
        = 0 := by
      rw [hsum, mul_sub, ← mul_assoc (e i) (e i) (glMat g i j), (hidem i).eq,
        sub_self]
    have hres := transLevel_of_rowAnnihilator hcard hnorm hg i j
      (twoPoint j i (1 : R) (-(glMat g⁻¹ i i * r i * glMat g i j))) (e i)
      hxj hann
    rw [hxi] at hres
    have hneg : e i * -(glMat g⁻¹ i i * r i * glMat g i j)
        = -(e i * (glMat g⁻¹ i i * r i * glMat g i j)) := by noncomm_ring
    rw [hneg] at hres
    have hfin := hres.neg
    rwa [neg_neg] at hfin
  -- The `card ι` pieces carrying the correction factor.
  have hA : TransLevel H
      (∑ p, glMat g i i * e p * (glMat g⁻¹ i i * r i * glMat g i j)) := by
    refine TransLevel.sum ?_
    intro p _
    by_cases hpi : p = i
    · rw [hpi]
      have h6 := hstep6.mul_left (glMat g i i)
      have hassoc : glMat g i i * (e i * (glMat g⁻¹ i i * r i * glMat g i j))
          = glMat g i i * e i * (glMat g⁻¹ i i * r i * glMat g i j) := by
        noncomm_ring
      rwa [hassoc] at h6
    · exact ((hstep5 p hpi).mul_left (glMat g i i)).mul_right
        (glMat g⁻¹ i i * r i * glMat g i j)
  have hAval : (∑ p, glMat g i i * e p * (glMat g⁻¹ i i * r i * glMat g i j))
      = e i * glMat g i j := by
    have hfac : glMat g i i * (∑ p, e p) * (glMat g⁻¹ i i * r i * glMat g i j)
        = ∑ p, glMat g i i * e p * (glMat g⁻¹ i i * r i * glMat g i j) := by
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [← hfac, hesum, mul_one, heqi]
    noncomm_ring
  -- The `card ι - 1` remaining pieces.
  have hB : TransLevel H
      (∑ p ∈ Finset.univ.erase i, e p * glMat g i j) := by
    refine TransLevel.sum ?_
    intro p hp
    exact (hstep5 p (Finset.ne_of_mem_erase hp)).mul_right (glMat g i j)
  have hBval : (∑ p ∈ Finset.univ.erase i, e p * glMat g i j)
      = glMat g i j - e i * glMat g i j := by
    rw [← Finset.sum_mul, Finset.sum_erase_eq_sub (Finset.mem_univ i), hesum,
      sub_mul, one_mul]
  have hfinal := hA.add hB
  rw [hAval, hBval] at hfinal
  have hval : e i * glMat g i j + (glMat g i j - e i * glMat g i j)
      = glMat g i j := by noncomm_ring
  rwa [hval] at hfinal

/-! ### Proposition 21(ii): diagonal differences -/

/-- **Preusser's Proposition 21(ii), off-diagonal case**, for a subgroup of
`GL_ι(R)` normalized by `EL_ι(R)`.

The `(j, i)` entry of the elementary conjugate `e_{ji}(c) σ e_{ji}(c)⁻¹` is
`σ_ji + c σ_ii - σ_jj c - c σ_ij c`.  Part (i) applied to that conjugate, to `σ`
at `(j, i)`, and to `σ` at `(i, j)` puts three of the four summands in the
level, leaving `c σ_ii - σ_jj c`.

Being normalized by `EL_ι(R)` is used here, and only here: it is what puts the
elementary conjugate back into `H`. -/
theorem transLevel_diagDiff_of_ne (hcard : 3 ≤ Fintype.card ι)
    (hex : ExchangePrerequisite.HasFiniteRightExchangePartitions R)
    {H : Subgroup (Matrix ι ι R)ˣ}
    (hnorm : NormalizedBy H (elementaryGroup ι R))
    {g : (Matrix ι ι R)ˣ} (hg : g ∈ H) {i j : ι} (hij : i ≠ j) (c : R) :
    TransLevel H (c * glMat g i i - glMat g j j * c) := by
  have hji : j ≠ i := Ne.symm hij
  have hgt : elementaryUnit j i hji c * g * (elementaryUnit j i hji c)⁻¹ ∈ H :=
    hnorm.conj_mem (elementaryUnit_mem j i hji c) hg
  have hM : glMat (elementaryUnit j i hji c * g * (elementaryUnit j i hji c)⁻¹)
      = (1 + Matrix.single j i c) * glMat g * (1 - Matrix.single j i c) := by
    rw [glMat_mul, glMat_mul, glMat_elementaryUnit, glMat_elementaryUnit_inv]
  have hexp : (1 + Matrix.single j i c) * glMat g * (1 - Matrix.single j i c)
      = glMat g + Matrix.single j i c * glMat g - glMat g * Matrix.single j i c
        - Matrix.single j i c * glMat g * Matrix.single j i c := by
    noncomm_ring
  have hentry :
      glMat (elementaryUnit j i hji c * g * (elementaryUnit j i hji c)⁻¹) j i
      = glMat g j i + c * glMat g i i - glMat g j j * c
        - c * glMat g i j * c := by
    rw [hM, hexp]
    simp
  have h1 : TransLevel H
      (glMat (elementaryUnit j i hji c * g * (elementaryUnit j i hji c)⁻¹) j i) :=
    transLevel_entry hcard hex hnorm hgt hji
  rw [hentry] at h1
  have h2 : TransLevel H (glMat g j i) :=
    transLevel_entry hcard hex hnorm hg hji
  have h3 : TransLevel H (glMat g i j) :=
    transLevel_entry hcard hex hnorm hg hij
  have h4 : TransLevel H (c * glMat g i j * c) := (h3.mul_left c).mul_right c
  have h5 := (h1.sub h2).add h4
  have hval : glMat g j i + c * glMat g i i - glMat g j j * c
      - c * glMat g i j * c - glMat g j i + c * glMat g i j * c
      = c * glMat g i i - glMat g j j * c := by
    noncomm_ring
  rwa [hval] at h5

/-- **Preusser's Proposition 21(ii)**, with the restriction `i ≠ j` removed.

The congruence-subgroup description quantifies the diagonal clause over all
pairs `i j`, the diagonal pair included.  The case `i = j` follows from two
instances of the off-diagonal case through a third index `m`:
`c σ_ii - σ_ii c = (c σ_ii - σ_mm c) + (σ_mm - σ_ii) c`. -/
theorem transLevel_diagDiff (hcard : 3 ≤ Fintype.card ι)
    (hex : ExchangePrerequisite.HasFiniteRightExchangePartitions R)
    {H : Subgroup (Matrix ι ι R)ˣ}
    (hnorm : NormalizedBy H (elementaryGroup ι R))
    {g : (Matrix ι ι R)ˣ} (hg : g ∈ H) (i j : ι) (c : R) :
    TransLevel H (c * glMat g i i - glMat g j j * c) := by
  by_cases hij : i = j
  · obtain ⟨m, hmi, -⟩ := exists_third_index hcard i i
    have hA := transLevel_diagDiff_of_ne hcard hex hnorm hg (Ne.symm hmi) c
    have hB := transLevel_diagDiff_of_ne hcard hex hnorm hg hmi (1 : R)
    have hsum := hA.add (hB.mul_right c)
    have hval : c * glMat g i i - glMat g m m * c
        + (1 * glMat g m m - glMat g i i * 1) * c
        = c * glMat g i i - glMat g i i * c := by
      noncomm_ring
    rw [hval] at hsum
    rw [← hij]
    exact hsum
  · exact transLevel_diagDiff_of_ne hcard hex hnorm hg hij c

/-! ### The named endpoints

These are the two clauses of Preusser's Proposition 21 in exactly the shape the
entrywise description of `C_ι(R, I)` consumes: coefficients set to `1`. -/

/-- **Preusser, Proposition 21(i)**, coefficient-free.  For `i ≠ j`, the entry
`σ_ij` of an element of `H` produces elementary roots in `H`, in every
position. -/
theorem elementaryUnit_entry_mem (hcard : 3 ≤ Fintype.card ι)
    (hex : ExchangePrerequisite.HasFiniteRightExchangePartitions R)
    {H : Subgroup (Matrix ι ι R)ˣ}
    (hnorm : NormalizedBy H (elementaryGroup ι R))
    {g : (Matrix ι ι R)ˣ} (hg : g ∈ H) {i j : ι} (hij : i ≠ j)
    {k l : ι} (hkl : k ≠ l) :
    elementaryUnit k l hkl (glMat g i j) ∈ H := by
  have h := transLevel_entry hcard hex hnorm hg hij k l hkl 1 1
  rwa [one_mul, mul_one] at h

/-- **Preusser, Proposition 21(ii)**, coefficient-free.  No restriction on `i`
and `j`. -/
theorem elementaryUnit_diagDiff_mem (hcard : 3 ≤ Fintype.card ι)
    (hex : ExchangePrerequisite.HasFiniteRightExchangePartitions R)
    {H : Subgroup (Matrix ι ι R)ˣ}
    (hnorm : NormalizedBy H (elementaryGroup ι R))
    {g : (Matrix ι ι R)ˣ} (hg : g ∈ H) (i j : ι) (c : R)
    {k l : ι} (hkl : k ≠ l) :
    elementaryUnit k l hkl (c * glMat g i i - glMat g j j * c) ∈ H := by
  have h := transLevel_diagDiff hcard hex hnorm hg i j c k l hkl 1 1
  rwa [one_mul, mul_one] at h

end PreusserNormalizedBy
end GroupApproximation
