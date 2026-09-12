import GroupApproximation.Leavitt.ElementarySimplicity
import GroupApproximation.Leavitt.ExchangePrerequisite
import Mathlib.Data.Fintype.EquivFin

/-!
# The exchange-consuming step of the normal-structure theorem

This file formalizes Proposition 21 of R. Preusser, *On general linear groups
over exchange rings*, Linear and Multilinear Algebra **70** (2022), no. 4,
705--713 (arXiv:1912.11386), in the membership form the sandwich argument
actually consumes.  Preusser's Proposition 21 says that for `σ ∈ GL_n(R)` over
an exchange ring and `n ≥ 3`,

* `t_kl(a σ_ij b)` is a product of `16n - 8` elementary conjugates of `σ^{±1}`,
  and
* `t_kl(a (c σ_ii - σ_jj c) b)` is a product of `48n - 24` such conjugates.

Conjugate *counts* are irrelevant to the sandwich classification, so the
statements below record only the membership consequence: with `N` a normal
subgroup of `EL_ι(R)` and `g ∈ N`, every elementary root
`e_{kl}(a · (elMat g) i j · b)` again lies in `N`, and likewise for the
diagonal differences.  That is exactly the clause
`map_le_congruenceSubgroup_of_entries` (`Leavitt.CongruencePlumbing`) needs,
and, read through `mem_normalLevel_iff` (`Leavitt.CongruenceSubgroups`), it is
the missing upper half of the sandwich.

## Hypotheses, and who is expected to discharge them

Nothing here is unconditional.  Every theorem below carries its inputs as
**leading explicit binders**:

* `hprop20 : RowAnnihilatorTransvection N` is Preusser's Proposition 20 (the
  exchange-*free* row-annihilator step) in membership form.  It is the target
  of the sibling task on `Leavitt.RowAnnihilatorTransvection`, whose statement
  is
  `elGen_mem_of_row_annihilator (hcard : 3 ≤ Fintype.card ι) (N) [N.Normal]
   (hg : g ∈ N) (i j) (x : ι → R) (y : R) (hxj : x j = 1)
   (hann : y * (∑ p, elMat g i p * x p) = 0) (hkl : k ≠ l) (a b) :
   elGen k l hkl (a * y * x i * b) ∈ N`,
  and `RowAnnihilatorTransvection N` is precisely that statement with `g`
  universally quantified over `N`, so the discharge is one `fun`-abstraction.
  It is satisfiable: Preusser proves it for every unital ring with `n ≥ 3`,
  by an explicit two-step reduction word, and the required square-zero and
  row-supported commutator calculus is already in
  `Leavitt.ElementaryTransvectionExtraction`.  Note that the universal
  quantification over `h ∈ N` is used: Proposition 21(ii) applies
  Proposition 20 not to `g` but to an elementary conjugate of `g`.

* `hex : ExchangePrerequisite.HasFiniteRightExchangePartitions R` is the finite
  one-sided exchange refinement already named in
  `Leavitt.ExchangePrerequisite`.  It is the target of the sibling task on
  `Leavitt.ExchangeRefinement`, and it is satisfiable: it is Nicholson's
  classical refinement property, and the two-term case is already proved for
  `L_k(1,2)` (`ExchangePrerequisite.hasRightExchange_of_singleSandwich`).

A reader who wants to know exactly what is still owed should look only at those
two binders; everything between them and the conclusions is proved here.

## What the proof uses, and what it does not

Preusser's Proposition 21(i) applies exchange to the row/column identity
`∑_p σ_ip σ'_pi = 1` (with `σ' = σ⁻¹`), producing idempotents
`e_p = σ_ip σ'_pi r_p` with `∑_p e_p = 1`.  Only **idempotency** and the
**right-multiple form** `e_p ∈ σ_ip σ'_pi R` are used; the *orthogonality*
clause `e p * e q = 0` of `HasFiniteRightExchangePartitions` is never needed.
The orthogonality clause is nevertheless kept in the hypothesis, because it is
part of the repository's existing named property and dropping it would make
the binder differ from the one the sibling task proves.

Two deviations from the task plan, both forced:

* Part (i) is **false without `i ≠ j`**.  For `N = ⊥` and `g = 1` the diagonal
  entry is `1`, so the claim would read `elGen k l hkl (a * b) ∈ ⊥` for all `a`
  and `b`, i.e. `a * b = 0` for all `a` and `b`, which fails in any nontrivial
  ring.  Preusser states Proposition 21 with `i ≠ j`; `transvectionLevel_entry`
  and `elGen_entry_mem` therefore take `hij : i ≠ j`.
* Part (ii) is stated *without* `i ≠ j`, which is stronger than Preusser's
  form and is what the congruence-subgroup clause needs (it quantifies over all
  `i j`, `i = j` included).  The diagonal case `i = j` is reduced to two
  instances of the off-diagonal case through a third index, which is where
  `3 ≤ Fintype.card ι` is used.  Part (i) itself needs no cardinality bound of
  its own: the `n ≥ 3` of Preusser's Proposition 21 enters only through
  `hprop20`.  The binder is retained in `elGen_entry_mem` (as `_hcard`) so that
  the statement matches Preusser's and the assembly step can pass it
  positionally.

Finally, `exists_orthogonalRefinement` re-indexes
`HasFiniteRightExchangePartitions` from `Fin n` to the ambient `Fintype ι`.
That bridge is deliberately duplicated here rather than imported, so that this
file compiles independently of the sibling tasks; it can be replaced by
`ExchangePrerequisite.exists_orthogonal_refinement` once that lands.
-/

namespace GroupApproximation

namespace PreusserSandwich

open ElementarySimplicity

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-! ### The transvection level of a subgroup

`TransvectionLevel N X` says that `X` contributes a genuine elementary root to
`N` in every position and with every pair of coefficients.  Preusser's
Propositions 20 and 21 all conclude statements of this shape, and the shape is
closed under the ring operations, which is what lets the `2 · card ι` pieces of
Proposition 21 be summed. -/

/-- `X` lies in the transvection level of `N`: every elementary root
`e_{kl}(a * X * b)` lies in `N`. -/
def TransvectionLevel (N : Subgroup (elementaryGroup ι R)) (X : R) : Prop :=
  ∀ (k l : ι) (hkl : k ≠ l) (a b : R), elGen k l hkl (a * X * b) ∈ N

section Level

variable {N : Subgroup (elementaryGroup ι R)} {X Y : R}

/-- `0` is always in the transvection level: `e_{kl}(0) = 1`. -/
theorem TransvectionLevel.zero : TransvectionLevel N (0 : R) := by
  intro k l hkl a b
  have h0 : a * (0 : R) * b = 0 := by simp
  rw [h0, elGen_zero]
  exact N.one_mem

/-- The transvection level is closed under addition, because
`e_{kl}(u) e_{kl}(v) = e_{kl}(u + v)`. -/
theorem TransvectionLevel.add (hX : TransvectionLevel N X) (hY : TransvectionLevel N Y) :
    TransvectionLevel N (X + Y) := by
  intro k l hkl a b
  have hd : a * (X + Y) * b = a * X * b + a * Y * b := by noncomm_ring
  rw [hd, ← elGen_mul]
  exact N.mul_mem (hX k l hkl a b) (hY k l hkl a b)

/-- The transvection level absorbs left multiplication: the extra factor is
folded into the left coefficient. -/
theorem TransvectionLevel.mul_left (hX : TransvectionLevel N X) (c : R) :
    TransvectionLevel N (c * X) := by
  intro k l hkl a b
  have hd : a * (c * X) * b = a * c * X * b := by noncomm_ring
  rw [hd]
  exact hX k l hkl (a * c) b

/-- The transvection level absorbs right multiplication. -/
theorem TransvectionLevel.mul_right (hX : TransvectionLevel N X) (c : R) :
    TransvectionLevel N (X * c) := by
  intro k l hkl a b
  have hd : a * (X * c) * b = a * X * (c * b) := by noncomm_ring
  rw [hd]
  exact hX k l hkl a (c * b)

/-- The transvection level is closed under negation. -/
theorem TransvectionLevel.neg (hX : TransvectionLevel N X) : TransvectionLevel N (-X) := by
  have h := hX.mul_left (-1)
  rwa [neg_one_mul] at h

/-- The transvection level is closed under subtraction. -/
theorem TransvectionLevel.sub (hX : TransvectionLevel N X) (hY : TransvectionLevel N Y) :
    TransvectionLevel N (X - Y) := by
  have h := hX.add hY.neg
  rwa [← sub_eq_add_neg] at h

/-- The transvection level is closed under finite sums.  This is what replaces
Preusser's conjugate bookkeeping: only membership is tracked, so the `16n - 8`
factors collapse to one additive induction. -/
theorem TransvectionLevel.sum {κ : Type*} {s : Finset κ} {f : κ → R}
    (h : ∀ p ∈ s, TransvectionLevel N (f p)) :
    TransvectionLevel N (∑ p ∈ s, f p) := by
  refine Finset.sum_induction f (fun z => TransvectionLevel N z) ?_ ?_ h
  · intro u v hu hv
    exact hu.add hv
  · exact TransvectionLevel.zero

end Level

/-! ### Proposition 20, packaged as a hypothesis -/

/-- **Preusser's Proposition 20, in membership form, as a property of `N`.**

If `y` annihilates the `i`-th entry of `σ x` for a coefficient vector `x` one of
whose entries is `1`, then `y * x i` lies in the transvection level of `N`.

This is *not* proved here.  It is the statement the sibling task
`Leavitt.RowAnnihilatorTransvection` targets, quantified over all `h ∈ N`
because Proposition 21(ii) below needs it for elementary conjugates of `g` as
well as for `g` itself.  Preusser proves it for every unital ring with
`3 ≤ Fintype.card ι`, so the binder is satisfiable. -/
def RowAnnihilatorTransvection (N : Subgroup (elementaryGroup ι R)) : Prop :=
  ∀ (h : elementaryGroup ι R), h ∈ N → ∀ (i j : ι) (x : ι → R) (y : R),
    x j = 1 → y * (∑ p, elMat h i p * x p) = 0 →
    ∀ (k l : ι) (hkl : k ≠ l) (a b : R), elGen k l hkl (a * y * x i * b) ∈ N

/-- Proposition 20 restated as a transvection-level statement.  Only the
associativity of `a * y * x i * b` separates the two. -/
theorem transvectionLevel_of_prop20 {N : Subgroup (elementaryGroup ι R)}
    (hprop20 : RowAnnihilatorTransvection N)
    {h : elementaryGroup ι R} (hh : h ∈ N) (i j : ι) (x : ι → R) (y : R)
    (hxj : x j = 1) (hann : y * (∑ p, elMat h i p * x p) = 0) :
    TransvectionLevel N (y * x i) := by
  intro k l hkl a b
  have hb := hprop20 h hh i j x y hxj hann k l hkl a b
  have hd : a * (y * x i) * b = a * y * x i * b := by noncomm_ring
  rw [hd]
  exact hb

/-! ### The two-point coefficient vectors fed to Proposition 20

Every application of Proposition 20 below uses a vector supported on two
indices: a `1` in one slot, and one prescribed coefficient in another. -/

/-- The coefficient vector with `u` at `p` and `w` at `q`. -/
def twoPoint (p q : ι) (u w : R) : ι → R :=
  fun m => (if m = p then u else 0) + (if m = q then w else 0)

omit [Fintype ι] in
theorem twoPoint_apply (p q : ι) (u w : R) (m : ι) :
    twoPoint p q u w m = (if m = p then u else 0) + (if m = q then w else 0) := rfl

omit [Fintype ι] in
theorem twoPoint_fst {p q : ι} (hpq : p ≠ q) (u w : R) : twoPoint p q u w p = u := by
  simp [twoPoint_apply, hpq]

omit [Fintype ι] in
theorem twoPoint_snd {p q : ι} (hpq : p ≠ q) (u w : R) : twoPoint p q u w q = w := by
  simp [twoPoint_apply, hpq.symm]

/-- A row of a matrix against a one-point vector. -/
theorem sum_mul_indicator (M : Matrix ι ι R) (i p : ι) (u : R) :
    (∑ m, M i m * (if m = p then u else 0)) = M i p * u := by
  have h0 : ∀ b ∈ (Finset.univ : Finset ι), b ≠ p →
      M i b * (if b = p then u else 0) = 0 := by
    intro b _ hb
    rw [if_neg hb, mul_zero]
  rw [Finset.sum_eq_single_of_mem p (Finset.mem_univ p) h0]
  simp

/-- A row of a matrix against a two-point vector. -/
theorem sum_mul_twoPoint (M : Matrix ι ι R) (i p q : ι) (u w : R) :
    (∑ m, M i m * twoPoint p q u w m) = M i p * u + M i q * w := by
  have hsplit : (∑ m, M i m * twoPoint p q u w m)
      = ∑ m, (M i m * (if m = p then u else 0) + M i m * (if m = q then w else 0)) := by
    refine Finset.sum_congr rfl ?_
    intro m _
    simp only [twoPoint_apply, mul_add]
  rw [hsplit, Finset.sum_add_distrib, sum_mul_indicator M i p u, sum_mul_indicator M i q w]

/-! ### Re-indexing the exchange refinement -/

omit [DecidableEq ι] in
/-- `HasFiniteRightExchangePartitions` re-indexed along an arbitrary `Fintype`.
The matrix calculus indexes rows by `ι`, while the exchange property is stated
for `Fin n`.

This duplicates `ExchangePrerequisite.exists_orthogonal_refinement` from the
sibling exchange task; it is repeated here only so that this file compiles
without importing that file. -/
theorem exists_orthogonalRefinement
    (hex : ExchangePrerequisite.HasFiniteRightExchangePartitions R)
    (x : ι → R) (hsum : (∑ p, x p) = 1) :
    ∃ e r : ι → R,
      (∀ p, IsIdempotentElem (e p)) ∧
      (∀ p q, p ≠ q → e p * e q = 0) ∧
      (∀ p, e p = x p * r p) ∧
      (∑ p, e p) = 1 := by
  obtain ⟨ε⟩ : Nonempty (ι ≃ Fin (Fintype.card ι)) := ⟨Fintype.equivFin ι⟩
  have hsum' : (∑ n : Fin (Fintype.card ι), x (ε.symm n)) = 1 := by
    rw [Equiv.sum_comp ε.symm x]
    exact hsum
  obtain ⟨e, r, hidem, horth, heq, hesum⟩ :=
    hex (Fintype.card ι) (fun n => x (ε.symm n)) hsum'
  refine ⟨fun p => e (ε p), fun p => r (ε p), fun p => hidem _, ?_, ?_, ?_⟩
  · intro p q hpq
    exact horth _ _ fun hcon => hpq (ε.injective hcon)
  · intro p
    have hp := heq (ε p)
    simp only [Equiv.symm_apply_apply] at hp
    exact hp
  · rw [← hesum]
    exact Equiv.sum_comp ε fun n => e n

/-! ### Proposition 21(i): off-diagonal entries -/

/-- **Preusser's Proposition 21(i), in membership form.**

Every off-diagonal entry of every element of `N` lies in the transvection level
of `N`.

The proof is Preusser's.  Exchange is applied to `∑_p σ_ip σ'_pi = 1`, giving
idempotents `e_p = σ_ip σ'_pi r_p` summing to `1`.  For `p ≠ i` the identity
`e_p (σ_ii - e_p σ_ii) = 0` feeds Proposition 20 along the vector with `1` in
slot `i` and `-σ'_pi r_p σ_ii` in slot `p`, giving `e_p` in the level; the
identity `e_i (σ_ij - e_i σ_ij) = 0` feeds Proposition 20 along the vector with
`1` in slot `j` and `-σ'_ii r_i σ_ij` in slot `i`, giving
`e_i σ'_ii r_i σ_ij` in the level.  Adding the `2 · card ι` pieces of
`σ_ij = σ_ii (∑_p e_p) σ'_ii r_i σ_ij + (∑_{p ≠ i} e_p) σ_ij`
finishes it.

Hypotheses: `hex` is owed by the exchange-refinement task, `hprop20` by the
Proposition 20 task.  Normality of `N` is not used here (it is used inside
`hprop20`, and in part (ii) below).  No cardinality bound on `ι` is used
either; Preusser's `n ≥ 3` enters through `hprop20`. -/
theorem transvectionLevel_entry
    (hex : ExchangePrerequisite.HasFiniteRightExchangePartitions R)
    (N : Subgroup (elementaryGroup ι R))
    (hprop20 : RowAnnihilatorTransvection N)
    {g : elementaryGroup ι R} (hg : g ∈ N) {i j : ι} (hij : i ≠ j) :
    TransvectionLevel N (elMat g i j) := by
  have hrow : (∑ p, elMat g i p * elMat (g⁻¹) p i) = 1 := by
    have h2 : (elMat g * elMat (g⁻¹)) i i = (1 : Matrix ι ι R) i i := by
      rw [elMat_mul_inv g]
    rwa [Matrix.mul_apply, Matrix.one_apply_eq] at h2
  obtain ⟨e, r, hidem, -, heq, hesum⟩ :=
    exists_orthogonalRefinement hex (fun p => elMat g i p * elMat (g⁻¹) p i) hrow
  have heqi : e i = elMat g i i * elMat (g⁻¹) i i * r i := heq i
  -- Preusser's step (5): for `p ≠ i` the idempotent `e p` is in the level.
  have hstep5 : ∀ p, p ≠ i → TransvectionLevel N (e p) := by
    intro p hpi
    have hip : i ≠ p := Ne.symm hpi
    have heqp : e p = elMat g i p * elMat (g⁻¹) p i * r p := heq p
    have hxi : twoPoint i p (1 : R) (-(elMat (g⁻¹) p i * r p * elMat g i i)) i = 1 :=
      twoPoint_fst hip _ _
    have hsum : (∑ m, elMat g i m *
          twoPoint i p (1 : R) (-(elMat (g⁻¹) p i * r p * elMat g i i)) m)
        = elMat g i i - e p * elMat g i i := by
      rw [sum_mul_twoPoint (elMat g) i i p (1 : R)
        (-(elMat (g⁻¹) p i * r p * elMat g i i)), heqp]
      noncomm_ring
    have hann : e p * (∑ m, elMat g i m *
          twoPoint i p (1 : R) (-(elMat (g⁻¹) p i * r p * elMat g i i)) m) = 0 := by
      rw [hsum, mul_sub, ← mul_assoc (e p) (e p) (elMat g i i), (hidem p).eq, sub_self]
    have hres := transvectionLevel_of_prop20 hprop20 hg i i
      (twoPoint i p (1 : R) (-(elMat (g⁻¹) p i * r p * elMat g i i))) (e p) hxi hann
    rwa [hxi, mul_one] at hres
  -- Preusser's step (6): the `i`-th piece, corrected by `σ'_ii r_i σ_ij`.
  have hstep6 : TransvectionLevel N (e i * (elMat (g⁻¹) i i * r i * elMat g i j)) := by
    have hji : j ≠ i := Ne.symm hij
    have hxj : twoPoint j i (1 : R) (-(elMat (g⁻¹) i i * r i * elMat g i j)) j = 1 :=
      twoPoint_fst hji _ _
    have hxi : twoPoint j i (1 : R) (-(elMat (g⁻¹) i i * r i * elMat g i j)) i
        = -(elMat (g⁻¹) i i * r i * elMat g i j) := twoPoint_snd hji _ _
    have hsum : (∑ m, elMat g i m *
          twoPoint j i (1 : R) (-(elMat (g⁻¹) i i * r i * elMat g i j)) m)
        = elMat g i j - e i * elMat g i j := by
      rw [sum_mul_twoPoint (elMat g) i j i (1 : R)
        (-(elMat (g⁻¹) i i * r i * elMat g i j)), heqi]
      noncomm_ring
    have hann : e i * (∑ m, elMat g i m *
          twoPoint j i (1 : R) (-(elMat (g⁻¹) i i * r i * elMat g i j)) m) = 0 := by
      rw [hsum, mul_sub, ← mul_assoc (e i) (e i) (elMat g i j), (hidem i).eq, sub_self]
    have hres := transvectionLevel_of_prop20 hprop20 hg i j
      (twoPoint j i (1 : R) (-(elMat (g⁻¹) i i * r i * elMat g i j))) (e i) hxj hann
    rw [hxi] at hres
    have hneg : e i * -(elMat (g⁻¹) i i * r i * elMat g i j)
        = -(e i * (elMat (g⁻¹) i i * r i * elMat g i j)) := by noncomm_ring
    rw [hneg] at hres
    have hfin := hres.neg
    rwa [neg_neg] at hfin
  -- The `card ι` pieces carrying the correction factor.
  have hA : TransvectionLevel N
      (∑ p, elMat g i i * e p * (elMat (g⁻¹) i i * r i * elMat g i j)) := by
    refine TransvectionLevel.sum ?_
    intro p _
    by_cases hpi : p = i
    · rw [hpi]
      have h6 := hstep6.mul_left (elMat g i i)
      have hassoc : elMat g i i * (e i * (elMat (g⁻¹) i i * r i * elMat g i j))
          = elMat g i i * e i * (elMat (g⁻¹) i i * r i * elMat g i j) := by noncomm_ring
      rwa [hassoc] at h6
    · exact ((hstep5 p hpi).mul_left (elMat g i i)).mul_right
        (elMat (g⁻¹) i i * r i * elMat g i j)
  have hAval : (∑ p, elMat g i i * e p * (elMat (g⁻¹) i i * r i * elMat g i j))
      = e i * elMat g i j := by
    have hfac : elMat g i i * (∑ p, e p) * (elMat (g⁻¹) i i * r i * elMat g i j)
        = ∑ p, elMat g i i * e p * (elMat (g⁻¹) i i * r i * elMat g i j) := by
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [← hfac, hesum, mul_one, heqi]
    noncomm_ring
  -- The `card ι - 1` remaining pieces.
  have hB : TransvectionLevel N (∑ p ∈ Finset.univ.erase i, e p * elMat g i j) := by
    refine TransvectionLevel.sum ?_
    intro p hp
    exact (hstep5 p (Finset.ne_of_mem_erase hp)).mul_right (elMat g i j)
  have hBval : (∑ p ∈ Finset.univ.erase i, e p * elMat g i j)
      = elMat g i j - e i * elMat g i j := by
    rw [← Finset.sum_mul, Finset.sum_erase_eq_sub (Finset.mem_univ i), hesum, sub_mul,
      one_mul]
  have hfinal := hA.add hB
  rw [hAval, hBval] at hfinal
  have hval : e i * elMat g i j + (elMat g i j - e i * elMat g i j) = elMat g i j := by
    noncomm_ring
  rwa [hval] at hfinal

/-! ### Proposition 21(ii): diagonal differences -/

/-- **Preusser's Proposition 21(ii), off-diagonal case.**

For `i ≠ j` and every `c`, the diagonal difference `c σ_ii - σ_jj c` lies in the
transvection level of `N`.

Preusser's argument: the `(j, i)` entry of the elementary conjugate
`e_{ji}(c) g e_{ji}(c)⁻¹` is `σ_ji + c σ_ii - σ_jj c - c σ_ij c`.  Part (i)
applied to that conjugate, to `g` at `(j, i)`, and to `g` at `(i, j)` puts three
of the four summands in the level, leaving `c σ_ii - σ_jj c`.

Normality of `N` is used here, and only here: it is what puts the elementary
conjugate back into `N`. -/
theorem transvectionLevel_diagDiff_of_ne
    (hex : ExchangePrerequisite.HasFiniteRightExchangePartitions R)
    (N : Subgroup (elementaryGroup ι R)) [hN : N.Normal]
    (hprop20 : RowAnnihilatorTransvection N)
    {g : elementaryGroup ι R} (hg : g ∈ N) {i j : ι} (hij : i ≠ j) (c : R) :
    TransvectionLevel N (c * elMat g i i - elMat g j j * c) := by
  have hji : j ≠ i := Ne.symm hij
  have hgt : elGen j i hji c * g * (elGen j i hji c)⁻¹ ∈ N :=
    hN.conj_mem g hg (elGen j i hji c)
  have hM : elMat (elGen j i hji c * g * (elGen j i hji c)⁻¹)
      = (1 + Matrix.single j i c) * elMat g * (1 - Matrix.single j i c) := by
    rw [elMat_mul, elMat_mul, elMat_elGen, elMat_elGen_inv]
  have hexp : (1 + Matrix.single j i c) * elMat g * (1 - Matrix.single j i c)
      = elMat g + Matrix.single j i c * elMat g - elMat g * Matrix.single j i c
        - Matrix.single j i c * elMat g * Matrix.single j i c := by
    noncomm_ring
  have hentry : elMat (elGen j i hji c * g * (elGen j i hji c)⁻¹) j i
      = elMat g j i + c * elMat g i i - elMat g j j * c - c * elMat g i j * c := by
    rw [hM, hexp]
    simp
  have h1 : TransvectionLevel N
      (elMat (elGen j i hji c * g * (elGen j i hji c)⁻¹) j i) :=
    transvectionLevel_entry hex N hprop20 hgt hji
  rw [hentry] at h1
  have h2 : TransvectionLevel N (elMat g j i) :=
    transvectionLevel_entry hex N hprop20 hg hji
  have h3 : TransvectionLevel N (elMat g i j) :=
    transvectionLevel_entry hex N hprop20 hg hij
  have h4 : TransvectionLevel N (c * elMat g i j * c) := (h3.mul_left c).mul_right c
  have h5 := (h1.sub h2).add h4
  have hval : elMat g j i + c * elMat g i i - elMat g j j * c - c * elMat g i j * c
      - elMat g j i + c * elMat g i j * c
      = c * elMat g i i - elMat g j j * c := by
    noncomm_ring
  rwa [hval] at h5

/-- **Preusser's Proposition 21(ii)**, with the restriction `i ≠ j` removed.

The congruence-subgroup description quantifies the diagonal clause over all
pairs `i j`, the diagonal pair included, so the case `i = j` is needed.  It
follows from two instances of the off-diagonal case through a third index `m`:
`c σ_ii - σ_ii c = (c σ_ii - σ_mm c) + (σ_mm - σ_ii) c`.  This is the only place
`3 ≤ Fintype.card ι` is used in this file; `1 < Fintype.card ι` would do. -/
theorem transvectionLevel_diagDiff (hcard : 3 ≤ Fintype.card ι)
    (hex : ExchangePrerequisite.HasFiniteRightExchangePartitions R)
    (N : Subgroup (elementaryGroup ι R)) [N.Normal]
    (hprop20 : RowAnnihilatorTransvection N)
    {g : elementaryGroup ι R} (hg : g ∈ N) (i j : ι) (c : R) :
    TransvectionLevel N (c * elMat g i i - elMat g j j * c) := by
  by_cases hij : i = j
  · obtain ⟨m, hmi, -⟩ := exists_third_index hcard i i
    have hA := transvectionLevel_diagDiff_of_ne hex N hprop20 hg (Ne.symm hmi) c
    have hB := transvectionLevel_diagDiff_of_ne hex N hprop20 hg hmi (1 : R)
    have hsum := hA.add (hB.mul_right c)
    have hval : c * elMat g i i - elMat g m m * c
        + (1 * elMat g m m - elMat g i i * 1) * c
        = c * elMat g i i - elMat g i i * c := by
      noncomm_ring
    rw [hval] at hsum
    rw [← hij]
    exact hsum
  · exact transvectionLevel_diagDiff_of_ne hex N hprop20 hg hij c

/-! ### The named endpoints

These are the two clauses of Preusser's Proposition 21 in exactly the shape the
assembly step consumes.  The primed variants set both coefficients to `1`, which
is the form `mem_normalLevel_iff` (`Leavitt.CongruenceSubgroups`) asks for. -/

/-- **Preusser, Proposition 21(i).**  For `i ≠ j`, the entry `σ_ij` of an
element of a normal subgroup produces elementary roots in that subgroup, in
every position and with every pair of coefficients.

`_hcard` is unused: see the module docstring.  `hex` and `hprop20` are the two
leading binders owed by the exchange-refinement and Proposition 20 tasks. -/
theorem elGen_entry_mem (_hcard : 3 ≤ Fintype.card ι)
    (hex : ExchangePrerequisite.HasFiniteRightExchangePartitions R)
    (N : Subgroup (elementaryGroup ι R))
    (hprop20 : RowAnnihilatorTransvection N)
    {g : elementaryGroup ι R} (hg : g ∈ N) {i j : ι} (hij : i ≠ j)
    {k l : ι} (hkl : k ≠ l) (a b : R) :
    elGen k l hkl (a * elMat g i j * b) ∈ N :=
  transvectionLevel_entry hex N hprop20 hg hij k l hkl a b

/-- The coefficient-free form of Proposition 21(i). -/
theorem elGen_elMat_mem (hcard : 3 ≤ Fintype.card ι)
    (hex : ExchangePrerequisite.HasFiniteRightExchangePartitions R)
    (N : Subgroup (elementaryGroup ι R))
    (hprop20 : RowAnnihilatorTransvection N)
    {g : elementaryGroup ι R} (hg : g ∈ N) {i j : ι} (hij : i ≠ j)
    {k l : ι} (hkl : k ≠ l) :
    elGen k l hkl (elMat g i j) ∈ N := by
  have h := elGen_entry_mem hcard hex N hprop20 hg hij hkl 1 1
  rwa [one_mul, mul_one] at h

/-- **Preusser, Proposition 21(ii).**  The diagonal differences
`c σ_ii - σ_jj c` of an element of a normal subgroup produce elementary roots in
that subgroup.  No restriction on `i` and `j`. -/
theorem elGen_diag_diff_mem (hcard : 3 ≤ Fintype.card ι)
    (hex : ExchangePrerequisite.HasFiniteRightExchangePartitions R)
    (N : Subgroup (elementaryGroup ι R)) [N.Normal]
    (hprop20 : RowAnnihilatorTransvection N)
    {g : elementaryGroup ι R} (hg : g ∈ N) (i j : ι) (c : R)
    {k l : ι} (hkl : k ≠ l) (a b : R) :
    elGen k l hkl (a * (c * elMat g i i - elMat g j j * c) * b) ∈ N :=
  transvectionLevel_diagDiff hcard hex N hprop20 hg i j c k l hkl a b

/-- The coefficient-free form of Proposition 21(ii). -/
theorem elGen_diagDiff_mem (hcard : 3 ≤ Fintype.card ι)
    (hex : ExchangePrerequisite.HasFiniteRightExchangePartitions R)
    (N : Subgroup (elementaryGroup ι R)) [N.Normal]
    (hprop20 : RowAnnihilatorTransvection N)
    {g : elementaryGroup ι R} (hg : g ∈ N) (i j : ι) (c : R)
    {k l : ι} (hkl : k ≠ l) :
    elGen k l hkl (c * elMat g i i - elMat g j j * c) ∈ N := by
  have h := elGen_diag_diff_mem hcard hex N hprop20 hg i j c hkl 1 1
  rwa [one_mul, mul_one] at h

/-! ### The `∀ N` forms

The assembly step quantifies both clauses of Proposition 21 over all normal
subgroups at once.  The Proposition 20 input is quantified the same way, which
is exactly the shape of the sibling task's theorem (`N` is a binder there).

Note the `hij : i ≠ j` in the first conclusion.  It cannot be dropped: with
`N = ⊥`, `g = 1` and `i = j` the claim would read `elGen k l hkl (a * b) ∈ ⊥`
for all `a b`, i.e. `a * b = 0` for all `a b`, which fails in any nontrivial
ring.  Preusser states Proposition 21 with `i ≠ j` for this reason.  The
diagonal clause below, by contrast, does hold for all pairs, `i = j` included,
and is stated that way. -/

/-- **Preusser, Proposition 21(i), over all normal subgroups.** -/
theorem prop21Entry_of_prop20 (hcard : 3 ≤ Fintype.card ι)
    (hex : ExchangePrerequisite.HasFiniteRightExchangePartitions R)
    (h20 : ∀ (N : Subgroup (elementaryGroup ι R)), N.Normal →
      RowAnnihilatorTransvection N) :
    ∀ (N : Subgroup (elementaryGroup ι R)), N.Normal →
      ∀ (g : elementaryGroup ι R), g ∈ N →
        ∀ (i j : ι), i ≠ j →
          ∀ (k l : ι) (hkl : k ≠ l) (a b : R),
            elGen k l hkl (a * elMat g i j * b) ∈ N := by
  intro N hN g hg i j hij k l hkl a b
  exact elGen_entry_mem hcard hex N (h20 N hN) hg hij hkl a b

/-- **Preusser, Proposition 21(ii), over all normal subgroups.**  Stated with no
restriction on `i` and `j`, which is the form the entrywise description of the
congruence subgroup consumes. -/
theorem prop21DiagDiff_of_prop20 (hcard : 3 ≤ Fintype.card ι)
    (hex : ExchangePrerequisite.HasFiniteRightExchangePartitions R)
    (h20 : ∀ (N : Subgroup (elementaryGroup ι R)), N.Normal →
      RowAnnihilatorTransvection N) :
    ∀ (N : Subgroup (elementaryGroup ι R)), N.Normal →
      ∀ (g : elementaryGroup ι R), g ∈ N →
        ∀ (i j : ι) (c : R) (k l : ι) (hkl : k ≠ l) (a b : R),
          elGen k l hkl (a * (c * elMat g i i - elMat g j j * c) * b) ∈ N := by
  intro N hN g hg i j c k l hkl a b
  haveI := hN
  exact elGen_diag_diff_mem hcard hex N (h20 N hN) hg i j c hkl a b

end PreusserSandwich

end GroupApproximation
