import GroupApproximation.Leavitt.ElementarySimplicity
import GroupApproximation.Leavitt.ElementaryTransvectionExtraction

/-!
# Row annihilators produce prescribed transvections: the congruence decomposition

This module proves Preusser's Proposition 20 (arXiv:1912.11386) for `EL_ι(R)`:
if `σ` lies in a normal subgroup `N` of `EL_ι(R)` and `y · Σ_p σ_{ip} x_p = 0`
for a coefficient vector `x` with `x_j = 1`, then `t_{kl}(a · y · x_i · b) ∈ N`
for every `k ≠ l` and all `a, b ∈ R`.

The decomposition here is deliberately different from the one in
`Leavitt.RowAnnihilatorTransvection`, which attacks the same target head on.
Three layers are separated, and each is independently meaningful:

## Layer 1 — group theory, ring-free

Nothing about matrices enters here.  The two lemmas replace the whole of
Preusser's Lemma 19 (whose content is a *count* of conjugates, irrelevant to
membership):

* `conj_congr_mem`: the map `h ↦ h⁻¹ t h` is constant on cosets of `N`.  This is
  the reason the reduction word starts inside `N` at all, and it is a statement
  about conjugation, not about commutators.
* `commutator_congr_mem`: `u ↦ ⁅u, f⁆` is constant on cosets of `N`, in the form
  `⁅u, f⁆ * ⁅f, v⁆ ∈ N`.  Proved by pushing to `G ⧸ N` and using the identity
  `⁅x, y⁆ * ⁅y, x⁆ = 1`, so no explicit word rearrangement is needed.

## Layer 2 — the ring content, stated for abstract defects

`elGen_mem_of_rowCol_pair` is the load-bearing lemma.  It takes *two arbitrary
elements* `u, v` of `EL_ι(R)` that are congruent mod `N`, whose matrices are
`1 + V` and `1 + W`, and asks only two things of the defects:

* `V` is supported in row `r` and vanishes on the diagonal there;
* `W` has vanishing `j`-th column.

From that alone it produces `t_{js}(a · V_{rj} · b) ∈ N`.  No `σ`, no
coefficient vector, no column matrix appears: the two-step commutator word and
all four degeneracy computations live here and nowhere else.

## Layer 3 — the two supplies

* `exists_colElem` builds an element of `EL_ι(R)` with prescribed `j`-th column,
  as an existential (so no `Classical.choose` and no square-zero bookkeeping
  leaks into the definitions); its induction runs inside the group, one factor
  `t_{pj}(x_p)` at a time.
* `elGen_mem_of_column_annihilator` feeds `u := τ⁻¹ t_{ri}(y) τ` and
  `v := (στ)⁻¹ t_{ri}(y) (στ)` to Layer 2; the annihilation hypothesis is
  exactly the vanishing of the `j`-th column of the second defect.
* `elGen_mem_of_base` spreads one position to all positions by the Steinberg
  relation, factored through the two one-step lemmas `elGen_mem_extend_left`
  and `elGen_mem_extend_right`.

`forall_elGen_mem_of_row_annihilator` states the result in the exact shape a
consumer of Proposition 21 needs (`∀ h ∈ N, …`).
-/

namespace GroupApproximation

namespace RowAnnihilatorAlt

open ElementarySimplicity

open scoped BigOperators commutatorElement

/-! ## Layer 1: congruence mod a normal subgroup

Both lemmas say that a construction is constant on cosets of `N`.  They are the
only group-theoretic input to the whole file. -/

section GroupLayer

variable {G : Type*} [Group G]

/-- A commutator and its swap are inverse to each other. -/
theorem commutator_mul_swap (u v : G) : ⁅u, v⁆ * ⁅v, u⁆ = 1 := by
  simp only [commutatorElement_def]
  group

variable (N : Subgroup G) [hN : N.Normal]

/-- A commutator whose *right* entry lies in a normal subgroup lies in it. -/
theorem commutator_right_mem (x : G) {n : G} (hn : n ∈ N) : ⁅x, n⁆ ∈ N := by
  rw [commutatorElement_def]
  exact N.mul_mem (hN.conj_mem n hn x) (N.inv_mem hn)

/-- **Conjugation is constant on cosets.**  If `h₁` and `h₂` are congruent mod
`N` then so are `h₁⁻¹ t h₁` and `h₂⁻¹ t h₂`, for every `t`.

This is what makes the reduction word of Proposition 20 start inside `N`: the
two conjugating elements there are `τ` and `στ`, which differ by `σ ∈ N`. -/
theorem conj_congr_mem {h₁ h₂ : G} (hc : h₁ * h₂⁻¹ ∈ N) (t : G) :
    (h₁⁻¹ * t * h₁)⁻¹ * (h₂⁻¹ * t * h₂) ∈ N := by
  have key : (h₁⁻¹ * t * h₁)⁻¹ * (h₂⁻¹ * t * h₂)
      = h₁⁻¹ * (t⁻¹ * (h₁ * h₂⁻¹) * t * (h₁ * h₂⁻¹)⁻¹) * h₁ := by
    group
  rw [key]
  exact hN.conj_mem' _ (N.mul_mem (hN.conj_mem' _ hc t) (N.inv_mem hc)) h₁

/-- **Commutation is constant on cosets.**  If `u` and `v` are congruent mod `N`
then `⁅u, f⁆ * ⁅f, v⁆ ∈ N` for every `f`.

This is the membership form of Preusser's Lemma 19.  The published lemma tracks
how many conjugates of the original element are needed; membership in a normal
subgroup does not see that count, and in the quotient the statement is just
`⁅x, f⁆ * ⁅f, x⁆ = 1`. -/
theorem commutator_congr_mem {u v : G} (huv : u⁻¹ * v ∈ N) (f : G) :
    ⁅u, f⁆ * ⁅f, v⁆ ∈ N := by
  have hq : (QuotientGroup.mk' N) v = (QuotientGroup.mk' N) u := by
    have h1 : (QuotientGroup.mk' N) (u⁻¹) * (QuotientGroup.mk' N) v = 1 := by
      rw [← map_mul]
      exact (QuotientGroup.eq_one_iff (u⁻¹ * v)).mpr huv
    rw [map_inv] at h1
    exact (inv_mul_eq_one.mp h1).symm
  refine (QuotientGroup.eq_one_iff _).mp ?_
  show (QuotientGroup.mk' N) (⁅u, f⁆ * ⁅f, v⁆) = 1
  rw [map_mul, map_commutatorElement, map_commutatorElement, hq]
  exact commutator_mul_swap _ _

/-- `commutator_congr_mem` in the form produced by a previous application of
itself: the hypothesis arrives as a product rather than as `u⁻¹ * v`. -/
theorem commutator_congr_mem' {u v : G} (huv : u * v ∈ N) (f : G) :
    ⁅u⁻¹, f⁆ * ⁅f, v⁆ ∈ N :=
  commutator_congr_mem N (by rwa [inv_inv]) f

end GroupLayer

/-! ## Layer 2: the matrix calculus -/

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- The inverse of an elementary generator negates its coefficient. -/
theorem elGen_inv (i j : ι) (h : i ≠ j) (a : R) :
    (elGen (R := R) i j h a)⁻¹ = elGen i j h (-a) :=
  inv_eq_of_mul_eq_one_right (by rw [elGen_mul, add_neg_cancel, elGen_zero])

/-- The matrix of a commutator in `EL_ι(R)`. -/
theorem elMat_commutator (u v : elementaryGroup ι R) :
    elMat ⁅u, v⁆ = elMat u * elMat v * elMat (u⁻¹) * elMat (v⁻¹) := by
  rw [commutatorElement_def, elMat_mul, elMat_mul, elMat_mul]

/-- **The inverse of a unipotent with square-zero defect.**  Knowing the matrix
of `u` is `1 + A` with `A * A = 0` pins the matrix of `u⁻¹` to `1 - A`, without
having to produce `u` as a `sqZeroUnit` in the first place. -/
theorem elMat_inv_of_sqZero {u : elementaryGroup ι R} {A : Matrix ι ι R}
    (hu : elMat u = 1 + A) (hA : A * A = 0) : elMat (u⁻¹) = 1 - A := by
  have h2 : (1 + A) * (1 - A) = 1 := by
    have e : (1 + A) * (1 - A) = 1 - A * A := by noncomm_ring
    rw [e, hA, sub_zero]
  calc elMat (u⁻¹) = elMat (u⁻¹) * ((1 + A) * (1 - A)) := by rw [h2, mul_one]
    _ = elMat (u⁻¹) * elMat u * (1 - A) := by rw [hu, ← mul_assoc]
    _ = 1 - A := by rw [elMat_inv_mul, one_mul]

/-- **The sandwich entry formula.**  `(M E_{ri}(y) M')_{pq} = M_{pr} (y M'_{iq})`.
The right-hand parenthesisation is the one an annihilation hypothesis
`y * M'_{ij} = 0` discharges directly. -/
theorem sandwich_apply (M M' : Matrix ι ι R) (r i : ι) (y : R) (p q : ι) :
    (M * Matrix.single r i y * M') p q = M p r * (y * M' i q) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [matrix_mul_single_apply, if_pos rfl, mul_assoc]
  · intro m _ hm
    rw [matrix_mul_single_apply, if_neg hm, zero_mul]
  · intro hcon
    exact absurd (Finset.mem_univ i) hcon

/-- The defect of a conjugated off-diagonal root squares to zero. -/
theorem sandwich_mul_self (M M' : Matrix ι ι R) (h : M' * M = 1) (r i : ι)
    (hri : r ≠ i) (y : R) :
    (M * Matrix.single r i y * M') * (M * Matrix.single r i y * M') = 0 := by
  have e : (M * Matrix.single r i y * M') * (M * Matrix.single r i y * M')
      = M * (Matrix.single r i y * (M' * M) * Matrix.single r i y) * M' := by
    noncomm_ring
  rw [e, h, mul_one, single_mul_self_eq_zero r i hri y, mul_zero, zero_mul]

/-- **The production lemma.**  Let `u, v ∈ EL_ι(R)` be congruent mod a normal
subgroup `N`, with matrices `1 + V` and `1 + W`.  If `V` is a one-row defect in
row `r` with vanishing diagonal entry, and the `j`-th column of `W` vanishes,
then `t_{js}(a · V_{rj} · b) ∈ N` for all `a, b`.

This is the entire content of Preusser's Proposition 20 stripped of the
particular `σ` and coefficient vector that produce `u`, `v`, `V` and `W`.  The
proof is two applications of `commutator_congr_mem`: the first turns the pair
`(u, v)` into `(t_{rs}(V_{rj} b), 1 + E_{js}(b) W)`, whose second coordinate is
again a one-row defect but now with a *vanishing* diagonal entry; the second
kills that coordinate outright and gains the left coefficient `a`. -/
theorem elGen_mem_of_rowCol_pair
    (N : Subgroup (elementaryGroup ι R)) [N.Normal]
    {u v : elementaryGroup ι R} (huv : u⁻¹ * v ∈ N)
    {V W : Matrix ι ι R} (hu : elMat u = 1 + V) (hv : elMat v = 1 + W)
    {r j s : ι} (hrj : r ≠ j) (hsr : s ≠ r) (hjs : j ≠ s)
    (hVrow : IsRowSupported V r) (hVrr : V r r = 0)
    (hWW : W * W = 0) (hWcol : ∀ p : ι, W p j = 0) (a b : R) :
    elGen j s hjs (a * (V r j * b)) ∈ N := by
  have hjr : j ≠ r := Ne.symm hrj
  have hrs : r ≠ s := Ne.symm hsr
  -- the two defects and their inverses
  have hVV : V * V = 0 := hVrow.mul_self hVrr
  have huinv : elMat (u⁻¹) = 1 - V := elMat_inv_of_sqZero hu hVV
  have hvinv : elMat (v⁻¹) = 1 - W := elMat_inv_of_sqZero hv hWW
  have hFF : Matrix.single j s b * Matrix.single j s b = 0 :=
    single_mul_self_eq_zero j s hjs b
  have hGG : Matrix.single j r a * Matrix.single j r a = 0 :=
    single_mul_self_eq_zero j r hjr a
  -- the four degeneracies
  have hFV : Matrix.single j s b * V = 0 := single_mul_row_eq_zero V hVrow hsr b
  have hWF : W * Matrix.single j s b = 0 := by
    ext p q
    rw [matrix_mul_single_apply, Matrix.zero_apply]
    by_cases hq : q = s
    · rw [if_pos hq, hWcol p, zero_mul]
    · rw [if_neg hq]
  have hZrow : IsRowSupported (Matrix.single j s b * W) j := by
    intro p q hp
    rw [matrix_single_mul_apply, if_neg hp]
  have hZjj : (Matrix.single j s b * W) j j = 0 := by
    rw [matrix_single_mul_apply, if_pos rfl, hWcol s, mul_zero]
  have hZZ : (Matrix.single j s b * W) * (Matrix.single j s b * W) = 0 :=
    hZrow.mul_self hZjj
  have hGZ : Matrix.single j r a * (Matrix.single j s b * W) = 0 :=
    single_mul_row_eq_zero _ hZrow hrj a
  have hZG : (Matrix.single j s b * W) * Matrix.single j r a = 0 := by
    rw [row_mul_single _ hZrow j r a, hZjj, zero_mul, single_zero_coeff]
  -- first step of the reduction word
  have h1 := commutator_congr_mem N huv (elGen j s hjs b)
  have hc1 : ⁅u, elGen j s hjs b⁆ = elGen r s hrs (V r j * b) := by
    apply elMat_injective
    rw [elMat_commutator u (elGen j s hjs b), hu, huinv,
      elMat_elGen j s hjs b, elMat_elGen_inv j s hjs b,
      elMat_elGen r s hrs (V r j * b),
      unipotent_commutator_of_right_annihilates _ _ hVV hFF hFV,
      row_mul_single _ hVrow j s b]
  have hc2 : elMat ⁅elGen j s hjs b, v⁆ = 1 + Matrix.single j s b * W := by
    rw [elMat_commutator (elGen j s hjs b) v, elMat_elGen j s hjs b,
      elMat_elGen_inv j s hjs b, hv, hvinv]
    exact unipotent_commutator_of_right_annihilates _ _ hFF hWW hWF
  have hc2inv : elMat (⁅elGen j s hjs b, v⁆⁻¹) = 1 - Matrix.single j s b * W :=
    elMat_inv_of_sqZero hc2 hZZ
  -- second step: the junk coordinate dies, the good one gains `a`
  have h2 := commutator_congr_mem' N h1 (elGen j r hjr a)
  have hc3 : ⁅elGen j r hjr a, ⁅elGen j s hjs b, v⁆⁆ = (1 : elementaryGroup ι R) := by
    apply elMat_injective
    rw [elMat_commutator (elGen j r hjr a), elMat_elGen j r hjr a,
      elMat_elGen_inv j r hjr a, hc2, hc2inv, elMat_one,
      unipotent_commutator _ _ hGG hZZ, hGZ, hZG]
    simp
  have hc4 : ⁅(elGen r s hrs (V r j * b))⁻¹, elGen j r hjr a⁆
      = elGen j s hjs (a * (V r j * b)) := by
    rw [← commutatorElement_inv (elGen j r hjr a) ((elGen r s hrs (V r j * b))⁻¹),
      elGen_inv r s hrs (V r j * b), commutatorElement_def,
      elGen_commutator j r s hjr hrs hjs a (-(V r j * b)),
      elGen_inv j s hjs (a * -(V r j * b)), mul_neg, neg_neg]
  rwa [hc1, hc3, mul_one, hc4] at h2

/-! ## Layer 3a: an element of `EL_ι(R)` with prescribed column

Preusser's argument replaces `σ` by `στ` where `τ = ∏_{p ≠ j} t_{pj}(x_p)`.
Only two facts about `τ` are ever used: its `j`-th column is `x`, and its other
columns are those of the identity.  Both are packaged into one existential, so
that no auxiliary definition — and in particular no `Classical.choose` — is
needed downstream. -/

omit [Fintype ι] in
/-- Entry formula for a partial column sum of single-entry matrices. -/
theorem colSum_apply (j : ι) (x : ι → R) (s : Finset ι) (p q : ι) :
    (∑ m ∈ s, Matrix.single m j (x m)) p q =
      if q = j then (if p ∈ s then x p else 0) else 0 := by
  rw [Matrix.sum_apply]
  by_cases hq : q = j
  · rw [if_pos hq]
    by_cases hp : p ∈ s
    · rw [if_pos hp, Finset.sum_eq_single p]
      · rw [Matrix.single_apply, if_pos ⟨rfl, hq.symm⟩]
      · intro m _ hmp
        rw [Matrix.single_apply, if_neg (fun hh => hmp hh.1)]
      · intro hcon
        exact absurd hp hcon
    · rw [if_neg hp]
      refine Finset.sum_eq_zero fun m hm => ?_
      rw [Matrix.single_apply]
      refine if_neg ?_
      rintro ⟨rfl, -⟩
      exact hp hm
  · rw [if_neg hq]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [Matrix.single_apply]
    exact if_neg (fun hh => hq hh.2.symm)

/-- The partial column matrices are elementary.  The induction peels off one
factor `t_{pj}(x_p)` at a time; the peeled factor annihilates the remaining sum
because row `j` of that sum vanishes. -/
theorem exists_elem_colSum (j : ι) (x : ι → R) :
    ∀ s : Finset ι, j ∉ s →
      ∃ τ : elementaryGroup ι R,
        elMat τ = 1 + ∑ m ∈ s, Matrix.single m j (x m) := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro _
      exact ⟨1, by rw [elMat_one, Finset.sum_empty, add_zero]⟩
  | insert p s hps ih =>
      intro hj
      have hjp : j ≠ p := fun h => hj (Finset.mem_insert.mpr (Or.inl h))
      have hjs : j ∉ s := fun h => hj (Finset.mem_insert.mpr (Or.inr h))
      have hpj : p ≠ j := fun h => hjp h.symm
      obtain ⟨τ', hτ'⟩ := ih hjs
      have hzero :
          Matrix.single p j (x p) * (∑ m ∈ s, Matrix.single m j (x m)) = 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_eq_zero fun m hm => ?_
        have hjm : j ≠ m := by
          intro hcon
          apply hjs
          rw [hcon]
          exact hm
        exact Matrix.single_mul_single_of_ne (c := x p) p j m hjm (x m)
      refine ⟨elGen p j hpj (x p) * τ', ?_⟩
      rw [elMat_mul, elMat_elGen, hτ', Finset.sum_insert hps]
      have e : (1 + Matrix.single p j (x p)) *
            (1 + ∑ m ∈ s, Matrix.single m j (x m))
          = 1 + (Matrix.single p j (x p) + ∑ m ∈ s, Matrix.single m j (x m))
            + Matrix.single p j (x p) * (∑ m ∈ s, Matrix.single m j (x m)) := by
        noncomm_ring
      rw [e, hzero, add_zero]

/-- **An elementary element with prescribed column.**  For any `x` with
`x j = 1` there is `τ ∈ EL_ι(R)` whose `j`-th column is `x` and whose remaining
columns are those of the identity matrix. -/
theorem exists_colElem (j : ι) (x : ι → R) (hxj : x j = 1) :
    ∃ τ : elementaryGroup ι R,
      (∀ p : ι, elMat τ p j = x p) ∧
      (∀ p q : ι, q ≠ j → elMat τ p q = if p = q then 1 else 0) := by
  obtain ⟨τ, hτ⟩ :=
    exists_elem_colSum j x (Finset.univ.erase j) (Finset.notMem_erase j Finset.univ)
  refine ⟨τ, ?_, ?_⟩
  · intro p
    rw [hτ, Matrix.add_apply, colSum_apply, if_pos rfl]
    by_cases hp : p = j
    · rw [if_neg (fun hmem => (Finset.mem_erase.mp hmem).1 hp), add_zero, hp,
        Matrix.one_apply_eq]
      exact hxj.symm
    · rw [if_pos (Finset.mem_erase.mpr ⟨hp, Finset.mem_univ p⟩),
        Matrix.one_apply_ne hp, zero_add]
  · intro p q hq
    rw [hτ, Matrix.add_apply, colSum_apply, if_neg hq, add_zero, Matrix.one_apply]

/-! ## Layer 3b: Proposition 20 at one position -/

/-- **Preusser's Proposition 20, at the single position `(j, s)`.**

`τ` is any element of `EL_ι(R)` whose `r`-th column is the `r`-th column of the
identity — for the `τ` supplied by `exists_colElem` this holds for every column
but the `j`-th.  The hypothesis is the annihilation `y · (στ)_{ij} = 0`, and the
coefficient produced is `y · τ_{ij}`. -/
theorem elGen_mem_of_column_annihilator
    (N : Subgroup (elementaryGroup ι R)) [N.Normal]
    {g τ : elementaryGroup ι R} (hg : g ∈ N)
    {i j r s : ι} (hri : r ≠ i) (hrj : r ≠ j) (hsr : s ≠ r) (hjs : j ≠ s)
    (hTr : ∀ p : ι, elMat τ p r = if p = r then 1 else 0)
    {y : R} (hann : y * elMat (g * τ) i j = 0) (a b : R) :
    elGen j s hjs (a * (y * elMat τ i j * b)) ∈ N := by
  -- the pair of conjugates, congruent mod `N` because `τ` and `g τ` are
  have hmem : τ * (g * τ)⁻¹ ∈ N := by
    have e : τ * (g * τ)⁻¹ = g⁻¹ := by group
    rw [e]
    exact N.inv_mem hg
  have huv := conj_congr_mem N hmem (elGen r i hri y)
  -- the first defect: `E_{ri}(y) τ`, supported in row `r`
  have hTS : elMat τ * Matrix.single r i y = Matrix.single r i y := by
    ext p q
    rw [matrix_mul_single_apply, Matrix.single_apply]
    by_cases hq : q = i
    · rw [if_pos hq, hTr p]
      by_cases hp : p = r
      · rw [if_pos hp, if_pos ⟨hp.symm, hq.symm⟩, one_mul]
      · rw [if_neg hp, if_neg (fun hh => hp hh.1.symm), zero_mul]
    · rw [if_neg hq, if_neg (fun hh => hq hh.2.symm)]
  have hTinvS : elMat (τ⁻¹) * Matrix.single r i y = Matrix.single r i y := by
    calc elMat (τ⁻¹) * Matrix.single r i y
        = elMat (τ⁻¹) * (elMat τ * Matrix.single r i y) := by rw [hTS]
      _ = elMat (τ⁻¹) * elMat τ * Matrix.single r i y := by rw [← mul_assoc]
      _ = Matrix.single r i y := by rw [elMat_inv_mul, one_mul]
  have hAmat : elMat (τ⁻¹ * elGen r i hri y * τ)
      = 1 + Matrix.single r i y * elMat τ := by
    rw [elMat_mul, elMat_mul, elMat_elGen]
    have e : elMat (τ⁻¹) * (1 + Matrix.single r i y) * elMat τ
        = elMat (τ⁻¹) * elMat τ
          + elMat (τ⁻¹) * Matrix.single r i y * elMat τ := by
      noncomm_ring
    rw [e, elMat_inv_mul, hTinvS]
  have hVrow : IsRowSupported (Matrix.single r i y * elMat τ) r := by
    intro p q hp
    rw [matrix_single_mul_apply, if_neg hp]
  have hVrr : (Matrix.single r i y * elMat τ) r r = 0 := by
    rw [matrix_single_mul_apply, if_pos rfl, hTr i, if_neg (Ne.symm hri), mul_zero]
  -- the second defect: the conjugate by `g τ`, with vanishing `j`-th column
  have hBmat : elMat ((g * τ)⁻¹ * elGen r i hri y * (g * τ))
      = 1 + elMat ((g * τ)⁻¹) * Matrix.single r i y * elMat (g * τ) := by
    rw [elMat_mul, elMat_mul, elMat_elGen]
    have e : elMat ((g * τ)⁻¹) * (1 + Matrix.single r i y) * elMat (g * τ)
        = elMat ((g * τ)⁻¹) * elMat (g * τ)
          + elMat ((g * τ)⁻¹) * Matrix.single r i y * elMat (g * τ) := by
      noncomm_ring
    rw [e, elMat_inv_mul]
  have hWW : (elMat ((g * τ)⁻¹) * Matrix.single r i y * elMat (g * τ)) *
      (elMat ((g * τ)⁻¹) * Matrix.single r i y * elMat (g * τ)) = 0 :=
    sandwich_mul_self _ _ (elMat_mul_inv (g * τ)) r i hri y
  have hWcol : ∀ p : ι,
      (elMat ((g * τ)⁻¹) * Matrix.single r i y * elMat (g * τ)) p j = 0 := by
    intro p
    rw [sandwich_apply, hann, mul_zero]
  -- Layer 2 does the rest
  have hVrj : (Matrix.single r i y * elMat τ) r j = y * elMat τ i j := by
    rw [matrix_single_mul_apply, if_pos rfl]
  have h := elGen_mem_of_rowCol_pair N huv hAmat hBmat hrj hsr hjs hVrow hVrr
    hWW hWcol a b
  rwa [hVrj] at h

/-! ## Layer 3c: spreading one position to all positions -/

/-- Extend a transvection to a further column by one Steinberg commutator. -/
theorem elGen_mem_extend_right (N : Subgroup (elementaryGroup ι R)) [N.Normal]
    {k m l : ι} (hkm : k ≠ m) (hml : m ≠ l) (hkl : k ≠ l) {z : R}
    (hz : elGen k m hkm z ∈ N) : elGen k l hkl z ∈ N := by
  have hmem : ⁅elGen k m hkm z, elGen m l hml 1⁆ ∈ N := commutator_mem_left N hz _
  rwa [commutatorElement_def, elGen_commutator k m l hkm hml hkl z 1, mul_one] at hmem

/-- Extend a transvection to a further row by one Steinberg commutator, at the
cost of a left coefficient. -/
theorem elGen_mem_extend_left (N : Subgroup (elementaryGroup ι R)) [N.Normal]
    {k m l : ι} (hkm : k ≠ m) (hml : m ≠ l) (hkl : k ≠ l) (a : R) {z : R}
    (hz : elGen m l hml z ∈ N) : elGen k l hkl (a * z) ∈ N := by
  have hmem : ⁅elGen k m hkm a, elGen m l hml z⁆ ∈ N := commutator_right_mem N _ hz
  rwa [commutatorElement_def, elGen_commutator k m l hkm hml hkl a z] at hmem

/-- **From one position to all positions.**  A normal subgroup containing
`t_{pq}(a c b)` for one fixed pair `p ≠ q` and *all* `a, b` contains
`t_{kl}(a c b)` for every pair `k ≠ l`.  Only the Steinberg relation and a third
index are used. -/
theorem elGen_mem_of_base (hcard : 3 ≤ Fintype.card ι)
    (N : Subgroup (elementaryGroup ι R)) [N.Normal] {c : R} {p q : ι}
    (hpq : p ≠ q) (hbase : ∀ a b : R, elGen p q hpq (a * c * b) ∈ N)
    {k l : ι} (hkl : k ≠ l) (a b : R) :
    elGen k l hkl (a * c * b) ∈ N := by
  -- row `p`, arbitrary column
  have hrow : ∀ (m : ι) (hpm : p ≠ m) (a₁ b₁ : R),
      elGen p m hpm (a₁ * c * b₁) ∈ N := by
    intro m hpm a₁ b₁
    by_cases hmq : m = q
    · subst hmq
      exact hbase a₁ b₁
    · exact elGen_mem_extend_right N hpq (fun h => hmq h.symm) hpm (hbase a₁ b₁)
  -- every position whose two indices avoid `p`
  have hgen : ∀ (w z : ι) (hwz : w ≠ z), w ≠ p → p ≠ z → ∀ a₂ b₂ : R,
      elGen w z hwz (a₂ * c * b₂) ∈ N := by
    intro w z hwz hwp hpz a₂ b₂
    have h := elGen_mem_extend_left N hwp hpz hwz a₂ (hrow z hpz 1 b₂)
    rwa [one_mul, ← mul_assoc] at h
  by_cases hkp : k = p
  · subst hkp
    exact hrow l hkl a b
  · by_cases hlp : l = p
    · obtain ⟨m, hmk, hmp⟩ := exists_third_index hcard k p
      have hkm : k ≠ m := fun h => hmk h.symm
      have hpm : p ≠ m := fun h => hmp h.symm
      have hml : m ≠ l := fun h => hmp (h.trans hlp)
      exact elGen_mem_extend_right N hkm hml hkl (hgen k m hkm hkp hpm a b)
    · exact hgen k l hkl hkp (fun h => hlp h.symm) a b

/-! ## Preusser's Proposition 20 -/

/-- **Preusser, Proposition 20** (arXiv:1912.11386), in membership form.

Let `N` be a normal subgroup of `EL_ι(R)` with `3 ≤ card ι`, let `g ∈ N`, and
let `x : ι → R` satisfy `x j = 1` for some index `j`.  If `y` annihilates the
`i`-th coordinate of `g · x` on the left, then `t_{kl}(a y x_i b) ∈ N` for every
`k ≠ l` and all `a, b ∈ R`.

Preusser also counts the conjugates needed (eight); the count is irrelevant to
membership and is not tracked. -/
theorem elGen_mem_of_row_annihilator (hcard : 3 ≤ Fintype.card ι)
    (N : Subgroup (elementaryGroup ι R)) [N.Normal]
    {g : elementaryGroup ι R} (hg : g ∈ N)
    (i j : ι) (x : ι → R) (y : R) (hxj : x j = 1)
    (hann : y * (∑ p, elMat g i p * x p) = 0)
    {k l : ι} (hkl : k ≠ l) (a b : R) :
    elGen k l hkl (a * y * x i * b) ∈ N := by
  obtain ⟨τ, hTcol, hToff⟩ := exists_colElem j x hxj
  obtain ⟨r, hri, hrj⟩ := exists_third_index hcard i j
  obtain ⟨s, hsr, hsj⟩ := exists_third_index hcard r j
  have hjs : j ≠ s := Ne.symm hsj
  have hTr : ∀ p : ι, elMat τ p r = if p = r then 1 else 0 :=
    fun p => hToff p r hrj
  have hann' : y * elMat (g * τ) i j = 0 := by
    have he : elMat (g * τ) i j = ∑ p, elMat g i p * x p := by
      rw [elMat_mul, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun p _ => by rw [hTcol p]
    rw [he]
    exact hann
  have hbase : ∀ a' b' : R, elGen j s hjs (a' * (y * x i) * b') ∈ N := by
    intro a' b'
    have h := elGen_mem_of_column_annihilator N hg hri hrj hsr hjs hTr hann' a' b'
    rw [hTcol i] at h
    rw [mul_assoc a' (y * x i) b']
    exact h
  have hres := elGen_mem_of_base hcard N hjs hbase hkl a b
  rwa [← mul_assoc a y (x i)] at hres

/-- Proposition 20 in the `∀ h ∈ N` shape that Proposition 21 consumes: it needs
the statement for elementary conjugates of `g` as well as for `g` itself. -/
theorem forall_elGen_mem_of_row_annihilator (hcard : 3 ≤ Fintype.card ι)
    (N : Subgroup (elementaryGroup ι R)) [N.Normal] :
    ∀ h : elementaryGroup ι R, h ∈ N → ∀ (i j : ι) (x : ι → R) (y : R),
      x j = 1 → y * (∑ p, elMat h i p * x p) = 0 →
      ∀ (k l : ι) (hkl : k ≠ l) (a b : R),
        elGen k l hkl (a * y * x i * b) ∈ N :=
  fun _ hh i j x y hxj hann _ _ hkl a b =>
    elGen_mem_of_row_annihilator hcard N hh i j x y hxj hann hkl a b

end RowAnnihilatorAlt

end GroupApproximation
