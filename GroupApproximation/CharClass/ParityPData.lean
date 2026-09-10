import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Ring

/-!
# Step D mod `p`, uniform in the tower stage: the even side over an arbitrary prime

Let `N` be the mapping torus `S¹ × S^{2n+1} × Y`, `Y = ∏_j CP^{d_j}`, and let `W` be a
complex vector bundle on `N`.  Over `F_p` the Künneth decomposition of `H^*(N)` in even
degrees is `H^*(Y) ⊕ z·H^*(Y)` with `z = t x` of weight `n+1` (cohomological degree
`2n+2`) and `z² = 0`, so the mod-`p` Chern classes read

```text
γ_k(W) = ι(a_k) + z · ι(b_k),      a_k of weight k,   b_k of weight k − (n+1).
```

This file proves, over an abstract graded-commutative `F_p`-algebra and with no reference
to `Y`, to the number of projective factors, to `m = ∑_j d_j`, or to the tower stage:

> **Theorem.**  If `a_q = 0` whenever `p ∤ q` (A), if `P^i` kills `b_{i+1}` (I), and if the
> diagonal Wu relation `P^i(γ_{i+1}) = c_i·γ_{ip+1} + (decomposables)` holds for every `i`
> with `c_i` a unit (W), then `b_N = 0` for every `N ≡ 1 (mod p)`; hence `γ_r(W) = 0`
> whenever `r ≡ 1 (mod p)` and `a_r = 0`.

This is `notes/lix-stronger-lane-reports/sp-design.md` §3.2, and it is the general-`p`
replacement for `CharClass/ParityEven.lean`'s `ParityData.b_odd_eq_zero` and
`ParityData.gamma_top_eq_zero`.  Uniformity in the stage is not an extra argument: the
statement never mentions the stage, and the two arithmetic inputs it does use — `p ∣ d_j`
for every `j`, and `p ∣ n + m` — are supplied once, for every stage of the tower
`d_j = n·2^j`, by the single hypothesis `p ∣ n`.

## The mechanism

Read the Wu relation at diagonal index `i` on its `z`-component, and put `N = ip + 1`.

*Left side.*  `b_{i+1}` has weight `i + 1 − (n+1) = i − n < i`, so instability kills
`P^i(b_{i+1})`; `P(z) = z` and Cartan give `P^i(z·ι c) = z·ι(P^i c)`.  So the `z`-part of
the left side is `0`.  This is the field `pR_b_succ`.

*Right side.*  A monomial `γ_{α_1} ⋯ γ_{α_s}` contributes to the `z`-part by replacing
exactly one factor by its `b` and the others by their `a`.  By (A) such a term survives
only if `p ∣ α_{t'}` for every other index `t'`; since those indices are `≥ 1` they are then
`≥ p`, so the surviving `b`-index is `≡ N (mod p)` and at most `N − p`.  A monomial with
`s ≥ 2` factors therefore contributes only `b`'s at indices `i'p + 1` with `i' < i`.  The
one remaining term is `c_i·γ_N`, whose `z`-part is `c_i·b_N` with `c_i` a unit.  So the
relation reads `0 = c_i·b_N + Σ (earlier b's in the same residue)`, and induction on `i`
gives `b_N = 0` after cancelling the unit.

At `p = 2` this is `ParityEven.lean` verbatim: "`N ≡ 1 mod 2`" is "`N` odd" and
"`r ≡ 1 mod 2`" is "`m` even".  The `F₂` file states the `z`-part as a plain convolution
`∑_{q+k=N} a_q b_k = 0`, which it can because at `p = 2` the decomposable part of the
universal Wu polynomial is the single two-factor sum `∑_{j≤i} γ_{i−j} γ_{i+1+j}`; at odd
`p` there is no such closed form (`sp-design` §3.3, entry `WuSymmetric`), and the shape
`γ_{ip+1} + decomposables` is all the proof consumes.

## What is asked for, and what is not

* The universal polynomials `E_j` are **not** a hypothesis.  Only the *property* their
  weight-`(ip+1)` component has is: the `e_{ip+1}`-coefficient of `E_{i+1}` is a **unit**
  and every other monomial has at least two factors (`sp-design` §3.3 L4a, VERIFIED
  (model)).  `IsDecomposable` is exactly that property, as the additive subgroup generated
  by the products of at least two Chern classes of positive index and the right total
  index.
* The leading coefficient is a unit rather than `1`, because `sp-steenrod`'s normalisation
  gives `P(h) = h + κ·h^p` on a degree-two class and the diagonal coefficient is then
  `(−1)^{i(p−1)}·κ^i`.  Hard-coding `1` would make the even side hostage to a normalisation
  constant nobody intends to pin.
* **No characteristic hypothesis.**  `ParityEven.lean` needs `(2 : R) = 0` to cancel a
  repeated term; the argument here subtracts instead, so it holds over any commutative
  ring.  The prime enters only through the *arithmetic* of the indices.
* **No primality.**  Only `2 ≤ p` is used, once, to turn `c·p ≤ i·p + 1` into `c ≤ i`.
* Instability is asked for at the single index it is used at, `P^i(b_{i+1}) = 0`;
  `ParityP.pR_b_succ_of_instability` derives it from the general form once the weight of
  `z` is at least `2`, which for `z = t x` of weight `n + 1` says `n ≥ 1`.
* The Cartan formula is likewise not a field: only `P^i(z·ι c) = z·ι(P^i c)` is, and
  `ParityP.pH_z_mul_of_cartan` derives it from Cartan, `P^0 = id` and `P^{>0} z = 0`.

## Main results

* `GroupApproximation.CharClass.ParityP.IsDecomposable` — the decomposable part of the
  universal Wu polynomial, as a property.
* `ParityP.bPart_eq_zero` — the `z`-part of a decomposable monomial vanishes (L5).
* `GroupApproximation.CharClass.ParityPData` — the hypotheses, as a structure.
* `ParityPData.b_eq_zero` — `b_{ip+1} = 0` for every `i`.
* `ParityPData.b_eq_zero_of_mod` — the same as `N % p = 1`.
* `ParityPData.gamma_eq_zero` — `γ_r(W) = 0` for `r ≡ 1 mod p` with `a_r = 0`.
* `ParityPData.gamma_rank_eq_zero` — the tower form: `p ∣ n`, `p ∣ m` ⟹ `γ_{n+1+m}(W) = 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation.CharClass

/-! ## 1. Monomials in the Chern classes, and their Künneth components -/

namespace ParityP

section Monomials

variable {R : Type*} [CommRing R]

/-- `aProd a L` is the product `∏_{α ∈ L} a α` of the `H^*(Y)`-components. -/
def aProd (a : ℕ → R) : List ℕ → R
  | [] => 1
  | α :: L => a α * aProd a L

@[simp] theorem aProd_nil (a : ℕ → R) : aProd a ([] : List ℕ) = 1 := rfl

@[simp] theorem aProd_cons (a : ℕ → R) (α : ℕ) (L : List ℕ) :
    aProd a (α :: L) = a α * aProd a L := rfl

/-- `bPart a b L` is the `z`-component of the product `∏_{α ∈ L} γ_α`: because `z² = 0`,
exactly one factor contributes its `b` and all the others their `a`. -/
def bPart (a b : ℕ → R) : List ℕ → R
  | [] => 0
  | α :: L => b α * aProd a L + a α * bPart a b L

@[simp] theorem bPart_nil (a b : ℕ → R) : bPart a b ([] : List ℕ) = 0 := rfl

@[simp] theorem bPart_cons (a b : ℕ → R) (α : ℕ) (L : List ℕ) :
    bPart a b (α :: L) = b α * aProd a L + a α * bPart a b L := rfl

/-- One vanishing factor kills the product. -/
theorem aProd_eq_zero_of_mem {a : ℕ → R} {β : ℕ} (h : a β = 0) :
    ∀ {L : List ℕ}, β ∈ L → aProd a L = 0 := by
  intro L
  induction L with
  | nil => intro hβ; exact absurd hβ (by simp)
  | cons α L ih =>
    intro hβ
    rcases List.mem_cons.mp hβ with rfl | hmem
    · rw [aProd_cons, h, zero_mul]
    · rw [aProd_cons, ih hmem, mul_zero]

/-- A list of multiples of `p` has a sum that is a multiple of `p`. -/
theorem dvd_listSum {p : ℕ} : ∀ {L : List ℕ}, (∀ β ∈ L, p ∣ β) → p ∣ L.sum := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons α L ih =>
    intro h
    rw [List.sum_cons]
    obtain ⟨x, hx⟩ := h α (by simp)
    obtain ⟨z, hz⟩ := ih fun β hβ => h β (by simp [hβ])
    exact ⟨x + z, by rw [hx, hz, Nat.mul_add]⟩

/-- A nonempty list of positive entries has positive sum. -/
theorem one_le_listSum : ∀ {L : List ℕ}, L ≠ [] → (∀ β ∈ L, 1 ≤ β) → 1 ≤ L.sum := by
  intro L
  cases L with
  | nil => intro hne _; exact absurd rfl hne
  | cons α L' =>
    intro _ hpos
    have h := hpos α (by simp)
    rw [List.sum_cons]
    omega

/-- **The `z`-part of a decomposable monomial vanishes.**  This is `sp-design` §3.3's L5,
as a property rather than a formula: if every `b` at an index that is `p` less than `N`,
or lower in the same residue, vanishes, then so does the `z`-component of any product of
Chern classes of positive index with total index `N` and at least two factors.

The extra parameter `c₀` counts the factors already stripped off by the recursion, each of
which contributed an index divisible by `p`; the disjunction `1 ≤ c₀ ∨ 2 ≤ L.length` is
what says "at least two factors in total". -/
theorem bPart_eq_zero {p N : ℕ} {a b : ℕ → R}
    (ha : ∀ q : ℕ, ¬ p ∣ q → a q = 0)
    (hb : ∀ α c : ℕ, 1 ≤ c → α + c * p = N → b α = 0) :
    ∀ L : List ℕ, (∀ β ∈ L, 1 ≤ β) → ∀ c₀ : ℕ, L.sum + c₀ * p = N →
      (1 ≤ c₀ ∨ 2 ≤ L.length) → bPart a b L = 0 := by
  intro L
  induction L with
  | nil => intro _ _ _ _; exact bPart_nil a b
  | cons α L ih =>
    intro hpos c₀ hsum hcase
    have hα1 : 1 ≤ α := hpos α (by simp)
    have hposL : ∀ β ∈ L, 1 ≤ β := fun β hβ => hpos β (by simp [hβ])
    rw [bPart_cons]
    have hterm1 : b α * aProd a L = 0 := by
      by_cases hall : ∀ β ∈ L, p ∣ β
      · obtain ⟨u, hu⟩ := dvd_listSum hall
        have hu' : L.sum = u * p := by rw [hu]; ring
        have hsum' : α + u * p + c₀ * p = N := by
          rw [List.sum_cons, hu'] at hsum; exact hsum
        have hone : 1 ≤ u + c₀ := by
          rcases hcase with hc | hlen
          · omega
          · have hne : L ≠ [] := by
              rintro rfl
              exact absurd hlen (by simp)
            have hs1 : 1 ≤ L.sum := one_le_listSum hne hposL
            have hu1 : u ≠ 0 := by
              rintro rfl
              rw [Nat.zero_mul] at hu'
              omega
            omega
        have hkey : α + (u + c₀) * p = N := by rw [add_mul]; omega
        rw [hb α (u + c₀) hone hkey, zero_mul]
      · obtain ⟨β, hβ, hβd⟩ : ∃ β ∈ L, ¬ p ∣ β := by
          by_contra hc
          exact hall fun β hβ => by
            by_contra hd
            exact hc ⟨β, hβ, hd⟩
        rw [aProd_eq_zero_of_mem (ha β hβd) hβ, mul_zero]
    have hterm2 : a α * bPart a b L = 0 := by
      by_cases hd : p ∣ α
      · obtain ⟨c, hc⟩ := hd
        have hc' : α = c * p := by rw [hc]; ring
        have hc1 : 1 ≤ c := by
          rcases Nat.eq_zero_or_pos c with rfl | hcp
          · rw [Nat.zero_mul] at hc'; omega
          · exact hcp
        have hsum' : L.sum + c * p + c₀ * p = N := by
          rw [List.sum_cons, hc'] at hsum; omega
        have hnew : L.sum + (c₀ + c) * p = N := by rw [add_mul]; omega
        rw [ih hposL (c₀ + c) hnew (Or.inl (by omega)), mul_zero]
      · rw [ha α hd, zero_mul]
    rw [hterm1, hterm2, add_zero]

end Monomials

/-! ## 2. Decomposable classes -/

section Decomposable

variable {H : Type*} [CommRing H]

/-- `gammaProd γ L` is the product `∏_{α ∈ L} γ α` of Chern classes. -/
def gammaProd (γ : ℕ → H) : List ℕ → H
  | [] => 1
  | α :: L => γ α * gammaProd γ L

@[simp] theorem gammaProd_nil (γ : ℕ → H) : gammaProd γ ([] : List ℕ) = 1 := rfl

@[simp] theorem gammaProd_cons (γ : ℕ → H) (α : ℕ) (L : List ℕ) :
    gammaProd γ (α :: L) = γ α * gammaProd γ L := rfl

/-- **The decomposables in total index `N`**: the additive subgroup of `H` generated by
the products of **at least two** Chern classes, all of positive index, whose indices sum
to `N`.

This is the only thing the even side needs to know about the universal Wu polynomial
`E_{i+1}`: that it is `e_{ip+1}` plus an integral combination of such products
(`sp-design` §3.3, L4a).  No closed form for `E_{i+1}` is used, and none exists at odd `p`
in the two-factor shape the `F₂` tree enjoys. -/
inductive IsDecomposable (γ : ℕ → H) (N : ℕ) : H → Prop
  /-- A monomial: at least two Chern classes, positive indices summing to `N`. -/
  | monomial (L : List ℕ) (hpos : ∀ β ∈ L, 1 ≤ β) (hsum : L.sum = N) (hlen : 2 ≤ L.length) :
      IsDecomposable γ N (gammaProd γ L)
  /-- The empty combination. -/
  | zero : IsDecomposable γ N 0
  /-- Closure under addition. -/
  | add (u v : H) (hu : IsDecomposable γ N u) (hv : IsDecomposable γ N v) :
      IsDecomposable γ N (u + v)
  /-- Closure under negation. -/
  | neg (u : H) (hu : IsDecomposable γ N u) : IsDecomposable γ N (-u)

/-- Closure under finite sums.  An instantiator produces the decomposable part of the Wu
relation as a `Finset` sum, so this is the shape it needs. -/
theorem IsDecomposable.sum {γ : ℕ → H} {N : ℕ} {ι' : Type*} (f : ι' → H) :
    ∀ s : Finset ι', (∀ i ∈ s, IsDecomposable γ N (f i)) →
      IsDecomposable γ N (∑ i ∈ s, f i) := by
  intro s
  induction s using Finset.cons_induction with
  | empty => intro _; rw [Finset.sum_empty]; exact IsDecomposable.zero
  | cons a v _ha ihv =>
    intro hall
    rw [Finset.sum_cons]
    exact IsDecomposable.add _ _ (hall a (by simp)) (ihv fun i hi => hall i (by simp [hi]))

/-- A two-factor monomial is decomposable.  At `p = 2` every term of the diagonal Wu
relation other than `γ_{2i+1}` has this shape, which is why `ParityEven.lean`'s `wu` field
instantiates the field `wu` here. -/
theorem IsDecomposable.pair {γ : ℕ → H} {N α β : ℕ} (hα : 1 ≤ α) (hβ : 1 ≤ β)
    (hsum : α + β = N) : IsDecomposable γ N (γ α * γ β) := by
  have hprod : gammaProd γ [α, β] = γ α * γ β := by
    simp only [gammaProd_cons, gammaProd_nil, mul_one]
  rw [← hprod]
  refine IsDecomposable.monomial [α, β] ?_ ?_ ?_
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc2
    · exact hα
    · rcases List.mem_cons.mp hc2 with rfl | hc3
      · exact hβ
      · exact absurd hc3 (by simp)
  · simpa using hsum
  · simp

end Decomposable

end ParityP

open ParityP

/-! ## 3. The hypotheses of the even side mod `p` -/

/-- The Künneth and reduced-power data of the mapping torus `N = S¹ × S^{2n+1} × Y` that
the even side of Lemma 2 consumes at the prime `p`.

`R` is `H^*(Y; F_p)` and `H` is the even part of `H^*(N; F_p)`; `a k` and `b k` are the two
Künneth components of the `k`-th mod-`p` Chern class of the bundle.  Nothing here mentions
the rank of the bundle, the base `Y`, or the tower stage: the statement is rank-free and
stage-free, which is what makes Step D uniform.

Only the even part of `H^*(N)` appears, so `H` is a commutative ring even at odd `p`; the
odd classes `t` and `x` never occur separately, only through `z = t x`. -/
structure ParityPData (p : ℕ) (R H : Type*) [CommRing R] [CommRing H] where
  /-- The prime is at least `2`.  Primality itself is never used. -/
  p_two_le : 2 ≤ p
  /-- The Künneth inclusion `H^*(Y) → H^*(N)`. -/
  ι : R →+* H
  /-- The class `z = t x`, of weight `n + 1`. -/
  z : H
  /-- `z² = 0`, `z` being the product of two odd-dimensional exterior generators. -/
  z_mul_z : z * z = 0
  /-- Künneth: the `z`-component of the decomposition is well defined. -/
  z_inj : ∀ u v : R, ι u + z * ι v = 0 → v = 0
  /-- The reduced powers on the even part of `H^*(N)`, additive in the class. -/
  PH : ℕ → H →+ H
  /-- The reduced powers on `H^*(Y)`. -/
  PR : ℕ → R →+ R
  /-- The reduced powers preserve the Künneth decomposition. -/
  pH_ι : ∀ (i : ℕ) (r : R), PH i (ι r) = ι (PR i r)
  /-- `P(z) = z`, in the only form used: `P^i` passes through the `z`-component.
  `ParityP.pH_z_mul_of_cartan` derives this from the Cartan formula, `P^0 = id` and
  `P^i z = 0` for `i > 0`. -/
  pH_z_mul : ∀ (i : ℕ) (r : R), PH i (z * ι r) = z * ι (PR i r)
  /-- The mod-`p` Chern classes of `W`. -/
  γ : ℕ → H
  /-- The `H^*(Y)`-component of `γ k`, of weight `k`. -/
  a : ℕ → R
  /-- The `z H^*(Y)`-component of `γ k`, of weight `k − (n+1)`; indexed by the **total**
  index. -/
  b : ℕ → R
  /-- The Künneth decomposition of the Chern classes. -/
  γ_eq : ∀ k : ℕ, γ k = ι (a k) + z * ι (b k)
  /-- **(A)** Frobenius support of the slice class: `γ(V) = ∏_i (1 + h_i^p)^{d_i/p}` when
  `p ∣ d_i` for every `i`, so its components in indices not divisible by `p` vanish.
  `ParityPSlice.lean` produces this. -/
  a_eq_zero : ∀ q : ℕ, ¬ p ∣ q → a q = 0
  /-- **(I)** Instability, at the single index the argument uses it: `b (i+1)` has weight
  `i − n < i`, so `P^i` kills it.  `ParityP.pR_b_succ_of_instability` produces this. -/
  pR_b_succ : ∀ i : ℕ, PR i (b (i + 1)) = 0
  /-- The leading coefficient of the diagonal Wu relation.  It is **not** `1`: under the
  normalisation that makes `P^0 = id`, the relation on a degree-two class reads
  `P(h) = h + κ·h^p` with `κ` a unit that is not `1` in general, and tracking `κ` through
  the universal polynomial makes the coefficient `(−1)^{i(p−1)}·κ^i` (`sp-design`, L4a with
  the `κ`-correction of 2026-09-10).  Carrying it as an abstract unit makes the even side
  independent of `sp-steenrod`'s normalisation constant. -/
  c : ℕ → R
  /-- The leading coefficient is a unit.  This is all the induction needs: it cancels
  `c i` from `c i · b_{ip+1} = 0`. -/
  c_isUnit : ∀ i : ℕ, IsUnit (c i)
  /-- **(W)** The diagonal Wu relation: `P^i(γ_{i+1}) = c_i·γ_{ip+1} + (decomposables)`.
  The weight-`(ip+1)` component of the universal polynomial `E_{i+1}` has `e_{ip+1}` with
  the unit coefficient `c i`, and every other monomial has at least two factors
  (`sp-design` §3.3 L4a). -/
  wu : ∀ i : ℕ, IsDecomposable γ (i * p + 1)
    (PH i (γ (i + 1)) - ι (c i) * γ (i * p + 1))

/-! ## 4. Discharging two of the fields from their usual form -/

namespace ParityP

section Derivations

variable {R : Type*} [CommRing R]

/-- Instability in the form an instantiator has it: `P^i` kills a class of weight `< i`,
where `b k` has weight `k − w` and `w` is the weight of `z`. -/
def Instability (PR : ℕ → R →+ R) (b : ℕ → R) (w : ℕ) : Prop :=
  ∀ k i : ℕ, k < i + w → PR i (b k) = 0

/-- The field `pR_b_succ`, from instability.  For `z = t x` of weight `n + 1` the
hypothesis `2 ≤ w` says `n ≥ 1`, which every stage of the tower satisfies. -/
theorem pR_b_succ_of_instability {PR : ℕ → R →+ R} {b : ℕ → R} {w : ℕ} (hw : 2 ≤ w)
    (h : Instability PR b w) (i : ℕ) : PR i (b (i + 1)) = 0 :=
  h (i + 1) i (by omega)

variable {H : Type*} [CommRing H]

/-- The field `pH_z_mul`, from the Cartan formula together with `P^0 = id` and
`P^i z = 0` for `i > 0` (which is `P(z) = z`). -/
theorem pH_z_mul_of_cartan {ι : R →+* H} {z : H} {PH : ℕ → H →+ H} {PR : ℕ → R →+ R}
    (hzero : ∀ u : H, PH 0 u = u)
    (cartan : ∀ (i : ℕ) (u v : H),
      PH i (u * v) = ∑ j ∈ Finset.range (i + 1), PH j u * PH (i - j) v)
    (hz : ∀ i : ℕ, 0 < i → PH i z = 0)
    (hι : ∀ (i : ℕ) (r : R), PH i (ι r) = ι (PR i r)) (i : ℕ) (r : R) :
    PH i (z * ι r) = z * ι (PR i r) := by
  rw [cartan i z (ι r),
    Finset.sum_eq_single 0
      (fun j _ hj => by rw [hz j (Nat.pos_of_ne_zero hj), zero_mul])
      (fun h => absurd (Finset.mem_range.mpr (Nat.succ_pos i)) h),
    hzero, Nat.sub_zero, hι]

end Derivations

end ParityP

/-! ## 5. The uniform theorem -/

namespace ParityPData

variable {p : ℕ} {R H : Type*} [CommRing R] [CommRing H] (D : ParityPData p R H)

/-- The Künneth decomposition of a product of Chern classes: because `z² = 0`, the
`z`-component is `bPart`. -/
theorem gammaProd_eq (L : List ℕ) :
    gammaProd D.γ L = D.ι (aProd D.a L) + D.z * D.ι (bPart D.a D.b L) := by
  induction L with
  | nil =>
    simp only [gammaProd_nil, aProd_nil, bPart_nil, map_one, map_zero, mul_zero, add_zero]
  | cons α L ih =>
    have e : gammaProd D.γ (α :: L)
        = D.ι (D.a α) * D.ι (aProd D.a L)
          + D.z * (D.ι (D.b α) * D.ι (aProd D.a L) + D.ι (D.a α) * D.ι (bPart D.a D.b L))
          + D.z * D.z * (D.ι (D.b α) * D.ι (bPart D.a D.b L)) := by
      rw [gammaProd_cons, ih, D.γ_eq α]; ring
    rw [e, D.z_mul_z, zero_mul, add_zero]
    simp only [aProd_cons, bPart_cons, map_mul, map_add]

/-- **The decomposables have no `z`-part**, once every earlier `b` in the residue class
vanishes.  This is where `bPart_eq_zero` is consumed. -/
theorem exists_iota_of_isDecomposable {N : ℕ}
    (hb : ∀ α c : ℕ, 1 ≤ c → α + c * p = N → D.b α = 0) :
    ∀ {u : H}, IsDecomposable D.γ N u → ∃ w : R, u = D.ι w := by
  intro u hu
  induction hu with
  | monomial L hpos hsum hlen =>
    refine ⟨aProd D.a L, ?_⟩
    rw [D.gammaProd_eq L,
      bPart_eq_zero D.a_eq_zero hb L hpos 0 (by simpa using hsum) (Or.inr hlen),
      map_zero, mul_zero, add_zero]
  | zero => exact ⟨0, (map_zero D.ι).symm⟩
  | add u v _hu _hv ihu ihv =>
    obtain ⟨w₁, h₁⟩ := ihu
    obtain ⟨w₂, h₂⟩ := ihv
    exact ⟨w₁ + w₂, by rw [h₁, h₂, map_add]⟩
  | neg u _hu ihu =>
    obtain ⟨w, h⟩ := ihu
    exact ⟨-w, by rw [h, map_neg]⟩

/-- **The inductive step.**  The diagonal Wu relation at index `i`, read on its
`z`-component, kills `b_{ip+1}` once every earlier `b_{i'p+1}` vanishes. -/
theorem b_step (i : ℕ) (ih : ∀ i' : ℕ, i' < i → D.b (i' * p + 1) = 0) :
    D.b (i * p + 1) = 0 := by
  -- The `b`-indices that the decomposable part can reach are earlier ones in the
  -- residue class of `1` mod `p`.
  have hb : ∀ α c : ℕ, 1 ≤ c → α + c * p = i * p + 1 → D.b α = 0 := by
    intro α c hc hα
    have hci : c ≤ i := by
      by_contra hcon
      have hcon' : i + 1 ≤ c := by omega
      have h1 : (i + 1) * p ≤ c * p := Nat.mul_le_mul hcon' (le_refl p)
      rw [add_mul, one_mul] at h1
      have h2 := D.p_two_le
      omega
    obtain ⟨i', hi'⟩ : ∃ i', i = i' + c := ⟨i - c, by omega⟩
    have hα' : α = i' * p + 1 := by
      rw [hi', add_mul] at hα
      omega
    rw [hα']
    exact ih i' (by omega)
  -- The left side of the Wu relation has no `z`-part, by instability.
  have hL : D.PH i (D.γ (i + 1)) = D.ι (D.PR i (D.a (i + 1))) := by
    rw [D.γ_eq (i + 1), map_add, D.pH_ι, D.pH_z_mul, D.pR_b_succ i, map_zero, mul_zero,
      add_zero]
  obtain ⟨w, hw⟩ := D.exists_iota_of_isDecomposable hb (D.wu i)
  have hw' : D.ι w = D.ι (D.PR i (D.a (i + 1)))
      - D.ι (D.c i) * (D.ι (D.a (i * p + 1)) + D.z * D.ι (D.b (i * p + 1))) := by
    rw [← hw, hL, D.γ_eq (i * p + 1)]
  have key : D.ι (D.PR i (D.a (i + 1)) - D.c i * D.a (i * p + 1) - w)
      + D.z * D.ι (-(D.c i * D.b (i * p + 1))) = 0 := by
    simp only [map_sub, map_mul, map_neg]
    rw [hw']
    ring
  have hcb : D.c i * D.b (i * p + 1) = 0 := neg_eq_zero.mp (D.z_inj _ _ key)
  exact (D.c_isUnit i).mul_right_eq_zero.mp hcb

/-- **Step D mod `p`, uniform in the stage.**  Every Künneth component `b` in a total
index congruent to `1` mod `p` vanishes.  At `p = 2` this is `ParityData.b_odd_eq_zero`. -/
theorem b_eq_zero : ∀ i : ℕ, D.b (i * p + 1) = 0 := by
  suffices H' : ∀ M i : ℕ, i ≤ M → D.b (i * p + 1) = 0 by
    intro i
    exact H' i i le_rfl
  intro M
  induction M with
  | zero => exact fun i hi => D.b_step i fun i' hi' => absurd hi' (by omega)
  | succ M ihM => exact fun i hi => D.b_step i fun i' hi' => ihM i' (by omega)

/-- **Step D mod `p`**, in residue form: `b_N = 0` for every `N ≡ 1 (mod p)`. -/
theorem b_eq_zero_of_mod {N : ℕ} (hN : N % p = 1) : D.b N = 0 := by
  have h1 := D.b_eq_zero (N / p)
  have h3 := Nat.div_add_mod' N p
  rw [hN] at h3
  rwa [h3] at h1

/-! ### The conclusion -/

/-- **The even side mod `p`.**  A Chern class in a total index `≡ 1 (mod p)` whose
`H^*(Y)`-component vanishes is zero. -/
theorem gamma_eq_zero {r : ℕ} (hr : r % p = 1) (ha : D.a r = 0) : D.γ r = 0 := by
  rw [D.γ_eq r, ha, D.b_eq_zero_of_mod hr, map_zero, mul_zero, add_zero]

/-- **Step D mod `p`, in the tower's indexing.**  The rank at a stage is `r = n + 1 + m`
with `m = ∑_j d_j`, and `z` has weight `n + 1`; `p ∣ n` and `p ∣ m` make `r ≡ 1 (mod p)`.
For the tower `d_j = n · 2^j` both divisibilities follow from `p ∣ n` alone, at every
stage — this is the uniformity the limit needs. -/
theorem gamma_rank_eq_zero {n m : ℕ} (hn : p ∣ n) (hm : p ∣ m)
    (ha : D.a (n + 1 + m) = 0) : D.γ (n + 1 + m) = 0 := by
  refine D.gamma_eq_zero ?_ ha
  obtain ⟨s, rfl⟩ := hn
  obtain ⟨t, rfl⟩ := hm
  have hrw : p * s + 1 + p * t = p * (s + t) + 1 := by ring
  rw [hrw, Nat.mul_add_mod, Nat.mod_eq_of_lt (by have := D.p_two_le; omega)]

end ParityPData

end GroupApproximation.CharClass
