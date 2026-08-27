import GroupApproximation.Analysis.KazhdanProjectionAbsorption

/-!
# CO.19: the projection-difference collapse

Step 2 of the printed proof of `thm:projection-collapse` runs inside the corona,
on the conjugates `p_g = π(g) p π(g)*` of a single projection:

> `d_g = p_g − p` is self-adjoint with `d_g³ = d_g`, so `q_g = d_g²` is a
> projection and all of them commute; `q = 1 − ∏_{a∈S}(1 − q_a)` is nonzero
> because the `g` with `p_g = p` form a subgroup.

All of that is `*`-ring algebra plus one group-theoretic step, and none of it
needs a norm, a filter, or a corona.  This file proves it for an arbitrary ring
with involution.

## The commutation hypothesis is not decoration

`d³ = d` is **false** for two general projections.  With `p = diag(1,0)` and
`q = ½·(all ones)` in `M₂(ℂ)`, `d = q − p` has `d² = ½·1`, so `d³ = ½·d`, and
`d²` is not a projection either.  What the identity needs is that `p` and `q`
commute, and in the printed setting they do: the `p_g` are conjugates by a
commuting family of lamp involutions.  Every statement below therefore carries
the commutation hypothesis explicitly.

## Why a list and not a `Finset`

`∏_{a∈S}` over elements of a noncommutative ring is not `Finset.prod`, which
needs a commutative monoid.  The product is taken over a `List` with a pairwise
commutation hypothesis, which is what the printed product is: a finite product
of commuting projections in some order, the order being irrelevant precisely
because they commute.

`IsSelfAdjoint (q - p)` is `IsSelfAdjoint.sub` in mathlib and is not restated.
-/

namespace GroupApproximation
namespace ProjectionOrbitCollapse

variable {A : Type*} [Ring A]

/-! ## The difference of two commuting projections -/

/-- **CO.19, the cube identity.**  For *commuting* idempotents, `d = q − p`
satisfies `d³ = d`.  Without commutation this is false. -/
theorem cube_sub_eq_self {p q : A} (hp : IsIdempotentElem p)
    (hq : IsIdempotentElem q) (h : Commute p q) : (q - p) ^ 3 = q - p := by
  have hp2 : p * p = p := hp
  have hq2 : q * q = q := hq
  have hpq : p * q = q * p := h
  calc (q - p) ^ 3
      = q * q * q - q * q * p - q * p * q + q * p * p
          - p * q * q + p * q * p + p * p * q - p * p * p := by
        noncomm_ring
    _ = q - q * p - q * p + q * p - q * p + q * p + q * p - p := by
        rw [show q * q * q = q from by rw [hq2, hq2],
          show q * q * p = q * p from by rw [hq2],
          show q * p * q = q * p from by rw [← hpq, mul_assoc, hq2, hpq],
          show q * p * p = q * p from by rw [mul_assoc, hp2],
          show p * q * q = q * p from by rw [mul_assoc, hq2, hpq],
          show p * q * p = q * p from by rw [hpq, mul_assoc, hp2],
          show p * p * q = q * p from by rw [hp2, hpq],
          show p * p * p = p from by rw [hp2, hp2]]
    _ = q - p := by abel

/-- **CO.19, `q_g = d_g²` is a projection.**  Immediate from the cube identity:
`(d²)² = d³·d = d·d = d²`. -/
theorem isIdempotentElem_sq_sub {p q : A} (hp : IsIdempotentElem p)
    (hq : IsIdempotentElem q) (h : Commute p q) :
    IsIdempotentElem ((q - p) ^ 2) := by
  have hcube := cube_sub_eq_self hp hq h
  show ((q - p) ^ 2) * ((q - p) ^ 2) = (q - p) ^ 2
  calc ((q - p) ^ 2) * ((q - p) ^ 2)
      = (q - p) ^ 3 * (q - p) := by noncomm_ring
    _ = (q - p) * (q - p) := by rw [hcube]
    _ = (q - p) ^ 2 := by noncomm_ring

/-- The difference vanishes as soon as its square does, again by the cube
identity.  This is what makes `q_g = 0` say `p_g = p`, rather than merely
something about `d_g²`. -/
theorem eq_of_sq_sub_eq_zero {p q : A} (hp : IsIdempotentElem p)
    (hq : IsIdempotentElem q) (h : Commute p q) (hsq : (q - p) ^ 2 = 0) :
    q = p := by
  have hcube := cube_sub_eq_self hp hq h
  have hzero : q - p = 0 := by
    calc q - p = (q - p) ^ 3 := hcube.symm
      _ = (q - p) * (q - p) ^ 2 := by noncomm_ring
      _ = 0 := by rw [hsq, mul_zero]
  exact sub_eq_zero.mp hzero

/-- **CO.19, "all the `p_g` commute, hence so do all the `d_g`".** -/
theorem commute_sub {p a b : A} (hpa : Commute p a) (hpb : Commute p b)
    (hab : Commute a b) : Commute (a - p) (b - p) :=
  (hab.sub_right hpa.symm).sub_left (hpb.sub_right (Commute.refl p))

/-- **CO.19, "all of them commute".**  Hence so do the squares `q_g = d_g²`. -/
theorem commute_sq_sub {p a b : A} (hpa : Commute p a) (hpb : Commute p b)
    (hab : Commute a b) : Commute ((a - p) ^ 2) ((b - p) ^ 2) :=
  (commute_sub hpa hpb hab).pow_pow 2 2

/-! ## The product over a generating list -/

/-- A product of pairwise commuting idempotents is an idempotent. -/
theorem isIdempotentElem_listProd {l : List A}
    (hl : ∀ x ∈ l, IsIdempotentElem x) (hc : l.Pairwise Commute) :
    IsIdempotentElem l.prod := by
  induction l with
  | nil =>
    show IsIdempotentElem (List.prod ([] : List A))
    rw [List.prod_nil]
    exact IsIdempotentElem.one
  | cons a t ih =>
    have hpair : ∀ x ∈ t, Commute a x := (List.pairwise_cons.mp hc).1
    have hcomm : Commute a t.prod := Commute.list_prod_right t a hpair
    have ha : a * a = a := hl a (by simp)
    have ht : t.prod * t.prod = t.prod :=
      ih (fun x hx ↦ hl x (by simp [hx]))
        (List.pairwise_cons.mp hc).2
    show (List.prod (a :: t)) * (List.prod (a :: t)) = List.prod (a :: t)
    rw [List.prod_cons]
    calc (a * t.prod) * (a * t.prod)
        = a * (t.prod * a) * t.prod := by noncomm_ring
      _ = a * (a * t.prod) * t.prod := by rw [hcomm.symm.eq]
      _ = (a * a) * (t.prod * t.prod) := by noncomm_ring
      _ = a * t.prod := by rw [ha, ht]

/-- **The printed `q_a` annihilation.**  Each factor's index annihilates the
whole product: `q_a · ∏_b (1 − q_b) = 0`.  The argument is the printed one:
`q_a(1 − q_a) = 0`, and `q_a` commutes past the other factors. -/
theorem mul_listProd_one_sub_eq_zero {l : List A}
    (hl : ∀ y ∈ l, IsIdempotentElem y) (hc : l.Pairwise Commute)
    {x : A} (hx : x ∈ l) : x * (l.map fun y ↦ 1 - y).prod = 0 := by
  obtain ⟨s, t, hst⟩ := List.append_of_mem hx
  have hc' : (s ++ x :: t).Pairwise Commute := by rw [← hst]; exact hc
  have hcross := (List.pairwise_append.mp hc').2.2
  have hxs : ∀ y ∈ s, Commute x y := fun y hy ↦
    (hcross y hy x (by simp)).symm
  have hcs : Commute x (s.map fun y ↦ 1 - y).prod := by
    refine Commute.list_prod_right _ _ ?_
    intro z hz
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
    exact (Commute.one_right x).sub_right (hxs y hy)
  have hxx : x * (1 - x) = 0 := by
    have hxi : x * x = x := hl x hx
    rw [mul_sub, mul_one, hxi, sub_self]
  have hsplit : (l.map fun y ↦ 1 - y).prod
      = (s.map fun y ↦ 1 - y).prod
        * ((1 - x) * (t.map fun y ↦ 1 - y).prod) := by
    rw [hst, List.map_append, List.prod_append, List.map_cons, List.prod_cons]
  have hkey : x * (l.map fun y ↦ 1 - y).prod = 0 := by
    rw [hsplit]
    calc x * ((s.map fun y ↦ 1 - y).prod
            * ((1 - x) * (t.map fun y ↦ 1 - y).prod))
        = (x * (s.map fun y ↦ 1 - y).prod)
            * ((1 - x) * (t.map fun y ↦ 1 - y).prod) := by
          rw [mul_assoc]
      _ = ((s.map fun y ↦ 1 - y).prod * x)
            * ((1 - x) * (t.map fun y ↦ 1 - y).prod) := by
          rw [hcs.eq]
      _ = (s.map fun y ↦ 1 - y).prod * (x * (1 - x))
            * (t.map fun y ↦ 1 - y).prod := by
          noncomm_ring
      _ = 0 := by rw [hxx, mul_zero, zero_mul]
  exact hkey

/-- **CO.19, the vanishing criterion.**  If `1 − ∏(1 − q_a) = 0` then every
`q_a` vanishes. -/
theorem eq_zero_of_one_sub_listProd_eq_zero {l : List A}
    (hl : ∀ y ∈ l, IsIdempotentElem y) (hc : l.Pairwise Commute)
    {x : A} (hx : x ∈ l)
    (h : (1 : A) - (l.map fun y ↦ 1 - y).prod = 0) : x = 0 := by
  have hprod : (l.map fun y ↦ 1 - y).prod = 1 := (sub_eq_zero.mp h).symm
  have hkey := mul_listProd_one_sub_eq_zero hl hc hx
  rw [hprod, mul_one] at hkey
  exact hkey

/-- **The printed `q_a q = q_a`.**  Immediate from the annihilation. -/
theorem mul_one_sub_listProd {l : List A}
    (hl : ∀ y ∈ l, IsIdempotentElem y) (hc : l.Pairwise Commute)
    {x : A} (hx : x ∈ l) :
    x * ((1 : A) - (l.map fun y ↦ 1 - y).prod) = x := by
  rw [mul_sub, mul_one, mul_listProd_one_sub_eq_zero hl hc hx, sub_zero]

/-- **The printed `d_a = d_a q_a`.**  The cube identity, read as `d · d² = d`;
with `q_a q = q_a` this is the printed `d_a = d_a q_a = d_a q`. -/
theorem sub_mul_sq_sub {p q : A} (hp : IsIdempotentElem p)
    (hq : IsIdempotentElem q) (h : Commute p q) :
    (q - p) * (q - p) ^ 2 = q - p := by
  calc (q - p) * (q - p) ^ 2 = (q - p) ^ 3 := by noncomm_ring
    _ = q - p := cube_sub_eq_self hp hq h

/-- **CO.19, assembled.**  `q = 1 − ∏_{i}(1 − (P i − p)²)` is nonzero as soon as
one `P i` differs from `p`. -/
theorem one_sub_listProd_sq_ne_zero {ι : Type*} {l : List ι} {P : ι → A} {p : A}
    (hp : IsIdempotentElem p) (hP : ∀ i ∈ l, IsIdempotentElem (P i))
    (hc : ∀ i ∈ l, Commute p (P i))
    (hq : (l.map fun i ↦ (P i - p) ^ 2).Pairwise Commute)
    {i₀ : ι} (hi₀ : i₀ ∈ l) (hne : P i₀ ≠ p) :
    (1 : A) - ((l.map fun i ↦ (P i - p) ^ 2).map fun y ↦ 1 - y).prod ≠ 0 := by
  intro hzero
  have hidem : ∀ y ∈ (l.map fun i ↦ (P i - p) ^ 2), IsIdempotentElem y := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
    exact isIdempotentElem_sq_sub hp (hP i hi) (hc i hi)
  have hmem : (P i₀ - p) ^ 2 ∈ (l.map fun i ↦ (P i - p) ^ 2) :=
    List.mem_map_of_mem hi₀
  have hsq : (P i₀ - p) ^ 2 = 0 :=
    eq_zero_of_one_sub_listProd_eq_zero hidem hq hmem hzero
  exact hne (eq_of_sq_sub_eq_zero hp (hP i₀ hi₀) (hc i₀ hi₀) hsq)

/-! ## The group-theoretic half -/

section Conjugation

variable [StarRing A] {G : Type*} [Group G]

/-- `p_g = π(g) p π(g)*`. -/
def conj (ρ : G →* unitary A) (p : A) (g : G) : A :=
  (ρ g : A) * p * star (ρ g : A)

@[simp] theorem conj_one (ρ : G →* unitary A) (p : A) : conj ρ p 1 = p := by
  simp [conj]

theorem conj_mul (ρ : G →* unitary A) (p : A) (g h : G) :
    conj ρ p (g * h) = (ρ g : A) * conj ρ p h * star (ρ g : A) := by
  have hco : ((ρ (g * h) : unitary A) : A) = (ρ g : A) * (ρ h : A) := by
    rw [map_mul]
    rfl
  show (ρ (g * h) : A) * p * star ((ρ (g * h) : unitary A) : A) = _
  rw [hco, star_mul]
  unfold conj
  noncomm_ring

/-- **CO.19, "the `g` with `p_g = p` form a subgroup".** -/
def fixer (ρ : G →* unitary A) (p : A) : Subgroup G where
  carrier := {g | conj ρ p g = p}
  one_mem' := conj_one ρ p
  mul_mem' := fun {g h} hg hh ↦ by
    show conj ρ p (g * h) = p
    rw [conj_mul, show conj ρ p h = p from hh]
    exact hg
  inv_mem' := fun {g} hg ↦ by
    have hg' : (ρ g : A) * p * star (ρ g : A) = p := hg
    have hu1 : star (ρ g : A) * (ρ g : A) = 1 := (ρ g).2.1
    have hback : star (ρ g : A) * p * (ρ g : A) = p := by
      calc star (ρ g : A) * p * (ρ g : A)
          = star (ρ g : A) * ((ρ g : A) * p * star (ρ g : A)) * (ρ g : A) := by
            rw [hg']
        _ = (star (ρ g : A) * (ρ g : A)) * p
              * (star (ρ g : A) * (ρ g : A)) := by noncomm_ring
        _ = p := by rw [hu1, one_mul, mul_one]
    show conj ρ p g⁻¹ = p
    have hinv : ((ρ g⁻¹ : unitary A) : A) = star (ρ g : A) := by
      rw [map_inv]
      rfl
    show (ρ g⁻¹ : A) * p * star (ρ g⁻¹ : A) = p
    rw [hinv, star_star]
    exact hback

theorem mem_fixer_iff (ρ : G →* unitary A) (p : A) (g : G) :
    g ∈ fixer ρ p ↔ conj ρ p g = p := Iff.rfl

/-- **`eq:collapse-cocycle`.**  `d_{gh} = d_g + Θ(g) d_h Θ(g)*`.

This is pure algebra and needs nothing about the ambient: `p_{gh} = Θ(g) p_h
Θ(g)*` by multiplicativity, and then the two copies of `Θ(g) p Θ(g)*` cancel.
It is the identity that makes `β(g) = Λ(d_g)` a `1`-cocycle for the conjugation
representation, once `Λ` is available. -/
theorem sub_conj_mul (ρ : G →* unitary A) (p : A) (g h : G) :
    conj ρ p (g * h) - p
      = (conj ρ p g - p) + (ρ g : A) * (conj ρ p h - p) * star (ρ g : A) := by
  rw [conj_mul]
  simp only [conj, mul_sub, sub_mul]
  abel

/-- **CO.19, the generating step.**  If no generator moves `p`, nothing does; so
if something does, a generator already does. -/
theorem exists_mem_conj_ne (ρ : G →* unitary A) (p : A) {S : Set G}
    (hgen : Subgroup.closure S = ⊤) {g : G} (hg : conj ρ p g ≠ p) :
    ∃ a ∈ S, conj ρ p a ≠ p := by
  by_contra hcon
  have hsub : S ⊆ (fixer ρ p : Set G) := by
    intro a ha
    show conj ρ p a = p
    by_contra hne
    exact hcon ⟨a, ha, hne⟩
  have hle : Subgroup.closure S ≤ fixer ρ p := (Subgroup.closure_le _).2 hsub
  rw [hgen] at hle
  exact hg (hle (Subgroup.mem_top g))

end Conjugation

end ProjectionOrbitCollapse
end GroupApproximation
