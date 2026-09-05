import GroupApproximation.CharClass.ProjectiveSpaceRing

/-!
# Leray–Hirsch degree by degree, and the Chern classes it defines

The Leray–Hirsch theorem for a projective bundle `π : P → X` with fibre
`ℂP^{r-1}` says that in each degree

```text
H^n(P; F₂)  ≅  ⨁_{i < r,  2i ≤ n}  H^{n-2i}(X; F₂) · ξ^i,        ξ = e(taut).
```

Stating that in Lean means naming the index set.  Writing it as `Fin r` with
truncated subtraction is wrong — the summands with `2i > n` would contribute a
spurious copy of `H^0(X)` — so the index type here is
`Fin (lhDomainCard r n)` with `lhDomainCard r n = min r (n/2 + 1)`, which is
*exactly* `{i < r : 2i ≤ n}` and needs no side condition.

The pay-off is at `n = 2r`, where `lhDomainCard r (2r) = r`: the whole domain
survives, and the decomposition of `ξ^r` in it *is* the Grothendieck relation

```text
ξ^r  =  ∑_{i<r} π^*(γ_{r-i}) ⌣ ξ^i        (mod 2 there are no signs),
```

so the mod-2 Chern classes are read off with their degrees correct by
construction: `γ_k ∈ H^{2k}(X; F₂)`.  That is what this file delivers, and it
needs no ring structure and no graded commutativity — only the Leray–Hirsch
bijection, which enters as a `structure` field.

`CharClass/ChernClasses.lean` does the same thing over the even cohomology ring,
where `Polynomial` and `PowerBasis` are available and Whitney's formula is
multiplication of polynomials; the two views are the same classes, and the ring
view is the one that loses the grading, which is why this file exists.

## Main declarations

* `lhDomainCard`, `lhMap` — the index count and the Leray–Hirsch combination.
* `LerayHirschGraded` — the bijection in every degree, as a structure.
* `lhCoeff`, `lhCoeff_unique` — the coefficients of a class, and their uniqueness.
* `gamma` — the mod-2 Chern classes, `γ_k ∈ H^{2k}(X;F₂)`, with `γ_0 = 1`,
  `γ_k = 0` above the rank, and the defining relation `gamma_relation`.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory

noncomputable section

/-! ## 1. The index set -/

/-- The number of Leray–Hirsch summands in degree `n` for a rank-`r` bundle:
`min r (n/2 + 1)` is exactly the number of `i < r` with `2i ≤ n`. -/
def lhDomainCard (r n : ℕ) : ℕ := min r (n / 2 + 1)

theorem two_mul_le_of_lhDomain {r n : ℕ} (i : Fin (lhDomainCard r n)) :
    2 * (i : ℕ) ≤ n := by
  have h : (i : ℕ) < min r (n / 2 + 1) := i.2
  have h2 : (i : ℕ) < n / 2 + 1 := lt_of_lt_of_le h (min_le_right _ _)
  omega

theorem lt_rank_of_lhDomain {r n : ℕ} (i : Fin (lhDomainCard r n)) : (i : ℕ) < r :=
  lt_of_lt_of_le i.2 (min_le_left _ _)

/-- At degree `2r` every summand survives. -/
@[simp] theorem lhDomainCard_two_mul (r : ℕ) : lhDomainCard r (2 * r) = r := by
  unfold lhDomainCard
  omega

/-! ## 2. The Leray–Hirsch combination -/

variable {X P : TopCat.{0}}

/-- The Leray–Hirsch combination in degree `n`:
`(a_i) ↦ ∑_{i} π^*(a_i) ⌣ ξ^i`, the `i`-th summand taken from `H^{n-2i}(X)`. -/
def lhMap (π : P ⟶ X) (ξ : Hmod2 P 2) (r n : ℕ)
    (a : (i : Fin (lhDomainCard r n)) → Hmod2 X (n - 2 * (i : ℕ))) : Hmod2 P n :=
  ∑ i : Fin (lhDomainCard r n),
    cohCast (Nat.sub_add_cancel (two_mul_le_of_lhDomain i))
      (cup (pull π (n - 2 * (i : ℕ)) (a i)) (cupPowE ξ (i : ℕ)))

/-- **Leray–Hirsch, degree by degree.**  The single field is the statement that
`1, ξ, …, ξ^{r-1}` is a basis of `H^*(P)` over `H^*(X)` in every degree.  It is a
structure field because its proof is the Mayer–Vietoris induction over a finite
trivializing cover of the base, which lives downstream of this lane's peers; a
consumer only ever needs the bijection. -/
structure LerayHirschGraded (π : P ⟶ X) (ξ : Hmod2 P 2) (r : ℕ) : Prop where
  /-- The Leray–Hirsch map is bijective in every degree. -/
  bij : ∀ n : ℕ, Function.Bijective (lhMap π ξ r n)

namespace LerayHirschGraded

variable {π : P ⟶ X} {ξ : Hmod2 P 2} {r : ℕ} (L : LerayHirschGraded π ξ r)

/-- The Leray–Hirsch coefficients of a class. -/
def lhCoeff (n : ℕ) (z : Hmod2 P n) :
    (i : Fin (lhDomainCard r n)) → Hmod2 X (n - 2 * (i : ℕ)) :=
  (Equiv.ofBijective _ (L.bij n)).symm z

@[simp] theorem lhMap_lhCoeff (n : ℕ) (z : Hmod2 P n) :
    lhMap π ξ r n (L.lhCoeff n z) = z :=
  (Equiv.ofBijective _ (L.bij n)).apply_symm_apply z

/-- **Uniqueness of the coefficients.** -/
theorem lhCoeff_unique (n : ℕ) (z : Hmod2 P n)
    (c : (i : Fin (lhDomainCard r n)) → Hmod2 X (n - 2 * (i : ℕ)))
    (h : lhMap π ξ r n c = z) : c = L.lhCoeff n z :=
  (L.bij n).injective (by rw [h, L.lhMap_lhCoeff])

/-! ## 4. The mod-2 Chern classes -/

/-- The Leray–Hirsch coefficients of `ξ^r`.  At degree `2r` the index set is the
whole of `Fin r` (`lhDomainCard_two_mul`), so this family *is* the Grothendieck
relation. -/
def gammaCoeff : (i : Fin (lhDomainCard r (2 * r))) → Hmod2 X (2 * r - 2 * (i : ℕ)) :=
  L.lhCoeff (2 * r) (cupPowE ξ r)

/-- **The defining relation**, `ξ^r = ∑_{i<r} π^*(γ_{r-i}) ⌣ ξ^i`. -/
theorem lhMap_gammaCoeff : lhMap π ξ r (2 * r) L.gammaCoeff = cupPowE ξ r :=
  L.lhMap_lhCoeff (2 * r) (cupPowE ξ r)

/-- The `k`-th mod-2 Chern class for `1 ≤ k ≤ r`, read off the relation.  Its
degree is `2k` by construction: the coefficient of `ξ^{r-k}` lies in
`H^{2r - 2(r-k)}(X) = H^{2k}(X)`. -/
def gammaOf (k : ℕ) (hk1 : 0 < k) (hkr : k ≤ r) : Hmod2 X (2 * k) :=
  cohCast (show 2 * r - 2 * (r - k) = 2 * k by omega)
    (L.gammaCoeff ⟨r - k, by rw [lhDomainCard_two_mul]; omega⟩)

/-- **The mod-2 Chern classes** `γ_k(E) ∈ H^{2k}(X; F₂)`, with the conventions
`γ_0 = 1` and `γ_k = 0` above the rank. -/
def gamma (k : ℕ) : Hmod2 X (2 * k) :=
  if h : 0 < k ∧ k ≤ r then L.gammaOf k h.1 h.2
  else if hk : k = 0 then cohCast (show (0 : ℕ) = 2 * k by omega) (one X)
  else 0

@[simp] theorem gamma_zero : L.gamma 0 = one X := by
  rw [gamma, dif_neg (by omega : ¬ (0 < 0 ∧ (0 : ℕ) ≤ r)), dif_pos rfl]
  rfl

theorem gamma_eq_zero_of_gt {k : ℕ} (hk : r < k) : L.gamma k = 0 := by
  rw [gamma, dif_neg (by omega : ¬ (0 < k ∧ k ≤ r)), dif_neg (by omega : ¬ k = 0)]

theorem gamma_eq_gammaOf {k : ℕ} (hk1 : 0 < k) (hkr : k ≤ r) :
    L.gamma k = L.gammaOf k hk1 hkr :=
  dif_pos ⟨hk1, hkr⟩

end LerayHirschGraded

end

end CharClass
end GroupApproximation
