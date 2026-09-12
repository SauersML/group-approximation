import GroupApproximation.CharClass.ParityPSlice
import GroupApproximation.Meta.AxiomGuard

/-!
# Step D mod `p` at rank `n`: the uniform even side, instantiated

Lane `lix-evenside-n` of the STW Problem LIX strengthening programme
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`, §1.4; successor of `sp-evenside-n`).

`CharClass/ParityPData.lean` proves Step D mod `p` over an abstract pair of rings with the
fields a Künneth decomposition and the reduced powers supply, generic in the prime and in
the rank.  `CharClass/LIXStepDGenParity.lean` put the `F₂` even side at rank `n`.  This file
does the rank-`n` bridge at a general prime, and it does it by **instantiating**
`ParityPData`, never by re-deriving it: `ModPStepDData.toParityPData` builds the structure
and every conclusion below is `ParityPData.gamma_rank_eq_zero` read at the tower's index.

## Where the rank enters

The mapping torus is `N = S¹ × S^{2n+1} × Y` and `z = t x` has weight `n + 1`.  Three of
`ParityPData`'s fields are stated in the form an instantiator has them, and each of those
forms mentions the rank or the slice:

| `ParityPData` field | asked for here as | derived by |
|---|---|---|
| `pR_b_succ` | instability at weight `n + 1` | `ParityP.pR_b_succ_of_instability`, using `1 ≤ n` |
| `pH_z_mul` | Cartan, `P⁰ = id`, `P^{>0} z = 0` | `ParityP.pH_z_mul_of_cartan` |
| `a_eq_zero` | the slice class `∏ⱼ (1 + hⱼ)^{dⱼ}` with `p ∣ dⱼ` | `ParityP.sliceClass_coeff_eq_zero_of_not_dvd` |

The remaining fields — Künneth, `z² = 0`, naturality of the powers through `ι`, and the
diagonal Wu relation with a **unit** leading coefficient — are the same at every rank and
are asked for verbatim.

## The index orientation

`ParityPData.gamma_rank_eq_zero` concludes `γ (n + 1 + m) = 0`.  The tower and the `F₂`
rank-`n` even side read the rank as `m + (n + 1)`, which is the shape whose `n = 2`
instance is definitionally the landed `m + 3` (`Nat.add` recurses on its second argument,
so `m + 3` whnf-reduces while `3 + m` is stuck).  `gamma_rank_eq_zero_modP` below is the
theorem in that orientation, so no consumer pays an `add_comm` rewrite.

## Main results

* `Gen.gamma_rank_eq_zero_modP` — `ParityPData.gamma_rank_eq_zero` at index `m + (n + 1)`.
* `Gen.ModPStepDData` — the hypotheses of Step D mod `p` for one bundle, at rank `n`.
* `Gen.ModPStepDData.toParityPData` — **the instance**.
* `Gen.ModPStepDData.gamma_top_eq_zero` — `γ_{(∑ⱼ dⱼ) + n + 1}(W) = 0` from `p ∣ n` and
  `p ∣ dⱼ` for every `j`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation.CharClass

open ParityP

namespace Gen

/-! ## 1. The uniform conclusion in the tower's orientation -/

/-- **`ParityPData.gamma_rank_eq_zero`, read at `m + (n + 1)`.**  A Chern class whose total
index is the rank `m + (n + 1)` of a stage vanishes when `p ∣ n`, `p ∣ m` and its
`H^*(Y)`-component vanishes. -/
theorem gamma_rank_eq_zero_modP {p : ℕ} {R H : Type*} [CommRing R] [CommRing H]
    (P : ParityPData p R H) {n m : ℕ} (hn : p ∣ n)
    (hm : p ∣ m) (ha : P.a (m + (n + 1)) = 0) : P.γ (m + (n + 1)) = 0 := by
  have e : n + 1 + m = m + (n + 1) := by omega
  rw [← e]
  refine P.gamma_rank_eq_zero hn hm ?_
  rw [e]
  exact ha

/-! ## 2. The hypotheses at rank `n` -/

/-- **The hypotheses of Step D mod `p` at rank `n`**, for one bundle `W` over
`N = S¹ × S^{2n+1} × Y`, `Y = ∏ⱼ ℂP^{dⱼ}`.

`R` is `H^*(Y; F_p)`, `H` the even part of `H^*(N; F_p)`, `γ k` the `k`-th mod-`p` Chern
class of `W`, and `a k`, `b k` its two Künneth components.  The fields are those of
`ParityPData` with three of them in the form their producers state them (see the module
docstring); the prime itself is a hypothesis of the theorems, not a field. -/
structure ModPStepDData (n p : ℕ) {ℓ : ℕ} (dd : Fin ℓ → ℕ) (R H : Type*) [CommRing R]
    [CommRing H] (γ : ℕ → H) where
  /-- The Künneth inclusion `H^*(Y) → H^*(N)`. -/
  ι : R →+* H
  /-- The class `z = t x`, of weight `n + 1`. -/
  z : H
  /-- `z² = 0`. -/
  z_mul_z : z * z = 0
  /-- Künneth: the `z`-component is well defined. -/
  z_inj : ∀ u v : R, ι u + z * ι v = 0 → v = 0
  /-- The reduced powers on the even part of `H^*(N)`. -/
  PH : ℕ → H →+ H
  /-- The reduced powers on `H^*(Y)`. -/
  PR : ℕ → R →+ R
  /-- `P⁰ = id`. -/
  pH_zero : ∀ u : H, PH 0 u = u
  /-- The Cartan formula. -/
  cartan : ∀ (i : ℕ) (u v : H),
    PH i (u * v) = ∑ j ∈ Finset.range (i + 1), PH j u * PH (i - j) v
  /-- `P(z) = z`: the positive powers kill `z`. -/
  pH_z : ∀ i : ℕ, 0 < i → PH i z = 0
  /-- Naturality through the Künneth inclusion. -/
  pH_ι : ∀ (i : ℕ) (r : R), PH i (ι r) = ι (PR i r)
  /-- The `H^*(Y)`-component of `γ k`, of weight `k`. -/
  a : ℕ → R
  /-- The `z H^*(Y)`-component of `γ k`, indexed by the total index. -/
  b : ℕ → R
  /-- The Künneth decomposition of the Chern classes. -/
  γ_eq : ∀ k : ℕ, γ k = ι (a k) + z * ι (b k)
  /-- Instability at the rank-`n` weight: `b k` has weight `k − (n + 1)`, and `P^i` kills
  a class of weight `< i`. -/
  instability : Instability PR b (n + 1)
  /-- The degree-two generators `hⱼ`. -/
  gen : Fin ℓ → R
  /-- The slice class of `W` is `∏ⱼ (1 + hⱼ)^{dⱼ}`. -/
  slice : ∀ q : ℕ, a q = (sliceClass Finset.univ gen dd).coeff q
  /-- The leading coefficient of the diagonal Wu relation. -/
  c : ℕ → R
  /-- The leading coefficient is a unit (`sp-steenrod`'s `κ`, never a bare `1`). -/
  c_isUnit : ∀ i : ℕ, IsUnit (c i)
  /-- The diagonal Wu relation: `P^i(γ_{i+1}) = c_i·γ_{ip+1} + (decomposables)`. -/
  wu : ∀ i : ℕ, IsDecomposable γ (i * p + 1)
    (PH i (γ (i + 1)) - ι (c i) * γ (i * p + 1))

namespace ModPStepDData

variable {n p ℓ : ℕ} {dd : Fin ℓ → ℕ} {R H : Type*} [CommRing R] [CommRing H] {γ : ℕ → H}

/-- **The instance.**  The rank-`n` data is a `ParityPData p`: the three derived fields
come from their producers, every other field is carried over. -/
def toParityPData (D : ModPStepDData n p dd R H γ) (hp : 2 ≤ p) (hn : 1 ≤ n)
    [ExpChar R p] (hd : ∀ j, p ∣ dd j) : ParityPData p R H where
  p_two_le := hp
  ι := D.ι
  z := D.z
  z_mul_z := D.z_mul_z
  z_inj := D.z_inj
  PH := D.PH
  PR := D.PR
  pH_ι := D.pH_ι
  pH_z_mul := pH_z_mul_of_cartan D.pH_zero D.cartan D.pH_z D.pH_ι
  γ := γ
  a := D.a
  b := D.b
  γ_eq := D.γ_eq
  a_eq_zero := fun q hq => by
    rw [D.slice q]
    exact sliceClass_coeff_eq_zero_of_not_dvd p (by omega) Finset.univ D.gen dd
      (fun j _ => hd j) hq
  pR_b_succ := pR_b_succ_of_instability (by omega) D.instability
  c := D.c
  c_isUnit := D.c_isUnit
  wu := D.wu

/-- **Step D mod `p` at rank `n`.**  If `p ∣ n` and `p` divides every `dⱼ`, the Chern class
of `W` at the rank `(∑ⱼ dⱼ) + (n + 1)` vanishes.  Only `p ∣ n` and `p ∣ dⱼ` are used about
the rank and the dimensions; nothing about the tower stage. -/
theorem gamma_top_eq_zero (D : ModPStepDData n p dd R H γ) (hp : 2 ≤ p) (hn : 1 ≤ n)
    [ExpChar R p] (hpn : p ∣ n) (hd : ∀ j, p ∣ dd j) :
    γ ((∑ j, dd j) + (n + 1)) = 0 := by
  have hm : p ∣ ∑ j, dd j := Finset.dvd_sum fun j _ => hd j
  refine gamma_rank_eq_zero_modP (D.toParityPData hp hn hd) hpn hm ?_
  show D.a ((∑ j, dd j) + (n + 1)) = 0
  rw [D.slice]
  exact sliceClass_coeff_eq_zero_of_lt Finset.univ D.gen dd (by omega)

end ModPStepDData

end Gen

#audit_axioms Gen.gamma_rank_eq_zero_modP
#audit_axioms Gen.ModPStepDData.toParityPData
#audit_axioms Gen.ModPStepDData.gamma_top_eq_zero

end GroupApproximation.CharClass
