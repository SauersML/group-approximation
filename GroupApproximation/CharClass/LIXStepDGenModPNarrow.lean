import GroupApproximation.CharClass.LIXStepDGenModP
import GroupApproximation.CharClass.ParityPDataNarrow
import GroupApproximation.Meta.AxiomGuard

/-!
# Step D mod `p` at rank `n`, with the reduced powers asked only where they are used

Lane `lx-slice2` of the LIX strongest swarm (finding of `lx-review`, design of `lx-design`).

`Gen.ModPStepDData` (`CharClass/LIXStepDGenModP.lean`) asks for `P⁰ = id` on every class, the
Cartan formula and `P^{>0} z = 0`, and uses the three only to derive `ParityPData.pH_z_mul`,
whose one use is right after `P^i (b (i + 1)) = 0`.  Raw reduced powers fail `P⁰ = id`
(`P⁰ z = (−1)^{n+1} z` at the torus), so a producer of the old structure would owe a
normalisation nothing needs.

`Gen.ModPStepDDataN` replaces the three fields by the vanishing form
`pH_z_mul_zero : PR i r = 0 → PH i (z * ι r) = 0`, the field of lx-splitK's `ParityPDataN`
(`CharClass/ParityPDataNarrow.lean`).  At the real torus the intended producer is the
multiplicativity of the operations at `z` (`P^i (z · w) = c · z · P^i w` with `c` arbitrary)
together with naturality through `ι`.  The old structure is untouched.

## Main declarations

* `Gen.ModPStepDDataN` — the narrowed hypotheses.
* `Gen.ModPStepDDataN.toParityPDataN` — **the instance**.
* `Gen.ModPStepDDataN.gamma_top_eq_zero` — `γ_{(∑ⱼ dⱼ) + n + 1}(W) = 0` from `p ∣ n` and
  `p ∣ dⱼ` for every `j`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation.CharClass

open ParityP

namespace Gen

/-- **The hypotheses of Step D mod `p` at rank `n`, narrowed.**  The fields of
`Gen.ModPStepDData` with `pH_zero`, `cartan` and `pH_z` replaced by `pH_z_mul_zero`. -/
structure ModPStepDDataN (n p : ℕ) {ℓ : ℕ} (dd : Fin ℓ → ℕ) (R H : Type*) [CommRing R]
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
  /-- Naturality through the Künneth inclusion. -/
  pH_ι : ∀ (i : ℕ) (r : R), PH i (ι r) = ι (PR i r)
  /-- `P^i` kills `z · ι r` whenever it kills `r`. -/
  pH_z_mul_zero : ∀ (i : ℕ) (r : R), PR i r = 0 → PH i (z * ι r) = 0
  /-- The `H^*(Y)`-component of `γ k`, of weight `k`. -/
  a : ℕ → R
  /-- The `z H^*(Y)`-component of `γ k`, indexed by the total index. -/
  b : ℕ → R
  /-- The Künneth decomposition of the Chern classes. -/
  γ_eq : ∀ k : ℕ, γ k = ι (a k) + z * ι (b k)
  /-- Instability at the rank-`n` weight. -/
  instability : Instability PR b (n + 1)
  /-- The degree-two generators `hⱼ`. -/
  gen : Fin ℓ → R
  /-- The slice class of `W` is `∏ⱼ (1 + hⱼ)^{dⱼ}`. -/
  slice : ∀ q : ℕ, a q = (sliceClass Finset.univ gen dd).coeff q
  /-- The leading coefficient of the diagonal Wu relation. -/
  c : ℕ → R
  /-- The leading coefficient is a unit. -/
  c_isUnit : ∀ i : ℕ, IsUnit (c i)
  /-- The diagonal Wu relation: `P^i(γ_{i+1}) = c_i·γ_{ip+1} + (decomposables)`. -/
  wu : ∀ i : ℕ, IsDecomposable γ (i * p + 1)
    (PH i (γ (i + 1)) - ι (c i) * γ (i * p + 1))

namespace ModPStepDDataN

variable {n p ℓ : ℕ} {dd : Fin ℓ → ℕ} {R H : Type*} [CommRing R] [CommRing H] {γ : ℕ → H}

/-- **The instance.**  The narrowed rank-`n` data is a `ParityPDataN p`: the Frobenius support
comes from the slice class, the instability field from the weight, and every other field is
carried over. -/
def toParityPDataN (D : ModPStepDDataN n p dd R H γ) (hp : 2 ≤ p) (hn : 1 ≤ n)
    [ExpChar R p] (hd : ∀ j, p ∣ dd j) : ParityPDataN p R H where
  p_two_le := hp
  ι := D.ι
  z := D.z
  z_mul_z := D.z_mul_z
  z_inj := D.z_inj
  PH := D.PH
  PR := D.PR
  pH_ι := D.pH_ι
  pH_z_mul_zero := D.pH_z_mul_zero
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

/-- **Step D mod `p` at rank `n`, narrowed.**  If `p ∣ n` and `p` divides every `dⱼ`, the Chern
class of `W` at the rank `(∑ⱼ dⱼ) + (n + 1)` vanishes. -/
theorem gamma_top_eq_zero (D : ModPStepDDataN n p dd R H γ) (hp : 2 ≤ p) (hn : 1 ≤ n)
    [ExpChar R p] (hpn : p ∣ n) (hd : ∀ j, p ∣ dd j) :
    γ ((∑ j, dd j) + (n + 1)) = 0 := by
  have hm : p ∣ ∑ j, dd j := Finset.dvd_sum fun j _ => hd j
  have e : (∑ j, dd j) + (n + 1) = n + 1 + ∑ j, dd j := by omega
  rw [e]
  refine (D.toParityPDataN hp hn hd).gamma_rank_eq_zero hpn hm ?_
  show D.a (n + 1 + ∑ j, dd j) = 0
  rw [D.slice]
  exact sliceClass_coeff_eq_zero_of_lt Finset.univ D.gen dd (by omega)

end ModPStepDDataN

end Gen

#audit_axioms Gen.ModPStepDDataN.toParityPDataN
#audit_axioms Gen.ModPStepDDataN.gamma_top_eq_zero

end GroupApproximation.CharClass
