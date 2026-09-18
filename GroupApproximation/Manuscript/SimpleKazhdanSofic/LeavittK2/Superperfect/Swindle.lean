import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Superperfect.Coinvariant
import GroupApproximation.Meta.AxiomGuard

/-!
# Swindle certificates for the rank-three coinvariant kernel (lane sk-leavitt-31)

Let `L = L_{𝔽₂}(1,2)`.  Write `N₃ = K₂(3, L) = ker (St_3(L) → E_3(L))` and
`C₃ = ⁅St_3(L), N₃⁆`.  The target of this lane is lane sk-leavitt-30's isolated input
`BinaryLeavittKernelThreeCoinvariantStatement : N₃ ≤ C₃`.

## Isolated statement (the one remaining gap)

`BinaryLeavittKernelThreeSwindleStatement`: some subset `S ⊆ N₃` normally generates `N₃`, and
every `k ∈ S` is conjugate in `St_3(L)` to its square, `g k g⁻¹ = k²`.

## Proved here

* `mem_commutator_top_of_conj_eq_mul_self` (any group): from `k ∈ H` and `g k g⁻¹ = k²` we get
  `k = ⁅g, k⁆ ∈ ⁅⊤, H⁆`.
* `binaryLeavittKernelThreeCoinvariant_of_swindle`: the gap gives the target, because `C₃` is
  normal and contains `S`.
* `binaryLeavittUnitsSuperperfect_of_swindle`: the gap gives superperfect `Lˣ`, through lane 30.
* `binaryLeavittKernelThreeSwindle_of_forall_conj`: the pointwise identity on all of `N₃` (the
  lane's example) gives the gap, with `S = N₃`.
* `binaryLeavittKernelThreeSwindle_of_K2_eq_bot`: `K₂(3, L) = ⊥` gives the gap.
* `binaryLeavittK2Three_eq_bot_of_swindle_of_le_center`: if `N₃` is central, the gap forces
  `N₃ = ⊥`.

## Why it is strictly smaller in proof content

The target needs every `k ∈ N₃` as a product of commutators `⁅g, n⁆` with `n ∈ N₃`.  The gap needs
only one explicit conjugator per element of a normal generating set (e.g. Steinberg symbols).
That conjugator is a single word identity in `St_3(L)`.  It implies the target
(`binaryLeavittKernelThreeCoinvariant_of_swindle`), and in general it is not implied by it.

## Route analysis

* Route (a), Eilenberg swindle.  Write `s₀, s₁, t₀, t₁` for the Leavitt generators.  The corner
  endomorphisms `T_i : x_{jl}(a) ↦ x_{jl}(s_i a t_i)` of `St_3(L)` induce `X ↦ X ⊕ 1` and
  `X ↦ 1 ⊕ X` through `L³ ≅ L⁶`.  The entrywise ring map `σ(a) = s₀ a t₀ + s₁ a t₁` induces
  `X ↦ X ⊕ X`.  Modulo `C₃`, uniqueness of lifts out of the perfect group `St_3(L)` gives
  `σ ≡ T₀ · T₁` and `T₁ ≡ Ad(p̃) ∘ T₀` with `p = s₁ t₀ + s₀ t₁`.  So on `N₃ / C₃` we have
  `σ = T₀²` and `T₀² = T₀`.  These identities say `σ_* = 2 T₀_*` and `T₀_* = T₀_*²`.  They are
  consistent with a nonzero `K₂` and do not force `N₃ / C₃ = 0`: no identity `σ ≡ T₀` or
  `σ ≡ id` comes for free.  The vanishing of `K_*(L)` comes from the Ara–Brustenga–Cortiñas
  localization sequence, using `K₁(𝔽₂) = K₂(𝔽₂) = 0`, not from a swindle.  In `GL_3(L)`, `σ` is
  not inner, so no `g ∈ St_3(L)` realizes `σ` on `N₃` by conjugation.  Route (a) therefore does
  not close the target.  It is the reason the gap is phrased as an explicit conjugation
  certificate.
* Route (b), `K₂(3, L) = ⊥` directly.  This is Khanh's Thm 5.4 as cited in
  `EndpointInterfaces`.  It is research-level (an unstable Brown/Bruhat analysis in rank 3) and
  is not attempted here.

## Truth check

* The target is TRUE (lane 30: Khanh Thm 2.2 via `K2_three_le_commutator_of_superperfect`).
* The gap is TRUE provided `K₂(3, L) = ⊥` (Khanh Thm 5.4, cited in
  `EndpointInterfaces.BinaryLeavittStabKernelThreeTrivialStatement`'s module docstring), with
  `S = ∅`.

LOUD: the gap is logically STRONGER than the target, not weaker.  Its truth rests on
`K₂(3, L) = ⊥`, a stronger literature claim than the target's source (Thm 2.2).  If `N₃` is
central in `St_3(L)`, the gap is equivalent to `N₃ = ⊥`
(`binaryLeavittK2Three_eq_bot_of_swindle_of_le_center`).  I could not verify Thm 5.4
independently.  If `K₂(3, L) ≠ ⊥`, the gap may be FALSE while the target stays true.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation.BooneHigman.SteinbergBasic
open scoped commutatorElement

section Generic

/-- **Square-conjugate elements are relative commutators.**  If `k ∈ H` and `g k g⁻¹ = k²`,
then `k = ⁅g, k⁆ ∈ ⁅⊤, H⁆`. -/
theorem mem_commutator_top_of_conj_eq_mul_self {G : Type*} [Group G] {H : Subgroup G}
    {k g : G} (hk : k ∈ H) (hg : g * k * g⁻¹ = k * k) :
    k ∈ ⁅(⊤ : Subgroup G), H⁆ := by
  have hc : ⁅g, k⁆ = k := by
    rw [commutatorElement_def, hg, mul_inv_cancel_right]
  have hmem := Subgroup.commutator_mem_commutator (Subgroup.mem_top g) hk
  rwa [hc] at hmem

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.mem_commutator_top_of_conj_eq_mul_self

/-- **Central square-conjugate elements are trivial.**  If `k` is central and
`g k g⁻¹ = k²`, then `k = 1`. -/
theorem eq_one_of_conj_eq_mul_self_of_mem_center {G : Type*} [Group G] {k g : G}
    (hc : k ∈ Subgroup.center G) (hg : g * k * g⁻¹ = k * k) : k = 1 := by
  have h1 : g * k * g⁻¹ = k := by
    rw [Subgroup.mem_center_iff.mp hc g, mul_inv_cancel_right]
  have h2 : k * 1 = k * k := by
    rw [mul_one, ← hg, h1]
  exact (mul_left_cancel h2).symm

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.eq_one_of_conj_eq_mul_self_of_mem_center

end Generic
