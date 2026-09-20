import GroupApproximation.BooneHigmanLinear.RelGen.Tits
import GroupApproximation.Meta.AxiomGuard

/-!
# Stepanov's theorem, part 1: `z_ab` from two `z`'s through a third index

Lane bh-pal-wire, k2-poly H.L3 (L–S Remark 4.5 in type A). Let `G` be a subgroup containing
`St(Φ, J)`, and write `z_cd ⊆ G` for "every `z_cd(s, ξ)` with `s ∈ J` lies in `G`". Let
`m ∉ {a, b}`.

* `z_mem_of_col_pair`: `z_am ⊆ G` and `z_bm ⊆ G` give `z_ab ⊆ G` (the root `a - b` is the
  difference of `a - m` and `b - m`).
* `z_mem_of_row_pair`: `z_ma ⊆ G` and `z_mb ⊆ G` give `z_ab ⊆ G`.

Both expand `x_ab(s)` as a commutator through `m`, as in `RelGen.Tits.z_mem_zGen_ne`, and conjugate
by `x_ba(-ξ)`.
-/

namespace GroupApproximation.BooneHigmanLinear.RelGen

open scoped commutatorElement
open GroupApproximation.SteinbergGroup

variable {I : Type*} [Fintype I] [DecidableEq I] {R : Type*} [CommRing R] {J : Ideal R}

/-- `z_cd ⊆ G`: every `z_cd(s, ξ)` with `s ∈ J` lies in `G`. -/
def ZIn (G : Subgroup (SteinbergGroup I R)) (J : Ideal R) (c d : I) : Prop :=
  ∀ (hcd : c ≠ d) (s ξ : R), s ∈ J → zElt c d hcd s ξ ∈ G

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.ZIn

/-- `⟨x(J), z_cd(J, ·)⟩ ≤ G` when `St(Φ, J) ≤ G` and `z_cd ⊆ G`. -/
theorem zGen_single_le {G : Subgroup (SteinbergGroup I R)} (hx : xGroup I J ≤ G) {c d : I}
    (hz : ZIn G J c d) : zGen I J (fun i j => i = c ∧ j = d) ≤ G := by
  refine (Subgroup.closure_le _).mpr (Set.union_subset (fun g hg => hx
    (Subgroup.subset_closure hg)) ?_)
  rintro _ ⟨i, j, hij, s, ξ, ⟨rfl, rfl⟩, hs, rfl⟩
  exact hz hij s ξ hs

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.zGen_single_le

/-- **Column pair.** `z_am ⊆ G` and `z_bm ⊆ G` give `z_ab ⊆ G`. -/
theorem z_mem_of_col_pair {G : Subgroup (SteinbergGroup I R)} (hx : xGroup I J ≤ G) {a b m : I}
    (ham : a ≠ m) (hbm : b ≠ m) (h1 : ZIn G J a m) (h2 : ZIn G J b m) :
    ZIn G J a b := by
  intro hab' s ξ hs
  have hmb : m ≠ b := hbm.symm
  have hma : m ≠ a := ham.symm
  have hxab : x a b hab' s = ⁅x a m ham s, x m b hmb 1⁆ := by
    rw [x_commutator a m b ham hmb hab', mul_one]
  have hP : x b a hab'.symm (-ξ) * x a m ham s * (x b a hab'.symm (-ξ))⁻¹ =
      x b m hbm (-ξ * s) * x a m ham s := by
    rw [conj_eq_commutator_mul, x_commutator b a m hab'.symm ham hbm]
  have hQ : x b a hab'.symm (-ξ) * x m b hmb 1 * (x b a hab'.symm (-ξ))⁻¹ =
      x m a hma (-(1 * -ξ)) * x m b hmb 1 := by
    rw [conj_eq_commutator_mul, ← commutatorElement_inv, x_commutator m b a hmb hab'.symm hma,
      ← x_neg m a hma (1 * -ξ)]
  have hz : zElt a b hab' s ξ =
      ⁅x b a hab'.symm (-ξ) * x a m ham s * (x b a hab'.symm (-ξ))⁻¹,
        x b a hab'.symm (-ξ) * x m b hmb 1 * (x b a hab'.symm (-ξ))⁻¹⁆ := by
    rw [zElt_eq_conj, hxab]
    simp only [commutatorElement_def]
    group
  have hA : x m b hmb 1 * (x a m ham s)⁻¹ * (x m b hmb 1)⁻¹ =
      x a b hab' (-(-s * 1)) * x a m ham (-s) := by
    rw [← x_neg a m ham s, conj_eq_commutator_mul, ← commutatorElement_inv,
      x_commutator a m b ham hmb hab' (-s) 1, ← x_neg a b hab' (-s * 1)]
  have hB : x m b hmb 1 * (x b m hbm (-ξ * s))⁻¹ * (x m b hmb 1)⁻¹ =
      zElt b m hbm (-(-ξ * s)) (-1) := by
    rw [← x_neg b m hbm (-ξ * s), zElt, neg_neg, ← x_neg m b hmb 1]
  have hs1 : -(-s * 1) ∈ J := neg_mem (J.mul_mem_right 1 (neg_mem hs))
  have hs2 : -(-ξ * s) ∈ J := neg_mem (J.mul_mem_left (-ξ) hs)
  obtain ⟨U, hU⟩ : ∃ U, U = x m a hma (-(1 * -ξ)) := ⟨_, rfl⟩
  rw [← hU] at hQ
  have hmemA : U * (x a b hab' (-(-s * 1)) * x a m ham (-s)) * U⁻¹ ∈ G := by
    rw [show U * (x a b hab' (-(-s * 1)) * x a m ham (-s)) * U⁻¹ =
      (U * x a b hab' (-(-s * 1)) * U⁻¹) * (U * x a m ham (-s) * U⁻¹) by group, hU]
    refine Subgroup.mul_mem _ (hx ?_) (zGen_single_le hx h1 ?_)
    · exact conj_x_mem_xGroup hma hab' _ hs1 (fun h => hbm h.2)
    · exact conj_ba_x_ab ham hma _ (neg_mem hs)
  have hmemB : U * zElt b m hbm (-(-ξ * s)) (-1) * U⁻¹ ∈ G := by
    rw [hU]
    exact zGen_single_le hx h2 (conj_z_mem hbm hma _ (-1) hs2 (fun h => hmb h.1))
  have hmemP : x b m hbm (-ξ * s) * x a m ham s ∈ G :=
    hx (Subgroup.mul_mem _ (x_mem_xGroup hbm (J.mul_mem_left (-ξ) hs)) (x_mem_xGroup ham hs))
  rw [hz, hP, hQ]
  have e : ⁅x b m hbm (-ξ * s) * x a m ham s, U * x m b hmb 1⁆ =
      (x b m hbm (-ξ * s) * x a m ham s) *
        (U * (x m b hmb 1 * (x a m ham s)⁻¹ * (x m b hmb 1)⁻¹) * U⁻¹) *
        (U * (x m b hmb 1 * (x b m hbm (-ξ * s))⁻¹ * (x m b hmb 1)⁻¹) * U⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e, hA, hB]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hmemP hmemA) hmemB

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.z_mem_of_col_pair

/-- **Row pair.** `z_ma ⊆ G` and `z_mb ⊆ G` give `z_ab ⊆ G`. -/
theorem z_mem_of_row_pair {G : Subgroup (SteinbergGroup I R)} (hx : xGroup I J ≤ G) {a b m : I}
    (ham : a ≠ m) (hbm : b ≠ m) (h1 : ZIn G J m a) (h2 : ZIn G J m b) :
    ZIn G J a b := by
  intro hab' s ξ hs
  have hmb : m ≠ b := hbm.symm
  have hma : m ≠ a := ham.symm
  -- `x_ab(s) = ⁅x_am(1), x_mb(s)⁆`, conjugated by `X = x_ba(-ξ)`.
  have hxab : x a b hab' s = ⁅x a m ham 1, x m b hmb s⁆ := by
    rw [x_commutator a m b ham hmb hab', one_mul]
  have hP : x b a hab'.symm (-ξ) * x a m ham 1 * (x b a hab'.symm (-ξ))⁻¹ =
      x b m hbm (-ξ * 1) * x a m ham 1 := by
    rw [conj_eq_commutator_mul, x_commutator b a m hab'.symm ham hbm]
  have hQ : x b a hab'.symm (-ξ) * x m b hmb s * (x b a hab'.symm (-ξ))⁻¹ =
      x m a hma (-(s * -ξ)) * x m b hmb s := by
    rw [conj_eq_commutator_mul, ← commutatorElement_inv, x_commutator m b a hmb hab'.symm hma,
      ← x_neg m a hma (s * -ξ)]
  have hz : zElt a b hab' s ξ =
      ⁅x b a hab'.symm (-ξ) * x a m ham 1 * (x b a hab'.symm (-ξ))⁻¹,
        x b a hab'.symm (-ξ) * x m b hmb s * (x b a hab'.symm (-ξ))⁻¹⁆ := by
    rw [zElt_eq_conj, hxab]
    simp only [commutatorElement_def]
    group
  have hs1 : -(s * -ξ) ∈ J := neg_mem (J.mul_mem_right (-ξ) hs)
  -- With `V = x_bm(-ξ)`, `W = x_am(1)` and `t = sξ`:
  -- `W x_ma(t) W⁻¹ = z_ma(t, -1)` and `W x_mb(s) W⁻¹ = x_ab(s) x_mb(s)`.
  have hW1 : x a m ham 1 * x m a hma (-(s * -ξ)) * (x a m ham 1)⁻¹ =
      zElt m a hma (-(s * -ξ)) (-1) := by
    rw [zElt, neg_neg, x_neg]
  have hW2 : x a m ham 1 * x m b hmb s * (x a m ham 1)⁻¹ = x a b hab' (1 * s) * x m b hmb s := by
    rw [conj_eq_commutator_mul, x_commutator a m b ham hmb hab']
  have hmem1 : x b m hbm (-ξ * 1) * zElt m a hma (-(s * -ξ)) (-1) * (x b m hbm (-ξ * 1))⁻¹ ∈ G :=
    zGen_single_le hx h1 (conj_z_mem hma hbm _ _ hs1 (fun h => hbm h.1))
  have hmem2 : x b m hbm (-ξ * 1) * x a b hab' (1 * s) * (x b m hbm (-ξ * 1))⁻¹ ∈ G :=
    hx (conj_x_mem_xGroup hbm hab' _ (J.mul_mem_left 1 hs) (fun h => ham h.1))
  have hmem3 : x b m hbm (-ξ * 1) * x m b hmb s * (x b m hbm (-ξ * 1))⁻¹ ∈ G :=
    zGen_single_le hx h2 (conj_ba_x_ab hmb hbm _ hs)
  have hmemQ : (x m a hma (-(s * -ξ)) * x m b hmb s)⁻¹ ∈ G :=
    hx (Subgroup.inv_mem _ (Subgroup.mul_mem _ (x_mem_xGroup hma hs1) (x_mem_xGroup hmb hs)))
  rw [hz, hP, hQ]
  have e : ⁅x b m hbm (-ξ * 1) * x a m ham 1, x m a hma (-(s * -ξ)) * x m b hmb s⁆ =
      (x b m hbm (-ξ * 1) * (x a m ham 1 * x m a hma (-(s * -ξ)) * (x a m ham 1)⁻¹) *
          (x b m hbm (-ξ * 1))⁻¹) *
        (x b m hbm (-ξ * 1) * (x a m ham 1 * x m b hmb s * (x a m ham 1)⁻¹) *
          (x b m hbm (-ξ * 1))⁻¹) *
        (x m a hma (-(s * -ξ)) * x m b hmb s)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e, hW1, hW2]
  have e2 : x b m hbm (-ξ * 1) * (x a b hab' (1 * s) * x m b hmb s) * (x b m hbm (-ξ * 1))⁻¹ =
      (x b m hbm (-ξ * 1) * x a b hab' (1 * s) * (x b m hbm (-ξ * 1))⁻¹) *
        (x b m hbm (-ξ * 1) * x m b hmb s * (x b m hbm (-ξ * 1))⁻¹) := by group
  rw [e2]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hmem1 (Subgroup.mul_mem _ hmem2 hmem3)) hmemQ

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.z_mem_of_row_pair

end GroupApproximation.BooneHigmanLinear.RelGen
