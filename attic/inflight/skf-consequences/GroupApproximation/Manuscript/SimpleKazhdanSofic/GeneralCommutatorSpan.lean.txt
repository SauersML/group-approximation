import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralRoot
import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralCommutatorProducts
import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralTowerUnits
import Mathlib.Tactic.NoncommRing

/-!
# The commutator witness for a topologically free action

`simple_kazhdan_sofic_group.tex` at 37551fd93, `\label{sec:proof}`, subsection "Simplicity", tex
l.152–154 and l.188–197:

> Let $1\ne K\trianglelefteq G$ and $1\ne g\in K$, and let $w\ge0$ bound the word lengths of the
> $\xi$ with $u_\xi$ occurring in the entries of $g$ and $g^{-1}$. … Put $k=[g,h]\in K\setminus\{1\}$.
> … The entries of $ghg^{-1}-I_3=g\,e_VE_{ij}\,g^{-1}$ are sums of such products, and
> $h^{-1}=h=I_3+\epsilon_{ee}E_{ij}$, so $k-I_3=(ghg^{-1}-h)h$ and $k^{-1}-I_3=h(ghg^{-1}-h)$ lie in
> $M_3(A_V)$.

The finite set `B` plays the printed ball `B_w`: it contains `e`, every `ξ` with `u_ξ` occurring in
the entries of `g` and `g⁻¹`, and their inverses.  `D ⊇ B · B` plays `B_{2w}`.  Here `A_V` is
skf-consequences' `epsilonSpan`, and `A_V` being a ring (tex l.180–181) is `epsilonSpan_mul_mem`,
over skf-consequences' `epsilon_mul_epsilon`.

* `epsilonSpan_mul_mem`: `A_V` is closed under products;
* `generalCommutatorWitness`: every nontrivial normal subgroup of `EL_n(LC(Z, F₂) ⋊ Λ)`, `n ≥ 2`,
  contains the witness of `GeneralCommutatorWitness`;
* the closed endpoint `printedGeneralCommutatorWitness`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace General

open scoped Pointwise commutatorElement

variable {Λ Z : Type*} [Group Λ] [TopologicalSpace Z] [MulAction Λ Z] [ContinuousConstSMul Λ Z]

/-- **`A_V` is a ring** (tex l.180–181): the span of the `ε_ab`, `a, b ∈ B`, is closed under products
when the translates `aV`, `a ∈ B`, are pairwise disjoint. -/
theorem epsilonSpan_mul_mem [DecidableEq Λ] {R : Type*} [Ring R]
    {coeff : LocallyConstant Z (ZMod 2) →+* R} {u : Λ →* Rˣ} (hcov : IsCovariantPair coeff u)
    {B : Finset Λ} {V : Set Z} (hV : IsClopen V) (hdisj : TranslatesDisjoint B V) {x y : R}
    (hx : x ∈ epsilonSpan coeff u B hV) (hy : y ∈ epsilonSpan coeff u B hV) :
    x * y ∈ epsilonSpan coeff u B hV := by
  have hgen : ∀ a ∈ B, ∀ b ∈ B, ∀ y ∈ epsilonSpan coeff u B hV,
      epsilon coeff u hV a b * y ∈ epsilonSpan coeff u B hV := by
    intro a ha b hb y hy
    have hle : epsilonSpan coeff u B hV ≤
        (epsilonSpan coeff u B hV).comap (AddMonoidHom.mulLeft (epsilon coeff u hV a b)) := by
      refine (AddSubgroup.closure_le (K := _)).2 ?_
      rintro _ ⟨a', ha', b', hb', rfl⟩
      show epsilon coeff u hV a b * epsilon coeff u hV a' b' ∈ epsilonSpan coeff u B hV
      rw [epsilon_mul_epsilon hcov hV hdisj hb ha']
      split_ifs
      · exact AddSubgroup.subset_closure ⟨a, ha, b', hb', rfl⟩
      · exact AddSubgroup.zero_mem _
    exact hle hy
  have hle : epsilonSpan coeff u B hV ≤
      (epsilonSpan coeff u B hV).comap (AddMonoidHom.mulRight y) := by
    refine (AddSubgroup.closure_le (K := _)).2 ?_
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact hgen a ha b hb y hy
  exact hle hx

variable [TotallySeparatedSpace Z] [MulSemiringAction Λ (LocallyConstant Z (ZMod 2))]

/-- **The commutator witness** (tex l.152–154, 188–197): for a topologically free action, every
nontrivial normal subgroup `K` of `EL_n(LC(Z, F₂) ⋊ Λ)`, `n ≥ 2`, contains `k = [g, h] ≠ 1`, with
`h = e_{ij}(e_V)` over a small nonempty `V`, such that `k - I` and `k⁻¹ - I` lie in `M_n(A_V)`. -/
theorem generalCommutatorWitness
    (hact : ∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z))
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → interior {z : Z | ξ • z = z} = ∅) {n : ℕ} (hn : 2 ≤ n) :
    GeneralCommutatorWitness (coeffHom Λ Z) (unitHom Λ Z) n := by
  classical
  intro K hK hne
  have hex : ∃ g ∈ K, g ≠ 1 := by
    by_contra h
    exact hne ((Subgroup.eq_bot_iff_forall K).mpr fun x hx =>
      Classical.byContradiction fun hx1 => h ⟨x, hx, hx1⟩)
  obtain ⟨g, hgK, hg1⟩ := hex
  -- the `ξ` occurring in the entries of `g` and `g⁻¹`
  obtain ⟨S, hS⟩ : ∃ S : Finset Λ, ∀ (p q : Fin n) (ξ : Λ),
      (ξ ∈ SkewMonoidAlgebra.support (mat g p q) → ξ ∈ S) ∧
        (ξ ∈ SkewMonoidAlgebra.support (mat g⁻¹ p q) → ξ ∈ S) :=
    ⟨Finset.univ.biUnion fun pq : Fin n × Fin n =>
      SkewMonoidAlgebra.support (mat g pq.1 pq.2) ∪ SkewMonoidAlgebra.support (mat g⁻¹ pq.1 pq.2),
      fun p q ξ =>
        ⟨fun h => Finset.mem_biUnion.mpr ⟨(p, q), Finset.mem_univ _, Finset.mem_union_left _ h⟩,
          fun h => Finset.mem_biUnion.mpr ⟨(p, q), Finset.mem_univ _, Finset.mem_union_right _ h⟩⟩⟩
  -- the ball `B_w`
  obtain ⟨B, hB1, hBS, hBinv⟩ : ∃ B : Finset Λ, (1 : Λ) ∈ B ∧ (∀ ξ ∈ S, ξ ∈ B) ∧
      ∀ ξ ∈ B, ξ⁻¹ ∈ B := by
    refine ⟨insert 1 (S ∪ S.image fun ξ => ξ⁻¹), Finset.mem_insert_self _ _,
      fun ξ hξ => Finset.mem_insert_of_mem (Finset.mem_union_left _ hξ), fun ξ hξ => ?_⟩
    rcases Finset.mem_insert.mp hξ with h1 | h2
    · rw [h1, inv_one]
      exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem ?_
      rcases Finset.mem_union.mp h2 with h3 | h4
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h3)
      · obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp h4
        rw [inv_inv]
        exact Finset.mem_union_left _ hη
  -- the ball `B_{2w}`
  obtain ⟨D, hD⟩ : ∃ D : Finset Λ, ∀ a ∈ B, ∀ b ∈ B, a * b ∈ D :=
    ⟨(B ×ˢ B).image fun p => p.1 * p.2, fun a ha b hb =>
      Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩⟩
  -- the coefficients of the entries of `g` and `g⁻¹`
  obtain ⟨F, hF⟩ : ∃ F : Finset (LocallyConstant Z (ZMod 2)), ∀ (p q : Fin n) (ξ : Λ),
      (ξ ∈ SkewMonoidAlgebra.support (mat g p q) → SkewMonoidAlgebra.coeff (mat g p q) ξ ∈ F) ∧
        (ξ ∈ SkewMonoidAlgebra.support (mat g⁻¹ p q) →
          SkewMonoidAlgebra.coeff (mat g⁻¹ p q) ξ ∈ F) :=
    ⟨Finset.univ.biUnion fun pq : Fin n × Fin n =>
      (SkewMonoidAlgebra.support (mat g pq.1 pq.2)).image
          (fun ξ => SkewMonoidAlgebra.coeff (mat g pq.1 pq.2) ξ) ∪
        (SkewMonoidAlgebra.support (mat g⁻¹ pq.1 pq.2)).image
          (fun ξ => SkewMonoidAlgebra.coeff (mat g⁻¹ pq.1 pq.2) ξ),
      fun p q ξ =>
        ⟨fun h => Finset.mem_biUnion.mpr ⟨(p, q), Finset.mem_univ _,
            Finset.mem_union_left _ (Finset.mem_image_of_mem _ h)⟩,
          fun h => Finset.mem_biUnion.mpr ⟨(p, q), Finset.mem_univ _,
            Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)⟩⟩⟩
  have hsupp : ∀ (p q : Fin n) (ξ : Λ), ξ ∈ SkewMonoidAlgebra.support (mat g p q) → ξ ∈ D := by
    intro p q ξ hξ
    have h := hD ξ (hBS ξ ((hS p q ξ).1 hξ)) 1 hB1
    rwa [mul_one] at h
  -- tex l.161: a noncommuting root over a small set
  obtain ⟨V, hV, hVne, hVs, i, j, hij, hgh⟩ :=
    exists_isSmall_not_commute_elGen hact hfree D B F hn hsupp hg1
  have hdisj : TranslatesDisjoint B V := by
    intro a ha b hb hab
    rw [Set.disjoint_left]
    intro z hza hzb
    have h1 : a⁻¹ • z ∈ V := Set.mem_smul_set_iff_inv_smul_mem.mp hza
    have h2 : b⁻¹ • z ∈ V := Set.mem_smul_set_iff_inv_smul_mem.mp hzb
    have hne1 : a⁻¹ * b ≠ 1 := fun h => hab (inv_mul_eq_one.mp h)
    have hmem : a⁻¹ • z ∈ (a⁻¹ * b) • V := by
      rw [Set.mem_smul_set_iff_inv_smul_mem, mul_inv_rev, inv_inv, mul_smul, smul_inv_smul]
      exact h2
    exact Set.disjoint_left.mp (hVs.1 _ (hD a⁻¹ (hBinv a ha) b hb) hne1) h1 hmem
  -- `k = [g, h] ∈ K ∖ {1}`
  have hkK : ⁅g, elGen i j hij (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV))⁆ ∈
      K := by
    have h1 : elGen i j hij (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV)) * g⁻¹ *
        (elGen i j hij (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV)))⁻¹ ∈ K :=
      hK.conj_mem g⁻¹ (K.inv_mem hgK) _
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    rw [mul_assoc] at h1
    exact K.mul_mem hgK h1
  have hk1 : ⁅g, elGen i j hij (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV))⁆ ≠
      1 := fun h1 => hgh (commutatorElement_eq_one_iff_commute.mp h1)
  have hGG : mat g * mat g⁻¹ = 1 := by
    simp only [mat, Subgroup.coe_inv, Units.mul_inv]
  have he : SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV) ∈
      epsilonSpan (coeffHom Λ Z) (unitHom Λ Z) B hV := charFn_mem_epsilonSpan hB1 hV
  have hmul : ∀ {x y : SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ},
      x ∈ epsilonSpan (coeffHom Λ Z) (unitHom Λ Z) B hV →
        y ∈ epsilonSpan (coeffHom Λ Z) (unitHom Λ Z) B hV →
          x * y ∈ epsilonSpan (coeffHom Λ Z) (unitHom Λ Z) B hV :=
    fun hx hy => epsilonSpan_mul_mem (isCovariantPair hact) hV hdisj hx hy
  -- tex l.194–195: the entries of `ghg⁻¹ - I = g e_V E_{ij} g⁻¹` lie in `A_V`
  have hM : ∀ p q : Fin n,
      (mat g * Matrix.single i j (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV)) *
        mat g⁻¹) p q ∈ epsilonSpan (coeffHom Λ Z) (unitHom Λ Z) B hV := by
    intro p q
    rw [mul_single_mul_apply]
    refine mul_charFn_mul_mem hact hV
      (fun a ha => ⟨hBS a ((hS p i a).1 ha), fun x hx y hy =>
        hVs.2 _ ((hF p i a).1 ha) a (hBS a ((hS p i a).1 ha)) x hx y hy⟩)
      (fun b hb => ⟨hBinv b (hBS b ((hS j q b).2 hb)), fun x hx y hy => ?_⟩)
    have h := hVs.2 _ ((hF j q b).2 hb) 1 hB1 x hx y hy
    rwa [one_smul, one_smul] at h
  -- tex l.196: `h = I + ε_{ee} E_{ij}`
  have hE : ∀ p q : Fin n,
      Matrix.single i j (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV)) p q ∈
        epsilonSpan (coeffHom Λ Z) (unitHom Λ Z) B hV := by
    intro p q
    rw [Matrix.single_apply]
    split_ifs
    · exact he
    · exact AddSubgroup.zero_mem _
  -- tex l.196–197: `k - I` and `k⁻¹ - I`
  have hk : mat ⁅g, elGen i j hij (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV))⁆ -
        1 =
      mat g * Matrix.single i j (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV)) *
          mat g⁻¹ -
        Matrix.single i j (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV)) -
        mat g * Matrix.single i j (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV)) *
          mat g⁻¹ *
          Matrix.single i j (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV)) := by
    have h2 : mat g *
          (1 + Matrix.single i j (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV))) *
          mat g⁻¹ =
        1 + mat g *
          Matrix.single i j (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV)) *
            mat g⁻¹ := by
      rw [mul_add, mul_one, add_mul, hGG]
    show mat g *
          (1 + Matrix.single i j (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV))) *
          mat g⁻¹ *
          (1 - Matrix.single i j (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV))) -
        1 = _
    rw [h2, add_mul, one_mul, mul_sub, mul_one]
    abel
  have hk' : mat ⁅g, elGen i j hij
        (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV))⁆⁻¹ - 1 =
      Matrix.single i j (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV)) -
        mat g * Matrix.single i j (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV)) *
          mat g⁻¹ -
        Matrix.single i j (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV)) *
          (mat g *
            Matrix.single i j (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV)) *
            mat g⁻¹) := by
    rw [commutatorElement_inv]
    have h1 : mat g *
          (1 - Matrix.single i j (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV))) *
          mat g⁻¹ =
        1 - mat g *
          Matrix.single i j (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV)) *
            mat g⁻¹ := by
      rw [mul_sub, mul_one, sub_mul, hGG]
    show (1 + Matrix.single i j (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV))) *
          mat g *
          (1 - Matrix.single i j (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV))) *
          mat g⁻¹ - 1 = _
    have h3 : (1 + Matrix.single i j (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV))) *
          mat g *
          (1 - Matrix.single i j (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV))) *
          mat g⁻¹ =
        (1 + Matrix.single i j (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV))) *
          (mat g *
            (1 - Matrix.single i j (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV))) *
            mat g⁻¹) := by
      noncomm_ring
    rw [h3, h1, add_mul, one_mul, mul_sub, mul_one]
    abel
  refine ⟨V, hV, B,
    ⁅g, elGen i j hij (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV))⁆, hVne, hB1,
    hdisj, hkK, hk1, fun p q => ⟨?_, ?_⟩⟩
  · show (mat ⁅g, elGen i j hij
        (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV))⁆ - 1) p q ∈
      epsilonSpan (coeffHom Λ Z) (unitHom Λ Z) B hV
    rw [hk, Matrix.sub_apply, Matrix.sub_apply, ElementarySimplicity.mul_single_apply]
    refine AddSubgroup.sub_mem _ (AddSubgroup.sub_mem _ (hM p q) (hE p q)) ?_
    split_ifs
    · exact hmul (hM p i) he
    · exact AddSubgroup.zero_mem _
  · show (mat ⁅g, elGen i j hij
        (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV))⁆⁻¹ - 1) p q ∈
      epsilonSpan (coeffHom Λ Z) (unitHom Λ Z) B hV
    rw [hk', Matrix.sub_apply, Matrix.sub_apply, ElementarySimplicity.single_mul_apply]
    refine AddSubgroup.sub_mem _ (AddSubgroup.sub_mem _ (hE p q) (hM p q)) ?_
    split_ifs
    · exact hmul he (hM j q)
    · exact AddSubgroup.zero_mem _

/-- **tex l.152–154, 161, 188–197, as printed**: for a group acting topologically freely by
homeomorphisms on a totally separated space, `LC(Z, F₂) ⋊ Λ` is a covariant pair, and every
nontrivial normal subgroup of `EL_n`, `n ≥ 2`, contains the commutator witness. -/
def PrintedGeneralCommutatorWitness : Prop :=
  ∀ (Λ Z : Type) [Group Λ] [TopologicalSpace Z] [TotallySeparatedSpace Z] [MulAction Λ Z]
    [ContinuousConstSMul Λ Z] [MulSemiringAction Λ (LocallyConstant Z (ZMod 2))],
    (∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z)) →
    (∀ ξ : Λ, ξ ≠ 1 → interior {z : Z | ξ • z = z} = ∅) →
    IsCovariantPair (coeffHom Λ Z) (unitHom Λ Z) ∧
      ∀ n : ℕ, 2 ≤ n → GeneralCommutatorWitness (coeffHom Λ Z) (unitHom Λ Z) n

theorem printedGeneralCommutatorWitness : PrintedGeneralCommutatorWitness :=
  fun _ _ _ _ _ _ _ _ hact hfree =>
    ⟨isCovariantPair hact, fun _ hn => generalCommutatorWitness hact hfree hn⟩

end General
end SimpleKazhdanSofic
end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.epsilonSpan_mul_mem
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.generalCommutatorWitness
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.General.printedGeneralCommutatorWitness
