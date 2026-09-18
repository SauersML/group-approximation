import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralCommutatorSpan
import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralSimplicityNormalSubgroup
import GroupApproximation.Meta.AxiomGuard

/-!
# Step 2 of the simplicity proof: the entries of the commutator lie in `A_V`

`simple_kazhdan_sofic_group.tex` (HEAD), subsection "Simplicity", Step 2, tex l.289–292:

> The entries of $ghg^{-1}-I_3=g\,e_VE_{ij}\,g^{-1}$ are sums of such products, and
> $h^{-1}=h=I_3+\epsilon_{ee}E_{ij}$, so $x-I_3=(ghg^{-1}-h)h$ and
> $x^{-1}-I_3=h(ghg^{-1}-h)$ lie in $M_3(A_V)$.

Here `x = [g, h]` and `h = e_{ij}(e_V)`. The ring is `R = LC(Z, F_2) ⋊ Λ`, realised as
`SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ` with `e_V = 1_V u_e`. "Such products" are the
products `f u_a e_V f' u_b` of the display at tex l.284–288, taken over the terms `f u_a` of
`g_{pi}` and `f' u_b` of `(g⁻¹)_{jq}`. The context of the proof is as follows.
* `B ∋ e` (the ball `B_w`) is closed under inverses and contains the `ξ` with `u_ξ` in the entries
  of `g` and `g⁻¹`.
* `F` holds the coefficients of those entries, and `D ⊇ B·B` (the ball `B_{2w}`).
* `V` is small (`General.IsSmall D B F V`).
The size of the matrices is an arbitrary finite `ι`; the printed `3` is the case `ι = Fin 3`.

Proof route.
* `ghg⁻¹ - I = g E g⁻¹`, from `h = I + E` with `E = e_V E_{ij}`.
* Expanding `g_{pi}` and `(g⁻¹)_{jq}` into their terms gives the entry
  `(g E g⁻¹)_{pq} = g_{pi} e_V (g⁻¹)_{jq}` as a sum of products `f u_a e_V f' u_b`.
  Each product lies in `A_V` by `General.single_mul_charFn_mul_single_mem`.
* `h h = e_{ij}(e_V + e_V) = I` (characteristic 2), so `h⁻¹ = h`, and `ε_ee = e_V` gives
  `h = I + ε_ee E_{ij}`.
* `x = (ghg⁻¹) h` gives `x - I = (ghg⁻¹ - h) h`, and `x⁻¹ = h (ghg⁻¹)` gives
  `x⁻¹ - I = h (ghg⁻¹ - h)`.
* `ghg⁻¹ - h = gEg⁻¹ - E` has entries in `A_V`. Right or left multiplication by `h = I + E` adds
  a product of matrices over `A_V`, and `A_V` is closed under products
  (`General.epsilonSpan_mul_mem`, where the translates `aV`, `a ∈ B`, are disjoint because `V` is
  small).
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace Audit1

open scoped Pointwise commutatorElement

variable {Λ Z : Type*} [Group Λ] [TopologicalSpace Z] [MulAction Λ Z]
  [MulSemiringAction Λ (LocallyConstant Z (ZMod 2))] [ContinuousConstSMul Λ Z]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **tex l.289–292.** For `h = e_{ij}(e_V)` over a small clopen `V`:
* `ghg⁻¹ - I = g e_V E_{ij} g⁻¹`;
* each entry is the sum of the products `f u_a e_V f' u_b`, and each such product lies in `A_V`;
* `h⁻¹ = h = I + ε_ee E_{ij}`;
* `x - I = (ghg⁻¹ - h) h` and `x⁻¹ - I = h (ghg⁻¹ - h)` for `x = [g, h]`;
* all entries of `x - I` and `x⁻¹ - I` lie in `A_V`. -/
theorem manuscriptSentence_commutatorEntriesInTower
    (hact : ∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z))
    {D B : Finset Λ} {F : Finset (LocallyConstant Z (ZMod 2))} {V : Set Z} (hV : IsClopen V)
    (hVs : General.IsSmall D B F V) (hB1 : (1 : Λ) ∈ B) (hBinv : ∀ a ∈ B, a⁻¹ ∈ B)
    (hD : ∀ a ∈ B, ∀ b ∈ B, a * b ∈ D)
    (g : (Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ)
    (hg : ∀ p q, ∀ ξ ∈ SkewMonoidAlgebra.support
        ((g : Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) p q),
      ξ ∈ B ∧ SkewMonoidAlgebra.coeff
        ((g : Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) p q) ξ ∈ F)
    (hginv : ∀ p q, ∀ ξ ∈ SkewMonoidAlgebra.support
        (((g⁻¹ : (Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ) :
          Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) p q),
      ξ ∈ B ∧ SkewMonoidAlgebra.coeff
        (((g⁻¹ : (Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ) :
          Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) p q) ξ ∈ F)
    {i j : ι} (hij : i ≠ j) :
    -- `ghg⁻¹ - I = g e_V E_{ij} g⁻¹`
    ((g * elementaryUnit i j hij (SkewMonoidAlgebra.single (1 : Λ)
          (LocallyConstant.charFn (ZMod 2) hV)) * g⁻¹ :
        (Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ) :
        Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) - 1 =
      (g : Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) *
        Matrix.single i j (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV)) *
        ((g⁻¹ : (Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ) :
          Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) ∧
    -- the entries are sums of the products `f u_a e_V f' u_b`
    (∀ p q,
      ((g : Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) *
        Matrix.single i j (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV)) *
        ((g⁻¹ : (Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ) :
          Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))) p q =
        ∑ a ∈ SkewMonoidAlgebra.support
            ((g : Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) p i),
          ∑ b ∈ SkewMonoidAlgebra.support
            (((g⁻¹ : (Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ) :
              Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) j q),
            SkewMonoidAlgebra.single a (SkewMonoidAlgebra.coeff
                ((g : Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) p i) a) *
              SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV) *
              SkewMonoidAlgebra.single b (SkewMonoidAlgebra.coeff
                (((g⁻¹ : (Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ) :
                  Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) j q) b)) ∧
    -- each such product lies in `A_V`
    (∀ p q, ∀ a ∈ SkewMonoidAlgebra.support
        ((g : Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) p i),
      ∀ b ∈ SkewMonoidAlgebra.support
        (((g⁻¹ : (Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ) :
          Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) j q),
      SkewMonoidAlgebra.single a (SkewMonoidAlgebra.coeff
          ((g : Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) p i) a) *
        SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV) *
        SkewMonoidAlgebra.single b (SkewMonoidAlgebra.coeff
          (((g⁻¹ : (Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ) :
            Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) j q) b) ∈
        epsilonSpan (General.coeffHom Λ Z) (General.unitHom Λ Z) B hV) ∧
    -- `h⁻¹ = h`
    (elementaryUnit i j hij
        (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV)))⁻¹ =
      elementaryUnit i j hij
        (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV)) ∧
    -- `h = I + ε_ee E_{ij}`
    ((elementaryUnit i j hij
        (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV)) :
        (Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ) :
        Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) =
      1 + Matrix.single i j (epsilon (General.coeffHom Λ Z) (General.unitHom Λ Z) hV 1 1) ∧
    -- `x - I = (ghg⁻¹ - h) h`
    ((⁅g, elementaryUnit i j hij
          (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV))⁆ :
        (Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ) :
        Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) - 1 =
      (((g * elementaryUnit i j hij (SkewMonoidAlgebra.single (1 : Λ)
          (LocallyConstant.charFn (ZMod 2) hV)) * g⁻¹ :
          (Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ) :
          Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) -
        ((elementaryUnit i j hij
          (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV)) :
          (Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ) :
          Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))) *
        ((elementaryUnit i j hij
          (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV)) :
          (Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ) :
          Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) ∧
    -- `x⁻¹ - I = h (ghg⁻¹ - h)`
    ((⁅g, elementaryUnit i j hij
          (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV))⁆⁻¹ :
        (Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ) :
        Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) - 1 =
      ((elementaryUnit i j hij
          (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV)) :
          (Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ) :
          Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) *
        (((g * elementaryUnit i j hij (SkewMonoidAlgebra.single (1 : Λ)
          (LocallyConstant.charFn (ZMod 2) hV)) * g⁻¹ :
          (Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ) :
          Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) -
        ((elementaryUnit i j hij
          (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV)) :
          (Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ) :
          Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))) ∧
    -- `x - I` and `x⁻¹ - I` lie in `M_ι(A_V)`
    (∀ p q,
      (((⁅g, elementaryUnit i j hij
          (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV))⁆ :
          (Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ) :
          Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) - 1) p q ∈
        epsilonSpan (General.coeffHom Λ Z) (General.unitHom Λ Z) B hV ∧
      (((⁅g, elementaryUnit i j hij
          (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV))⁆⁻¹ :
          (Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ) :
          Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) - 1) p q ∈
        epsilonSpan (General.coeffHom Λ Z) (General.unitHom Λ Z) B hV) := by
  classical
  have hcov := General.isCovariantPair (Λ := Λ) (Z := Z) hact
  -- the translates `aV`, `a ∈ B`, are pairwise disjoint
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
  have hmul : ∀ {x y : SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ},
      x ∈ epsilonSpan (General.coeffHom Λ Z) (General.unitHom Λ Z) B hV →
        y ∈ epsilonSpan (General.coeffHom Λ Z) (General.unitHom Λ Z) B hV →
          x * y ∈ epsilonSpan (General.coeffHom Λ Z) (General.unitHom Λ Z) B hV :=
    fun hx hy => General.epsilonSpan_mul_mem hcov hV hdisj hx hy
  have he : SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV) ∈
      epsilonSpan (General.coeffHom Λ Z) (General.unitHom Λ Z) B hV :=
    General.charFn_mem_epsilonSpan hB1 hV
  have he2 : SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV) +
      SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV) = 0 := by
    rw [← two_nsmul]
    exact General.two_nsmul_eq_zero (General.coeffHom Λ Z) _
  have hee : epsilon (General.coeffHom Λ Z) (General.unitHom Λ Z) hV 1 1 =
      SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV) :=
    General.epsilon_one_one hV
  -- the terms `f u_a` of an entry
  have hsum : ∀ d : SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ,
      d = ∑ a ∈ SkewMonoidAlgebra.support d,
        SkewMonoidAlgebra.single a (SkewMonoidAlgebra.coeff d a) :=
    fun d => (SkewMonoidAlgebra.sum_single d).symm
  have hexp : ∀ c c' : SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ,
      c * SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV) * c' =
        ∑ a ∈ SkewMonoidAlgebra.support c, ∑ b ∈ SkewMonoidAlgebra.support c',
          SkewMonoidAlgebra.single a (SkewMonoidAlgebra.coeff c a) *
            SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV) *
            SkewMonoidAlgebra.single b (SkewMonoidAlgebra.coeff c' b) := by
    intro c c'
    conv_lhs => rw [hsum c, hsum c']
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
  -- name `E = e_V E_{ij}` and `h = e_{ij}(e_V)`
  obtain ⟨E, hE⟩ : ∃ E : Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ),
      E = Matrix.single i j
        (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV)) := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : (Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ,
      h = elementaryUnit i j hij
        (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV)) := ⟨_, rfl⟩
  rw [← hh, ← hE]
  have hHval : (h : Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) = 1 + E := by
    subst hh hE
    rfl
  have hhh : h * h = 1 := by
    subst hh
    rw [elementaryUnit_mul, he2, elementaryUnit_zero]
  have hinv : h⁻¹ = h := inv_eq_of_mul_eq_one_right hhh
  have hconj : ((g * h * g⁻¹ : (Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ) :
      Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) =
        1 + (g : Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) * E *
          ((g⁻¹ : (Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ) :
            Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) := by
    rw [Units.val_mul, Units.val_mul, hHval, mul_add, mul_one, add_mul, Units.mul_inv]
  have hcomm : ((⁅g, h⁆ : (Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ) :
      Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) - 1 =
        (((g * h * g⁻¹ : (Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ) :
          Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) -
          (h : Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))) *
          (h : Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) := by
    rw [commutatorElement_def, hinv, Units.val_mul (g * h * g⁻¹) h, sub_mul, ← Units.val_mul h h,
      hhh, Units.val_one]
  have hassoc : h * g * h * g⁻¹ = h * (g * h * g⁻¹) := by
    simp only [mul_assoc]
  have hcomm' : ((⁅g, h⁆⁻¹ : (Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ) :
      Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) - 1 =
        (h : Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) *
          (((g * h * g⁻¹ : (Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ) :
            Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) -
            (h : Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))) := by
    rw [commutatorElement_inv, commutatorElement_def, hinv, hassoc, Units.val_mul h, mul_sub,
      ← Units.val_mul h h, hhh, Units.val_one]
  -- the entries of `E` and of `g E g⁻¹` lie in `A_V`
  have hEent : ∀ p q, E p q ∈ epsilonSpan (General.coeffHom Λ Z) (General.unitHom Λ Z) B hV := by
    intro p q
    rw [hE, Matrix.single_apply]
    split_ifs
    · exact he
    · exact AddSubgroup.zero_mem _
  have hGE : ∀ p q,
      ((g : Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) * E *
        ((g⁻¹ : (Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ) :
          Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))) p q ∈
        epsilonSpan (General.coeffHom Λ Z) (General.unitHom Λ Z) B hV := by
    intro p q
    rw [hE, General.mul_single_mul_apply]
    refine General.mul_charFn_mul_mem hact hV
      (fun a ha => ⟨(hg p i a ha).1, fun x hx y hy =>
        hVs.2 _ (hg p i a ha).2 a (hg p i a ha).1 x hx y hy⟩)
      (fun b hb => ⟨hBinv b (hginv j q b hb).1, fun x hx y hy => ?_⟩)
    have hc := hVs.2 _ (hginv j q b hb).2 1 hB1 x hx y hy
    rwa [one_smul, one_smul] at hc
  have hmulM : ∀ A A' : Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ),
      (∀ p q, A p q ∈ epsilonSpan (General.coeffHom Λ Z) (General.unitHom Λ Z) B hV) →
      (∀ p q, A' p q ∈ epsilonSpan (General.coeffHom Λ Z) (General.unitHom Λ Z) B hV) →
      ∀ p q, (A * A') p q ∈ epsilonSpan (General.coeffHom Λ Z) (General.unitHom Λ Z) B hV := by
    intro A A' hA hA' p q
    rw [Matrix.mul_apply]
    exact _root_.sum_mem fun r _ => hmul (hA p r) (hA' r q)
  have hright : ∀ A : Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ),
      (∀ p q, A p q ∈ epsilonSpan (General.coeffHom Λ Z) (General.unitHom Λ Z) B hV) →
      ∀ p q, (A * (h : Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))) p q ∈
        epsilonSpan (General.coeffHom Λ Z) (General.unitHom Λ Z) B hV := by
    intro A hA p q
    rw [hHval, mul_add, mul_one, Matrix.add_apply]
    exact _root_.add_mem (hA p q) (hmulM A E hA hEent p q)
  have hleft : ∀ A : Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ),
      (∀ p q, A p q ∈ epsilonSpan (General.coeffHom Λ Z) (General.unitHom Λ Z) B hV) →
      ∀ p q, ((h : Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) * A) p q ∈
        epsilonSpan (General.coeffHom Λ Z) (General.unitHom Λ Z) B hV := by
    intro A hA p q
    rw [hHval, add_mul, one_mul, Matrix.add_apply]
    exact _root_.add_mem (hA p q) (hmulM E A hEent hA p q)
  -- `ghg⁻¹ - h = g E g⁻¹ - E`
  have hXH : ((g * h * g⁻¹ : (Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ) :
      Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) -
        (h : Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) =
      (g : Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) * E *
          ((g⁻¹ : (Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ) :
            Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) - E := by
    rw [hconj, hHval, add_sub_add_left_eq_sub]
  have hM : ∀ p q,
      (((g * h * g⁻¹ : (Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ) :
        Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) -
        (h : Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))) p q ∈
        epsilonSpan (General.coeffHom Λ Z) (General.unitHom Λ Z) B hV := by
    intro p q
    rw [hXH, Matrix.sub_apply]
    exact AddSubgroup.sub_mem _ (hGE p q) (hEent p q)
  refine ⟨?_, fun p q => ?_, fun p q a ha b hb => ?_, hinv, ?_, hcomm, hcomm', fun p q => ⟨?_, ?_⟩⟩
  · rw [hconj, add_sub_cancel_left]
  · rw [hE, General.mul_single_mul_apply]
    exact hexp _ _
  · have hc := hVs.2 _ (hginv j q b hb).2 1 hB1
    exact General.single_mul_charFn_mul_single_mem hact hV (hg p i a ha).1
      (hBinv b (hginv j q b hb).1)
      (fun x hx y hy => hVs.2 _ (hg p i a ha).2 a (hg p i a ha).1 x hx y hy)
      (fun x hx y hy => by
        have hxy := hc x hx y hy
        rwa [one_smul, one_smul] at hxy)
  · rw [hHval, hE, hee]
  · rw [hcomm]
    exact hright _ hM p q
  · rw [hcomm']
    exact hleft _ hM p q

#audit_axioms GroupApproximation.SimpleKazhdanSofic.Audit1.manuscriptSentence_commutatorEntriesInTower

end Audit1
end SimpleKazhdanSofic
end GroupApproximation
