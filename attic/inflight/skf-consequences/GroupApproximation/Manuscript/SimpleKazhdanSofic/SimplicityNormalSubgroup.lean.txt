import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimplicityStatement
import GroupApproximation.Manuscript.SimpleKazhdanSofic.TowerCopyGroup
import GroupApproximation.Pestov91.SimpleModCentre
import GroupApproximation.Pestov91.RingSimple

/-!
# Simplicity through one finite simple subgroup: from the commutator witness to `K = G`

`simple_kazhdan_sofic_group.tex` (origin/main tip), subsection "Simplicity":

> The image $\psi(M_d(\F_2))$ is the set of matrices with entries in the span of the
> $\epsilon_{ab}$, and it is closed under products. … say $k=I_3+\psi(M)$ and $k^{-1}=I_3+\psi(M')$.
> As $\psi$ is injective and multiplicative, $(I_d+M)(I_d+M')=I_d$, so $k$ is the image of $I_d+M$
> and $k\in H$. Then $K\cap H$ is a nontrivial normal subgroup of $H\cong\GL_d(\F_2)=\PSL_d(\F_2)$,
> which is simple as $d\ge3$. So $H\subseteq K$, and $e_{pq}(e_V)\in K$ for all $p\ne q$.
> Finally, $J=\{r\in R:e_{pq}(r)\in K\text{ for all }p\ne q\}$ is a two-sided ideal. … It contains
> $e_V$, so it contains every $e_{T^aV}=u^ae_Vu^{-a}$. By minimality and compactness finitely many
> of these sets cover $X$, so $1=1-\prod_i(1-e_{T^{a_i}V})\in J$. So $J=R$ and $K=G$.

The printed proof is for `EL_3`; `thm:main` covers `EL_n`, `n ≥ 3`, and the argument is the same, so
everything here is over `Fin n`.

* `mem_range_towerHom_of_mem_towerSpanOf`: the `ε`-span lies in the range of `ψ`;
* `exists_towerCopy_eq`: `k ∈ H`;
* `towerE_centre`: `ε_{00} = e_V`;
* `one_sub_map_prod_one_sub_mem`, `prod_one_sub_charFn_eq_zero`, `one_mem_levelIdeal_of_cover`:
  `1 = 1 - ∏ᵢ(1 - e_{T^{aᵢ}V}) ∈ J` (the product is taken in the commutative ring `LC(X, F_2)`);
* `exists_finset_cover_zpow_image`: minimality and compactness give the finite cover;
* `eq_top_of_simplicityCommutatorWitness`: `K = G`;
* the closed endpoint `printedSimplicityThroughFiniteSimpleSubgroup`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

open ClopenCrossedProduct ChainRadical Pestov91.SimpleModCentre

variable {X : Type*} [TopologicalSpace X] {T : X ≃ₜ X}

section Copy

variable {w : ℕ} {V : Set X} (hlev : LevelsDisjoint T w V) (hV : IsClopen V)

/-- **The `ε`-span lies in the range of `ψ`.** -/
theorem mem_range_towerHom_of_mem_towerSpanOf {x : ClopenCrossedProduct T (ZMod 2)}
    (hx : x ∈ towerSpanOf T (ZMod 2) w hV) :
    ∃ A : Matrix (Fin (2 * w + 1)) (Fin (2 * w + 1)) (ZMod 2),
      towerHom hlev subset_rfl hV A = x := by
  have hle : towerSpanOf T (ZMod 2) w hV ≤ AddMonoidHom.range (towerAddHom (T := T) (m := w) hV) := by
    unfold towerSpanOf
    refine (AddSubgroup.closure_le (K := _)).2 ?_
    rintro _ ⟨⟨a, b⟩, rfl⟩
    exact AddMonoidHom.mem_range.2 ⟨Matrix.single a b 1, towerHom_single hlev subset_rfl hV a b⟩
  obtain ⟨A, hA⟩ := AddMonoidHom.mem_range.1 (hle hx)
  exact ⟨A, hA⟩

/-- **`k ∈ H`**: a unit whose deviations `k - I` and `k⁻¹ - I` have entries in the `ε`-span is the
image of `I_d + M` under the tower copy. -/
theorem exists_towerCopy_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (hne : V.Nonempty)
    (g : (Matrix ι ι (ClopenCrossedProduct T (ZMod 2)))ˣ)
    (hg : ∀ p q, ((g : Matrix ι ι (ClopenCrossedProduct T (ZMod 2))) - 1) p q ∈
      towerSpanOf T (ZMod 2) w hV)
    (hginv : ∀ p q, (((g⁻¹ : (Matrix ι ι (ClopenCrossedProduct T (ZMod 2)))ˣ) :
      Matrix ι ι (ClopenCrossedProduct T (ZMod 2))) - 1) p q ∈ towerSpanOf T (ZMod 2) w hV) :
    ∃ x, towerCopy ι hlev subset_rfl hV x = g := by
  choose A hA using fun p q => mem_range_towerHom_of_mem_towerSpanOf hlev hV (hg p q)
  choose B hB using fun p q => mem_range_towerHom_of_mem_towerSpanOf hlev hV (hginv p q)
  have hgA : (g : Matrix ι ι (ClopenCrossedProduct T (ZMod 2))) =
      1 + (Matrix.of A).map (towerHom hlev subset_rfl hV) := by
    ext p q
    rw [Matrix.add_apply, Matrix.map_apply, Matrix.of_apply, hA p q, Matrix.sub_apply]
    abel
  have hgB : ((g⁻¹ : (Matrix ι ι (ClopenCrossedProduct T (ZMod 2)))ˣ) :
      Matrix ι ι (ClopenCrossedProduct T (ZMod 2))) =
        1 + (Matrix.of B).map (towerHom hlev subset_rfl hV) := by
    ext p q
    rw [Matrix.add_apply, Matrix.map_apply, Matrix.of_apply, hB p q, Matrix.sub_apply]
    abel
  have hφ := towerHom_injective hlev subset_rfl hV hne
  have key : ∀ M N : Matrix ι ι (Matrix (Fin (2 * w + 1)) (Fin (2 * w + 1)) (ZMod 2)),
      (1 + M.map (towerHom hlev subset_rfl hV)) * (1 + N.map (towerHom hlev subset_rfl hV)) = 1 →
        (1 + M) * (1 + N) = 1 := by
    intro M N h
    have e : (1 + M.map (towerHom hlev subset_rfl hV)) * (1 + N.map (towerHom hlev subset_rfl hV)) =
        1 + (M.map (towerHom hlev subset_rfl hV) + N.map (towerHom hlev subset_rfl hV) +
          M.map (towerHom hlev subset_rfl hV) * N.map (towerHom hlev subset_rfl hV)) := by
      simp only [add_mul, mul_add, one_mul, mul_one]
      abel
    rw [e] at h
    have h0 : M.map (towerHom hlev subset_rfl hV) + N.map (towerHom hlev subset_rfl hV) +
        M.map (towerHom hlev subset_rfl hV) * N.map (towerHom hlev subset_rfl hV) = 0 := by
      calc _ = (1 + (M.map (towerHom hlev subset_rfl hV) + N.map (towerHom hlev subset_rfl hV) +
            M.map (towerHom hlev subset_rfl hV) * N.map (towerHom hlev subset_rfl hV))) - 1 := by
            abel
        _ = 0 := by rw [h, sub_self]
    have h1 : (M + N + M * N).map (towerHom hlev subset_rfl hV) =
        (0 : Matrix ι ι (Matrix (Fin (2 * w + 1)) (Fin (2 * w + 1)) (ZMod 2))).map
          (towerHom hlev subset_rfl hV) := by
      rw [Matrix.map_add _ (map_add (towerHom hlev subset_rfl hV)),
        Matrix.map_add _ (map_add (towerHom hlev subset_rfl hV)),
        ← map_mul_map (towerHom hlev subset_rfl hV), h0,
        Matrix.map_zero _ (map_zero (towerHom hlev subset_rfl hV))]
    have h3 : M + N + M * N = 0 := Matrix.map_injective hφ h1
    have e2 : (1 + M) * (1 + N) = 1 + (M + N + M * N) := by
      simp only [add_mul, mul_add, one_mul, mul_one]
      abel
    rw [e2, h3, add_zero]
  have hAB : (1 + Matrix.of A) * (1 + Matrix.of B) = 1 :=
    key _ _ (by rw [← hgA, ← hgB, Units.mul_inv])
  have hBA : (1 + Matrix.of B) * (1 + Matrix.of A) = 1 :=
    key _ _ (by rw [← hgA, ← hgB, Units.inv_mul])
  refine ⟨(flatEquiv ι w).symm ⟨1 + Matrix.of A, 1 + Matrix.of B, hAB, hBA⟩, ?_⟩
  apply Units.ext
  rw [towerCopy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  change cornerMatrixHom (towerHom hlev subset_rfl hV) (1 + Matrix.of A) =
    (g : Matrix ι ι (ClopenCrossedProduct T (ZMod 2)))
  rw [cornerMatrixHom_one_add, hgA]

end Copy

/-- `ε_{aa} = e_{T^aV}`. -/
theorem towerE_self (w : ℕ) {V : Set X} (hV : IsClopen V) (a : Fin (2 * w + 1)) :
    towerE T (ZMod 2) w hV a a =
      coeff T (ZMod 2) (LocallyConstant.charFn (ZMod 2) (isClopen_image (T ^ (((a : ℕ) : ℤ) - w)) hV)) := by
  unfold towerE
  rw [sub_self, zpow_zero, Units.val_one, mul_one]

/-- `ε_{00} = e_V`. -/
theorem towerE_centre (w : ℕ) {V : Set X} (hV : IsClopen V) :
    towerE T (ZMod 2) w hV ⟨w, by omega⟩ ⟨w, by omega⟩ =
      coeff T (ZMod 2) (LocallyConstant.charFn (ZMod 2) hV) := by
  rw [towerE_self]
  congr 1
  refine charFn_congr _ _ ?_
  have h0 : ((((⟨w, by omega⟩ : Fin (2 * w + 1)) : ℕ) : ℤ) - (w : ℤ)) = 0 := by simp
  rw [h0, zpow_zero]
  ext x
  exact ⟨fun ⟨y, hy, e⟩ => e ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

/-- `1 - f(∏ᵢ (1 - eᵢ)) ∈ I` when every `f(eᵢ) ∈ I`, for a ring hom `f` from a commutative ring. -/
theorem one_sub_map_prod_one_sub_mem {A S ι : Type*} [CommRing A] [Ring S] (f : A →+* S)
    (I : TwoSidedIdeal S) (s : Finset ι) (e : ι → A) (he : ∀ i ∈ s, f (e i) ∈ I) :
    1 - f (∏ i ∈ s, (1 - e i)) ∈ I := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, map_mul, map_sub, map_one]
    have h : 1 - (1 - f (e i)) * f (∏ j ∈ s, (1 - e j)) =
        (1 - f (∏ j ∈ s, (1 - e j))) + f (e i) * f (∏ j ∈ s, (1 - e j)) := by
      noncomm_ring
    rw [h]
    exact I.add_mem (ih fun j hj => he j (Finset.mem_insert_of_mem hj))
      (I.mul_mem_right _ _ (he i (Finset.mem_insert_self i s)))

/-- `u^a e_V u^{-a} = e_{T^aV}`. -/
theorem unit_zpow_mul_charFn_mul_inv (a : ℤ) {V : Set X} (hV : IsClopen V) :
    ((unit T (ZMod 2) ^ a : (ClopenCrossedProduct T (ZMod 2))ˣ) : ClopenCrossedProduct T (ZMod 2)) *
        coeff T (ZMod 2) (LocallyConstant.charFn (ZMod 2) hV) *
        (((unit T (ZMod 2) ^ a)⁻¹ : (ClopenCrossedProduct T (ZMod 2))ˣ) :
          ClopenCrossedProduct T (ZMod 2)) =
      coeff T (ZMod 2) (LocallyConstant.charFn (ZMod 2) (isClopen_image (T ^ a) hV)) := by
  rw [unit_zpow_mul_charFn, mul_assoc, Units.mul_inv, mul_one]

/-- For a finite cover `X = ⋃_{a ∈ s} T^a V`: `∏_{a ∈ s} (1 - 1_{T^aV}) = 0` in `LC(X, F_2)`. -/
theorem prod_one_sub_charFn_eq_zero {V : Set X} (hV : IsClopen V) (s : Finset ℤ)
    (hs : ∀ x : X, ∃ a ∈ s, x ∈ ⇑(T ^ a) '' V) :
    ∏ a ∈ s, (1 - LocallyConstant.charFn (ZMod 2) (isClopen_image (T ^ a) hV)) = 0 := by
  ext x
  obtain ⟨a, ha, hx⟩ := hs x
  have hc : ∀ f : LocallyConstant X (ZMod 2),
      (f : X → ZMod 2) = LocallyConstant.coeFnMonoidHom f := fun _ => rfl
  rw [LocallyConstant.zero_apply, hc, map_prod, Finset.prod_apply]
  refine Finset.prod_eq_zero ha ?_
  rw [← hc, LocallyConstant.sub_apply, LocallyConstant.one_apply, LocallyConstant.coe_charFn,
    Set.indicator_of_mem hx, Pi.one_apply, sub_self]

/-- **`1 ∈ J`**: the level ideal containing `e_V` contains every `e_{T^aV}`, and a finite cover gives
`1 = 1 - ∏ᵢ(1 - e_{T^{aᵢ}V})`. -/
theorem one_mem_levelIdeal_of_cover {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : 3 ≤ Fintype.card ι) {V : Set X} (hV : IsClopen V) (s : Finset ℤ)
    (hs : ∀ x : X, ∃ a ∈ s, x ∈ ⇑(T ^ a) '' V)
    (N : Subgroup (elementaryGroup ι (ClopenCrossedProduct T (ZMod 2)))) [N.Normal]
    (hmem : coeff T (ZMod 2) (LocallyConstant.charFn (ZMod 2) hV) ∈ levelIdeal hcard N) :
    (1 : ClopenCrossedProduct T (ZMod 2)) ∈ levelIdeal hcard N := by
  have htrans : ∀ a ∈ s,
      coeff T (ZMod 2) (LocallyConstant.charFn (ZMod 2) (isClopen_image (T ^ a) hV)) ∈
        levelIdeal hcard N := fun a _ => by
    rw [← unit_zpow_mul_charFn_mul_inv a hV]
    exact TwoSidedIdeal.mul_mem_right _ _ _ (TwoSidedIdeal.mul_mem_left _ _ _ hmem)
  have h := one_sub_map_prod_one_sub_mem (coeff T (ZMod 2)) (levelIdeal hcard N) s _ htrans
  rwa [prod_one_sub_charFn_eq_zero hV s hs, map_zero, sub_zero] at h

/-- **Minimality and compactness**: finitely many translates `T^a V` of a nonempty open set cover
`X`. -/
theorem exists_finset_cover_zpow_image [CompactSpace X]
    (hmin : ∀ x : X, Dense (Set.range fun j : ℤ => (T ^ j) x)) {V : Set X} (hV : IsOpen V)
    (hne : V.Nonempty) : ∃ s : Finset ℤ, ∀ x : X, ∃ a ∈ s, x ∈ ⇑(T ^ a) '' V := by
  obtain ⟨s, hs⟩ := Pestov91.exists_finset_cover_of_dense_orbits (fun j => ⇑(T ^ j))
    (fun j => (T ^ j).continuous) hmin hV hne
  refine ⟨s.image Neg.neg, fun x => ?_⟩
  obtain ⟨i, hi, hx⟩ := hs x
  refine ⟨-i, Finset.mem_image_of_mem _ hi, (T ^ i) x, hx, ?_⟩
  rw [← Homeomorph.mul_apply, ← zpow_add, neg_add_cancel, zpow_zero, Homeomorph.one_apply]

/-- **`K = G`** from the commutator witness and the finite covering property of nonempty clopen
sets. -/
theorem eq_top_of_simplicityCommutatorWitness {n : ℕ} (hn : 3 ≤ n)
    (hw : SimplicityCommutatorWitness T n)
    (hcover : ∀ V : Set X, IsClopen V → V.Nonempty →
      ∃ s : Finset ℤ, ∀ x : X, ∃ a ∈ s, x ∈ ⇑(T ^ a) '' V)
    (N : Subgroup (elementaryGroup (Fin n) (ClopenCrossedProduct T (ZMod 2)))) (hN : N.Normal)
    (hne : N ≠ ⊥) : N = ⊤ := by
  haveI := hN
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  have hcard : 3 ≤ Fintype.card (Fin n) := by rw [Fintype.card_fin]; exact hn
  obtain ⟨V, hV, w, g, hVne, hlev, hgN, hg1, hent⟩ := hw N hN hne
  obtain ⟨x, hx⟩ := exists_towerCopy_eq hlev hV hVne
    (g : (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ)
    (fun p q => (hent p q).1) (fun p q => (hent p q).2)
  let H : (Matrix (Fin n × Fin (2 * w + 1)) (Fin n × Fin (2 * w + 1)) (ZMod 2))ˣ →*
      elementaryGroup (Fin n) (ClopenCrossedProduct T (ZMod 2)) :=
    (towerCopy (Fin n) hlev subset_rfl hV).codRestrict _
      (towerCopy_mem_elementaryGroup hlev subset_rfl hV)
  have hHx : H x = g := Subtype.ext hx
  have hcardd : 3 ≤ Fintype.card (Fin n × Fin (2 * w + 1)) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    calc 3 ≤ n := hn
      _ ≤ n * (2 * w + 1) := by nlinarith
  haveI := FinitaryLinear.isSimpleGroup_units_matrix_zmodTwo (Fin n × Fin (2 * w + 1)) hcardd
  have hxN : x ∈ N.comap H := by
    rw [Subgroup.mem_comap, hHx]
    exact hgN
  have hx1 : x ≠ 1 := fun h => hg1 (by rw [← hHx, h, map_one])
  have htop : N.comap H = ⊤ :=
    (hN.comap H).eq_bot_or_eq_top.resolve_left fun hb => hx1 (Subgroup.mem_bot.1 (hb ▸ hxN))
  have hroot : ∀ (p q : Fin n) (hpq : p ≠ q),
      elGen p q hpq (coeff T (ZMod 2) (LocallyConstant.charFn (ZMod 2) hV)) ∈ N := by
    intro p q hpq
    have hne' : ((p, ⟨w, by omega⟩) : Fin n × Fin (2 * w + 1)) ≠ (q, ⟨w, by omega⟩) := by
      simp [hpq]
    have hmem : elementaryUnit _ _ hne' (1 : ZMod 2) ∈ N.comap H := by
      rw [htop]
      exact Subgroup.mem_top _
    have hH : H (elementaryUnit _ _ hne' (1 : ZMod 2)) =
        elGen p q hpq (coeff T (ZMod 2) (LocallyConstant.charFn (ZMod 2) hV)) := by
      apply Subtype.ext
      change towerCopy (Fin n) hlev subset_rfl hV (elementaryUnit _ _ hne' (1 : ZMod 2)) =
        elementaryUnit p q hpq _
      rw [towerCopy_transvection hlev subset_rfl hV hpq _ _ hne', towerE_centre]
    rw [← hH]
    exact hmem
  have hmemJ : coeff T (ZMod 2) (LocallyConstant.charFn (ZMod 2) hV) ∈ levelIdeal hcard N :=
    (mem_levelIdeal hcard N _).2 hroot
  obtain ⟨s, hs⟩ := hcover V hV hVne
  have h1 := one_mem_levelIdeal_of_cover hcard hV s hs N hmemJ
  rw [Subgroup.eq_top_iff']
  intro y
  have hy := elementaryGroup_hom_eq_one_of_gens (QuotientGroup.mk' N)
    (fun l k hlk d => by
      have hd := TwoSidedIdeal.mul_mem_left _ d 1 h1
      rw [mul_one] at hd
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact (mem_levelIdeal hcard N d).mp hd l k hlk) y
  rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy

/-- **Printed simplicity through one finite simple subgroup**, for `EL_n`, `n ≥ 3`, over a compact
space with dense orbits, from the commutator witness produced by the first half of the proof. -/
def PrintedSimplicityThroughFiniteSimpleSubgroup : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] (T : X ≃ₜ X),
    (∀ x : X, Dense (Set.range fun j : ℤ => (T ^ j) x)) →
    ∀ n : ℕ, 3 ≤ n → SimplicityCommutatorWitness T n →
    ∀ N : Subgroup (elementaryGroup (Fin n) (ClopenCrossedProduct T (ZMod 2))), N.Normal → N ≠ ⊥ →
      N = ⊤

theorem printedSimplicityThroughFiniteSimpleSubgroup :
    PrintedSimplicityThroughFiniteSimpleSubgroup :=
  fun _ _ _ _ hmin _ hn hw N hN hne => eq_top_of_simplicityCommutatorWitness hn hw
    (fun _ hV hne' => exists_finset_cover_zpow_image hmin hV.isOpen hne') N hN hne

/-- **`EL_n(R_X)` is simple** for `n ≥ 3`, over a nonempty compact space with dense orbits, from the
commutator witness: it is nontrivial, and every nontrivial normal subgroup is everything. -/
theorem isSimpleGroup_elementaryGroup_of_simplicityCommutatorWitness [CompactSpace X] [Nonempty X]
    (hmin : ∀ x : X, Dense (Set.range fun j : ℤ => (T ^ j) x)) {n : ℕ} (hn : 3 ≤ n)
    (hw : SimplicityCommutatorWitness T n) :
    IsSimpleGroup ↥(elementaryGroup (Fin n) (ClopenCrossedProduct T (ZMod 2))) := by
  haveI : Nontrivial (ZMod 2) := nontrivial_of_ne (0 : ZMod 2) 1 (by decide)
  haveI : Nontrivial (LocallyConstant X (ZMod 2)) :=
    nontrivial_of_ne 0 1 fun h => by simpa using DFunLike.congr_fun h (Classical.arbitrary X)
  haveI : Nontrivial (ClopenCoeff T (ZMod 2)) :=
    inferInstanceAs (Nontrivial (LocallyConstant X (ZMod 2)))
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hne1 : elGen (R := ClopenCrossedProduct T (ZMod 2)) _ _ h01 1 ≠ 1 := by
    intro h
    have h' : elementaryUnit (R := ClopenCrossedProduct T (ZMod 2)) _ _ h01 1 =
        elementaryUnit _ _ h01 0 := by
      rw [elementaryUnit_zero]
      exact congrArg Subtype.val h
    exact one_ne_zero (elementaryUnit_injective _ _ h01 h')
  haveI : Nontrivial ↥(elementaryGroup (Fin n) (ClopenCrossedProduct T (ZMod 2))) :=
    nontrivial_of_ne _ _ hne1
  refine ⟨fun N hN => ?_⟩
  by_cases hb : N = ⊥
  · exact Or.inl hb
  · exact Or.inr (eq_top_of_simplicityCommutatorWitness hn hw
      (fun _ hV hne' => exists_finset_cover_zpow_image hmin hV.isOpen hne') N hN hb)

/-- **Printed simplicity, group form**: `EL_n(R_X)` is a simple group for `n ≥ 3`, over a nonempty
compact space with dense orbits, from the commutator witness of the first half of the proof. -/
def PrintedSimplicityIsSimpleGroup : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [Nonempty X] (T : X ≃ₜ X),
    (∀ x : X, Dense (Set.range fun j : ℤ => (T ^ j) x)) →
    ∀ n : ℕ, 3 ≤ n → SimplicityCommutatorWitness T n →
      IsSimpleGroup ↥(elementaryGroup (Fin n) (ClopenCrossedProduct T (ZMod 2)))

theorem printedSimplicityIsSimpleGroup : PrintedSimplicityIsSimpleGroup :=
  fun _ _ _ _ _ hmin _ hn hw => isSimpleGroup_elementaryGroup_of_simplicityCommutatorWitness hmin hn hw

#audit_axioms GroupApproximation.SimpleKazhdanSofic.isSimpleGroup_elementaryGroup_of_simplicityCommutatorWitness
#audit_axioms GroupApproximation.SimpleKazhdanSofic.printedSimplicityIsSimpleGroup
#audit_axioms GroupApproximation.SimpleKazhdanSofic.exists_towerCopy_eq
#audit_axioms GroupApproximation.SimpleKazhdanSofic.one_mem_levelIdeal_of_cover
#audit_axioms GroupApproximation.SimpleKazhdanSofic.eq_top_of_simplicityCommutatorWitness
#audit_axioms GroupApproximation.SimpleKazhdanSofic.printedSimplicityThroughFiniteSimpleSubgroup

end SimpleKazhdanSofic
end GroupApproximation
