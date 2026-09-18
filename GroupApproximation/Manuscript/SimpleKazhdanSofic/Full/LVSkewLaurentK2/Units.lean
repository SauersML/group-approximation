import GroupApproximation.Leavitt.ElementaryGroup
import GroupApproximation.Algebra.FinitaryLinearBinarySimple
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVSkewLaurentK2.Interface

/-!
# `K₁ = 0` for ultramatricial `𝔽₂`-rings (lane LVSkewLaurentK2-3c)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii; work order
WO-LVCohnK2-3.  In the degree-two Yao sequence of Ara–Brustenga–Cortiñas (Münster J. Math. 2
(2009), `thm:skewyao`, Steps 1-2, `yaoseq6.tex` l.574-640)
`K₂(S) ⊕ K₂(S) → K₂(S[t₊,φ]) ⊕ K₂(S[t₋,φ]) → K₂(S[t,t⁻¹;φ]) → K₁(S) ⊕ K₁(S)`
the `K₁` input for an ultramatricial ring `S` over `𝔽₂` is `K₁(S) = 0`.  This file proves the
unstable, finite-rank form of that vanishing: every invertible `ι × ι` matrix over `S` with
`#ι ≥ 2` lies in the elementary group `EL_ι(S)`.

* `units_mem_elementaryGroup_matrix_zmodTwo`: blocks `M_d(𝔽₂)`, via `EL_ι(M_d(R)) ≅ EL_{ι×d}(R)`
  and `GL_N(𝔽₂) = EL_N(𝔽₂)`;
* `units_mem_elementaryGroup_pi`: finite products of rings;
* `units_mem_elementaryGroup_of_ringEquiv`: ring isomorphisms;
* `units_mem_elementaryGroup_of_subrings`: directed unions of subrings;
* `units_mem_elementaryGroup_of_ultramatricial`: the assembly, under the ultramatricial
  hypothesis of WO-LVCohnK2-3;
* `k1Statement_of_ultramatricial`: the lane-3c statement of `Interface.lean`.
-/

namespace GroupApproximation.Full.LVSkewLaurentK2

open GroupApproximation

/-- The underlying matrix of the elementary unit `x_{ij}(a)`. -/
theorem elementaryUnit_val {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]
    (i j : ι) (h : i ≠ j) (a : R) :
    ((elementaryUnit i j h a : (Matrix ι ι R)ˣ) : Matrix ι ι R) = 1 + Matrix.single i j a :=
  rfl

/-! ### Matrix blocks over `𝔽₂` -/

/-- Every invertible `ι × ι` matrix over `M_d(𝔽₂)` is elementary when `#ι ≥ 2`: flatten to
`GL_{ι×d}(𝔽₂) = EL_{ι×d}(𝔽₂)` and use `EL_ι(M_d(𝔽₂)) ≅ EL_{ι×d}(𝔽₂)`.
(ABC 2009, `K₁` of ultramatricial algebras; `simple_kazhdan_sofic_group.tex` l.733-735.) -/
theorem units_mem_elementaryGroup_matrix_zmodTwo {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nontrivial ι] (d : ℕ) (g : (Matrix ι ι (Matrix (Fin d) (Fin d) (ZMod 2)))ˣ) :
    g ∈ elementaryGroup ι (Matrix (Fin d) (Fin d) (ZMod 2)) := by
  have hmem : elementaryBlockUnitEquiv (ι := ι) (κ := Fin d) (R := ZMod 2) g ∈
      elementaryGroup (ι × Fin d) (ZMod 2) := by
    rw [FinitaryLinear.elementaryGroup_zmodTwo_eq_top (ι × Fin d)]
    exact Subgroup.mem_top _
  rw [← elementaryBlockGroup_map (ι := ι) (κ := Fin d) (R := ZMod 2)] at hmem
  have hsymm := Subgroup.mem_map_equiv.mp hmem
  rwa [MulEquiv.symm_apply_apply] at hsymm

/-! ### Finite products -/

/-- Units of matrices over a product ring, coordinatewise. -/
def piMatrixUnitsEquiv {J : Type*} {A : J → Type*} [∀ j, Ring (A j)] {ι : Type*} [Fintype ι]
    [DecidableEq ι] :
    (Matrix ι ι (Π j, A j))ˣ ≃* Π j, (Matrix ι ι (A j))ˣ :=
  (Units.mapEquiv (Matrix.piRingEquiv (β := A) (n := ι)).toMulEquiv).trans
    (MulEquiv.piUnits (M := fun j => Matrix ι ι (A j)))

theorem piMatrixUnitsEquiv_apply_val {J : Type*} {A : J → Type*} [∀ j, Ring (A j)] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (g : (Matrix ι ι (Π j, A j))ˣ) (j : J) (k l : ι) :
    ((piMatrixUnitsEquiv g j : (Matrix ι ι (A j))ˣ) : Matrix ι ι (A j)) k l =
      (g : Matrix ι ι (Π j, A j)) k l j :=
  rfl

/-- The `j`-th coordinate of an elementary unit over a product ring is the elementary unit with
the `j`-th coordinate of the coefficient. -/
theorem piMatrixUnitsEquiv_elementaryUnit {J : Type*} {A : J → Type*} [∀ j, Ring (A j)]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (k l : ι) (hkl : k ≠ l) (x : Π j, A j) (j : J) :
    piMatrixUnitsEquiv (elementaryUnit k l hkl x) j = elementaryUnit k l hkl (x j) := by
  have h := elementaryMatrixUnitMap_elementaryUnit (ι := ι) (Pi.evalRingHom A j) k l hkl x
  apply Units.ext
  ext k' l'
  exact congrArg (fun z : (Matrix ι ι (A j))ˣ => (z : Matrix ι ι (A j)) k' l') h

/-- The elementary unit with coefficient supported in one coordinate is the elementary unit of
that coordinate, and `1` in the others. -/
theorem piMatrixUnitsEquiv_elementaryUnit_single {J : Type*} [DecidableEq J] {A : J → Type*}
    [∀ j, Ring (A j)] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k l : ι) (hkl : k ≠ l) (j : J) (a : A j) :
    piMatrixUnitsEquiv (elementaryUnit k l hkl (Pi.single j a : Π j, A j)) =
      Pi.mulSingle j (elementaryUnit k l hkl a) := by
  funext j'
  rw [piMatrixUnitsEquiv_elementaryUnit]
  by_cases hj : j' = j
  · subst hj
    rw [Pi.single_eq_same, Pi.mulSingle_eq_same]
  · rw [Pi.single_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj]
    exact elementaryUnit_zero k l hkl

/-- If every invertible matrix over each factor is elementary, so is every invertible matrix over
the finite product.  (ABC 2009, `K₁` of ultramatricial algebras;
`simple_kazhdan_sofic_group.tex` l.733-735.) -/
theorem units_mem_elementaryGroup_pi {J : Type*} [Fintype J] [DecidableEq J] {A : J → Type*}
    [∀ j, Ring (A j)] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hA : ∀ (j : J) (h : (Matrix ι ι (A j))ˣ), h ∈ elementaryGroup ι (A j))
    (g : (Matrix ι ι (Π j, A j))ˣ) : g ∈ elementaryGroup ι (Π j, A j) := by
  have hΦ : piMatrixUnitsEquiv (ι := ι) (A := A) g ∈
      (elementaryGroup ι (Π j, A j)).map (piMatrixUnitsEquiv (ι := ι) (A := A)).toMonoidHom := by
    refine Subgroup.pi_mem_of_mulSingle_mem _ fun j => ?_
    have hle : elementaryGroup ι (A j) ≤
        ((elementaryGroup ι (Π j, A j)).map
          (piMatrixUnitsEquiv (ι := ι) (A := A)).toMonoidHom).comap
          (MonoidHom.mulSingle (fun j => (Matrix ι ι (A j))ˣ) j) := by
      refine Subgroup.closure_le.mpr ?_
      rintro _ ⟨k, l, hkl, a, rfl⟩
      show (Pi.mulSingle j (elementaryUnit k l hkl a) : Π j, (Matrix ι ι (A j))ˣ) ∈
        (elementaryGroup ι (Π j, A j)).map (piMatrixUnitsEquiv (ι := ι) (A := A)).toMonoidHom
      exact Subgroup.mem_map.mpr ⟨elementaryUnit k l hkl (Pi.single j a : Π j, A j),
        elementaryUnit_mem k l hkl _, piMatrixUnitsEquiv_elementaryUnit_single k l hkl j a⟩
    exact hle (hA j (piMatrixUnitsEquiv (ι := ι) (A := A) g j))
  have hsymm := Subgroup.mem_map_equiv.mp hΦ
  rwa [MulEquiv.symm_apply_apply] at hsymm

/-! ### Ring isomorphisms and directed unions -/

/-- Transport along a ring isomorphism.  (`simple_kazhdan_sofic_group.tex` l.733-735.) -/
theorem units_mem_elementaryGroup_of_ringEquiv {ι R S : Type*} [Fintype ι] [DecidableEq ι]
    [Ring R] [Ring S] (e : R ≃+* S) (hR : ∀ h : (Matrix ι ι R)ˣ, h ∈ elementaryGroup ι R)
    (g : (Matrix ι ι S)ˣ) : g ∈ elementaryGroup ι S := by
  rw [← elementaryGroup_map_eq_of_surjective (ι := ι) e.toRingHom e.surjective,
    Subgroup.mem_map]
  refine ⟨elementaryMatrixUnitMap e.symm.toRingHom g, hR _, ?_⟩
  apply Units.ext
  ext k l
  exact e.apply_symm_apply ((g : Matrix ι ι S) k l)

/-- **Continuity of `K₁` along directed unions**, unstable form: if every finite set of
coefficients of `S` lies in a subring over which all invertible `ι × ι` matrices are elementary,
then all invertible `ι × ι` matrices over `S` are elementary.  (ABC 2009, proof of Thm 3.6;
`simple_kazhdan_sofic_group.tex` l.733-735.) -/
theorem units_mem_elementaryGroup_of_subrings {ι S : Type*} [Fintype ι] [DecidableEq ι] [Ring S]
    (hS : ∀ s : Finset S, ∃ T : Subring S, (s : Set S) ⊆ T ∧
      ∀ h : (Matrix ι ι T)ˣ, h ∈ elementaryGroup ι T)
    (g : (Matrix ι ι S)ˣ) : g ∈ elementaryGroup ι S := by
  classical
  obtain ⟨T, hsT, hT⟩ := hS (Finset.univ.biUnion fun k : ι => Finset.univ.biUnion fun l : ι =>
    {(g : Matrix ι ι S) k l, ((g⁻¹ : (Matrix ι ι S)ˣ) : Matrix ι ι S) k l})
  have hmem : ∀ k l : ι, (g : Matrix ι ι S) k l ∈ T ∧
      ((g⁻¹ : (Matrix ι ι S)ˣ) : Matrix ι ι S) k l ∈ T := by
    intro k l
    constructor
    · refine SetLike.mem_coe.mp (hsT (Finset.mem_coe.mpr ?_))
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k,
        Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ l, Finset.mem_insert_self _ _⟩⟩
    · refine SetLike.mem_coe.mp (hsT (Finset.mem_coe.mpr ?_))
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k,
        Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ l,
          Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩⟩
  let G : Matrix ι ι T := Matrix.of fun k l => ⟨(g : Matrix ι ι S) k l, (hmem k l).1⟩
  let H : Matrix ι ι T :=
    Matrix.of fun k l => ⟨((g⁻¹ : (Matrix ι ι S)ˣ) : Matrix ι ι S) k l, (hmem k l).2⟩
  have hinj : Function.Injective (T.subtype.mapMatrix : Matrix ι ι T →+* Matrix ι ι S) := by
    intro M N hMN
    ext k l
    exact T.subtype_injective (congrArg (fun Z : Matrix ι ι S => Z k l) hMN)
  have hG : T.subtype.mapMatrix G = (g : Matrix ι ι S) := by
    ext k l
    rfl
  have hH : T.subtype.mapMatrix H = ((g⁻¹ : (Matrix ι ι S)ˣ) : Matrix ι ι S) := by
    ext k l
    rfl
  have hGH : G * H = 1 := by
    apply hinj
    rw [map_mul, map_one, hG, hH]
    exact Units.mul_inv g
  have hHG : H * G = 1 := by
    apply hinj
    rw [map_mul, map_one, hG, hH]
    exact Units.inv_mul g
  let u : (Matrix ι ι T)ˣ := ⟨G, H, hGH, hHG⟩
  have hu : elementaryMatrixUnitMap T.subtype u = g := by
    apply Units.ext
    exact hG
  rw [← hu]
  exact elementaryGroup_map_le T.subtype (Subgroup.mem_map.mpr ⟨u, hT u, rfl⟩)

/-! ### Ultramatricial rings -/

/-- **`K₁ = 0` for ultramatricial `𝔽₂`-rings** (unstable form, the `K₁` input of the degree-two
Yao sequence in WO-LVCohnK2-3): if every finite subset of `S` lies in a subring isomorphic to a
finite product `∏_j M_{d_j}(𝔽₂)`, then every invertible `ι × ι` matrix over `S`, `#ι ≥ 2`, is a
product of elementary matrices.  (Ara–Brustenga–Cortiñas 2009, `thm:skewyao`, `yaoseq6.tex`
l.574-640; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem units_mem_elementaryGroup_of_ultramatricial {S : Type*} [Ring S]
    (hS : ∀ s : Finset S, ∃ (k : ℕ) (d : Fin (k + 1) → ℕ) (T : Subring S), (s : Set S) ⊆ T ∧
      Nonempty (T ≃+* ((j : Fin (k + 1)) → Matrix (Fin (d j)) (Fin (d j)) (ZMod 2))))
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι] (g : (Matrix ι ι S)ˣ) :
    g ∈ elementaryGroup ι S := by
  refine units_mem_elementaryGroup_of_subrings (fun s => ?_) g
  obtain ⟨k, d, T, hsT, ⟨e⟩⟩ := hS s
  exact ⟨T, hsT, units_mem_elementaryGroup_of_ringEquiv e.symm
    (units_mem_elementaryGroup_pi fun j h => units_mem_elementaryGroup_matrix_zmodTwo (d j) h)⟩

/-- `units_mem_elementaryGroup_of_ultramatricial` in rank `n ≥ 2`. -/
theorem units_mem_elementaryGroup_fin_of_ultramatricial {S : Type*} [Ring S]
    (hS : ∀ s : Finset S, ∃ (k : ℕ) (d : Fin (k + 1) → ℕ) (T : Subring S), (s : Set S) ⊆ T ∧
      Nonempty (T ≃+* ((j : Fin (k + 1)) → Matrix (Fin (d j)) (Fin (d j)) (ZMod 2))))
    (n : ℕ) (hn : 2 ≤ n) (g : (Matrix (Fin n) (Fin n) S)ˣ) :
    g ∈ elementaryGroup (Fin n) S := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  exact units_mem_elementaryGroup_of_ultramatricial hS g

/-- **Lane 3c of WO-LVCohnK2-3**: `K1Statement S` (`GL_n(S) = E_n(S)` for `n ≥ 2`) for every
ultramatricial `𝔽₂`-ring `S`.  (Ara–Brustenga–Cortiñas 2009, `thm:skewyao`, the term
`ker(1 - φ on K₁ S)`, `yaoseq6.tex` l.574-640; `simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem k1Statement_of_ultramatricial {S : Type*} [Ring S] (hS : IsUltramatricialF2 S) :
    K1Statement S := by
  intro n hn g
  exact units_mem_elementaryGroup_fin_of_ultramatricial hS n hn g

end GroupApproximation.Full.LVSkewLaurentK2
