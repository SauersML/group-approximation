# Statements of the FLT slice

Every theorem statement in `flt-slice.tar.gz`, verbatim from its `Theorems/Thm_*.lean` module (the surrounding `open`/`universe` context is in the module). Grep this file to find a result by its hypotheses or conclusion; `INDEX.md` has the one-line headlines.

## Module (198)

### `Module.Basis.exists_forall_apply_eq_ringHom_smul_of_repr_mem_range_ratCast`

`Thm_Module_Basis_exists_forall_apply_eq_ringHom_smul_of_repr_mem_range_ratCast` — Galois conjugation of a common eigenvector of rational operators

```lean
theorem Module.Basis.exists_forall_apply_eq_ringHom_smul_of_repr_mem_range_ratCast
    {ι : Type*} [Fintype ι] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis ι ℂ V) {J : Type*} (S : J → V →ₗ[ℂ] V)
    (hS : ∀ (j : J) (i i' : ι), b.repr (S j (b i)) i' ∈ Set.range ((↑) : ℚ → ℂ))
    (ℓ : V →ₗ[ℂ] ℂ) (hℓ : ∀ i : ι, ℓ (b i) ∈ Set.range ((↑) : ℚ → ℂ))
    (lam : J → ℂ) (v : V) (hv : ∀ j : J, S j v = lam j • v) (hℓv : ℓ v ≠ 0)
    (R : Subalgebra ℤ ℂ) [Module.Finite ℤ R] (hR : ∀ j : J, lam j ∈ R) (τ : R →+* ℂ) :
    ∃ w : V, ℓ w ≠ 0 ∧ ∀ j : J, S j w = τ ⟨lam j, hR j⟩ • w
```

### `Module.Basis.exists_not_exists_eq_smul_and_forall_exists_sub_smul_eq_smul_of_mulVec_eq_smul`

`Thm_Module_Basis_exists_not_exists_eq_smul_and_forall_exists_sub_smul_eq_smul_of_mulVec_eq_smul` — Lifting a mod p common eigenvector to a p-primitive lattice vector

```lean
theorem Module.Basis.exists_not_exists_eq_smul_and_forall_exists_sub_smul_eq_smul_of_mulVec_eq_smul
    {Λ : Type*} [AddCommGroup Λ] {t : ℕ} (b : Module.Basis (Fin t) ℤ Λ)
    {I : Type*} (T : I → Λ →ₗ[ℤ] Λ) (n : I → ℤ)
    (p : ℕ) [Fact p.Prime] (κ : Type*) [Field κ] [CharP κ p]
    (m : Fin t → κ) (hm : m ≠ 0)
    (heig : ∀ i, ((LinearMap.toMatrix b b (T i)).map (Int.cast : ℤ → κ)).mulVec m = (n i : κ) • m) :
    ∃ v : Λ, (¬ ∃ w : Λ, v = (p : ℤ) • w) ∧ ∀ i, ∃ w : Λ, T i v - n i • v = (p : ℤ) • w
```

### `Module.Basis.repr_apply_mem_of_mem_ideal_smul_top`

`Thm_Module_Basis_repr_apply_mem_of_mem_ideal_smul_top` — Basis coordinates of elements of I · N lie in I

```lean
theorem Module.Basis.repr_apply_mem_of_mem_ideal_smul_top {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N] {κ : Type*} (b : Module.Basis κ R N) (I : Ideal R) {x : N} (hx : x ∈ (I • ⊤ : Submodule R N)) (k : κ) :
    b.repr x k ∈ I
```

### `Module.Basis.repr_mem_range_ratCast_of_forall_dual`

`Thm_Module_Basis_repr_mem_range_ratCast_of_forall_dual` — Rational coordinates from a separating family of rational forms

```lean
theorem Module.Basis.repr_mem_range_ratCast_of_forall_dual
    {ι : Type*} [Fintype ι] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis ι ℂ V) {A : Type*} (φ : A → V →ₗ[ℂ] ℂ)
    (hinj : ∀ x : V, (∀ a : A, φ a x = 0) → x = 0)
    (hφb : ∀ (a : A) (i : ι), φ a (b i) ∈ Set.range ((↑) : ℚ → ℂ))
    (h : V) (hh : ∀ a : A, φ a h ∈ Set.range ((↑) : ℚ → ℂ)) (i : ι) :
    b.repr h i ∈ Set.range ((↑) : ℚ → ℂ)
```

### `Module.Basis.tensorProduct_tensorProduct_linearIndependent_restrictScalars`

`Thm_Module_Basis_tensorProduct_tensorProduct_linearIndependent_restrictScalars` — R-linear independence of a triple tensor K-basis

```lean
theorem Module.Basis.tensorProduct_tensorProduct_linearIndependent_restrictScalars
    (R : Type) (K : Type) (A : Type) [CommRing R] [CommRing K] [Algebra R K] [CommRing A]
    [Algebra K A] [Algebra R A] [IsScalarTower R K A]
    (hinj : Function.Injective (algebraMap R K))
    {n : ℕ} (b : Module.Basis (Fin n) K A) :
    LinearIndependent R ((b.tensorProduct (b.tensorProduct b)) :
      Fin n × Fin n × Fin n → A ⊗[K] (A ⊗[K] A))
```

### `Module.End.CommFamily.finrank_inf_annPart_le_finrank_mul_of_forall_finrank_inf_iInf_ker_le`

`Thm_Module_End_CommFamily_finrank_inf_annPart_le_finrank_mul_of_forall_finrank_inf_iInf_ker_le` — Dimension bound for the 𝔪-annihilator of a commuting family

```lean
theorem Module.End.CommFamily.finrank_inf_annPart_le_finrank_mul_of_forall_finrank_inf_iInf_ker_le
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {σ : Type*}
    (F : Module.End.CommFamily K V σ) (p : ℕ) [Fact p.Prime] [CharP K p]
    {k₀ : Type*} [Field k₀] [Finite k₀] [Algebra (ZMod p) k₀]
    (θ₀ : σ → k₀) (hgen : Algebra.adjoin (ZMod p) (Set.range θ₀) = ⊤) (e : k₀ →+* K)
    (W : Submodule K V) (hW : ∀ (a : σ) (v : V), v ∈ W → F.T a v ∈ W) (d : ℕ)
    (hd : ∀ τ : k₀ →+* K,
      FiniteDimensional K ↥(W ⊓ ⨅ a : σ, LinearMap.ker (F.T a - τ (θ₀ a) • LinearMap.id)) ∧
        Module.finrank K ↥(W ⊓ ⨅ a : σ, LinearMap.ker (F.T a - τ (θ₀ a) • LinearMap.id)) ≤ d) :
    FiniteDimensional K ↥(W ⊓ F.annPart p (e ∘ θ₀)) ∧
      Module.finrank K ↥(W ⊓ F.annPart p (e ∘ θ₀)) ≤ Module.finrank (ZMod p) k₀ * d
```

### `Module.End.eq_one_of_pow_eq_one_of_forall_exists_sub_eq_prime_pow_smul`

`Thm_Module_End_eq_one_of_pow_eq_one_of_forall_exists_sub_eq_prime_pow_smul` — Rigidity of finite-order endomorphisms congruent to 1 mod pᵃ

```lean
theorem Module.End.eq_one_of_pow_eq_one_of_forall_exists_sub_eq_prime_pow_smul
    {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
    {p : ℕ} (hp : p.Prime) (a : ℕ) (ha : 1 ≤ a) (ha2 : p = 2 → 2 ≤ a)
    (htf : ∀ x : M, p • x = 0 → x = 0)
    (hsep : ∀ x : M, (∀ n : ℕ, ∃ y : M, x = p ^ n • y) → x = 0)
    (u : M →ₗ[R] M) (m : ℕ) (hm : m ≠ 0) (hu : u ^ m = 1)
    (hcong : ∀ x : M, ∃ y : M, u x - x = p ^ a • y) :
    u = 1
```

### `Module.End.eq_zero_of_isNilpotent_of_forall_commute_of_forall_isUnit_of_finrank_eq`

`Thm_Module_End_eq_zero_of_isNilpotent_of_forall_commute_of_forall_isUnit_of_finrank_eq` — Nilpotent endomorphisms commuting with a division algebra vanish

```lean
theorem Module.End.eq_zero_of_isNilpotent_of_forall_commute_of_forall_isUnit_of_finrank_eq
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {D : Type*} [Ring D] [Algebra F D] (hD : ∀ x : D, x ≠ 0 → IsUnit x)
    (ι : D →ₐ[F] Module.End F V) (hdim : Module.finrank F D = Module.finrank F V)
    {N : Module.End F V} (hcomm : ∀ d : D, Commute (ι d) N) (hN : IsNilpotent N) : N = 0
```

### `Module.End.exists_charpoly_eq_and_commute_and_trace_eq_zero_and_notMem_of_irreducible`

`Thm_Module_End_exists_charpoly_eq_and_commute_and_trace_eq_zero_and_notMem_of_irreducible` — Regular semisimple element with trace-zero centraliser vector outside U

```lean
theorem Module.End.exists_charpoly_eq_and_commute_and_trace_eq_zero_and_notMem_of_irreducible
    {k : Type u} [Field k] (h2 : (2 : k) ≠ 0)
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hV : Module.finrank k V = 2)
    {H : Type w} [Group H] (ρ : H →* Module.End k V)
    (hirr : ∀ W : Submodule k V, (∀ h : H, ∀ x ∈ W, ρ h x ∈ W) → W = ⊥ ∨ W = ⊤)
    (hsplit : ∀ h : H, ∃ α β : k, (ρ h).charpoly = (X - C α) * (X - C β))
    (U : AddSubgroup (Module.End k V))
    (hU : ∀ h : H, ∀ m ∈ U, ρ h * m * ρ h⁻¹ ∈ U)
    (hproper : ∃ m : Module.End k V, LinearMap.trace k V m = 0 ∧ m ∉ U) :
    ∃ h : H, ∃ α β : k, α ≠ β ∧ (ρ h).charpoly = (X - C α) * (X - C β) ∧
      ∃ m : Module.End k V, LinearMap.trace k V m = 0 ∧ m * ρ h = ρ h * m ∧ m ∉ U
```

### `Module.End.exists_common_eigenvector_of_commute`

`Thm_Module_End_exists_common_eigenvector_of_commute` — Common eigenvector for a commuting family of endomorphisms

```lean
theorem Module.End.exists_common_eigenvector_of_commute
    {K : Type*} [Field K] [IsAlgClosed K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V] {ι : Type*} (T : ι → Module.End K V)
    (hcomm : ∀ i j, Commute (T i) (T j)) :
    ∃ (χ : ι → K) (v : V), v ≠ 0 ∧ ∀ i, T i v = χ i • v
```

### `Module.End.exists_dual_ne_zero_forall_apply_eq_mul_of_commute`

`Thm_Module_End_exists_dual_ne_zero_forall_apply_eq_mul_of_commute` — Common eigen-functional for a commuting family of endomorphisms

```lean
theorem Module.End.exists_dual_ne_zero_forall_apply_eq_mul_of_commute
    {K : Type*} [Field K] [IsAlgClosed K]
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Nontrivial W]
    {ι : Type*} (T : ι → Module.End K W) (hT : ∀ i j : ι, Commute (T i) (T j)) :
    ∃ (μ : W →ₗ[K] K) (c : ι → K), μ ≠ 0 ∧ ∀ (i : ι) (w : W), μ (T i w) = c i * μ w
```

### `Module.End.exists_eigenvector_or_exists_eigenvector_of_dualMap_comp_eq_smul`

`Thm_Module_End_exists_eigenvector_or_exists_eigenvector_of_dualMap_comp_eq_smul` — Dichotomy for joint eigenvectors along an exact window

```lean
theorem Module.End.exists_eigenvector_or_exists_eigenvector_of_dualMap_comp_eq_smul
    {K : Type*} [Field K]
    {L S Ω' : Type*} [AddCommGroup L] [Module K L] [AddCommGroup S] [Module K S] [AddCommGroup Ω'] [Module K Ω']
    [FiniteDimensional K L] [FiniteDimensional K Ω']
    {ι : Type*}
    (TL : ι → Module.End K L) (hTL : ∀ i j, Commute (TL i) (TL j))
    (TS : ι → Module.End K S)
    (TΩ : ι → Module.End K Ω') (hTΩ : ∀ i j, Commute (TΩ i) (TΩ j))
    (res : L →ₗ[K] S) (hres : ∀ i, res ∘ₗ TL i = TS i ∘ₗ res)
    (Θ : S →ₗ[K] Module.Dual K Ω') (hexact : ∀ v : S, Θ v = 0 ↔ v ∈ LinearMap.range res)
    (c : ι → K) (hc : ∀ i, c i ≠ 0)
    (hΘ : ∀ (i : ι) (v : S), Θ (TS i v) = c i • (TΩ i).dualMap (Θ v))
    (lam : ι → K) (v : S) (hv0 : v ≠ 0) (hv : ∀ i, TS i v = lam i • v) :
    (∃ G : L, G ≠ 0 ∧ ∀ i, TL i G = lam i • G) ∨
    (∃ ω : Ω', ω ≠ 0 ∧ ∀ i, TΩ i ω = ((c i)⁻¹ * lam i) • ω)
```

### `Module.End.exists_forall_apply_eq_smul_of_pairwise_commute`

`Thm_Module_End_exists_forall_apply_eq_smul_of_pairwise_commute` — Common eigenvector for a commuting family of endomorphisms

```lean
theorem Module.End.exists_forall_apply_eq_smul_of_pairwise_commute
    {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V]
    {ι : Type*} (T : ι → Module.End K V) (hT : Pairwise fun i j ↦ Commute (T i) (T j)) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, ∃ c : K, T i v = c • v
```

### `Module.End.exists_isNilpotent_pow_sub_one_of_mul_eq_pow_mul_of_isUnit`

`Thm_Module_End_exists_isNilpotent_pow_sub_one_of_mul_eq_pow_mul_of_isUnit` — An endomorphism conjugate to its q-th power is quasi-unipotent

```lean
theorem Module.End.exists_isNilpotent_pow_sub_one_of_mul_eq_pow_mul_of_isUnit
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (g h : Module.End F V) (hg : IsUnit g) (hh : IsUnit h) {q : ℕ} (hq : 2 ≤ q)
    (hrel : h * g = g ^ q * h) :
    ∃ e : ℕ, 0 < e ∧ IsNilpotent (g ^ e - 1)
```

### `Module.End.exists_linearEquiv_forall_algHom_matrix_apply_eq_mulVec_of_finrank_eq_two`

`Thm_Module_End_exists_linearEquiv_forall_algHom_matrix_apply_eq_mulVec_of_finrank_eq_two` — A two-dimensional M₂(k)-module is the standard one

```lean
theorem Module.End.exists_linearEquiv_forall_algHom_matrix_apply_eq_mulVec_of_finrank_eq_two
    (k : Type*) [Field k] (W : Type*) [AddCommGroup W] [Module k W] [Module.Finite k W]
    (hW : Module.finrank k W = 2) (ψ : Matrix (Fin 2) (Fin 2) k →ₐ[k] (W →ₗ[k] W)) :
    ∃ e : W ≃ₗ[k] (Fin 2 → k), ∀ (m : Matrix (Fin 2) (Fin 2) k) (w : W), e (ψ m w) = m.mulVec (e w)
```

### `Module.End.exists_mem_adjoin_aeval_ne_zero_mul_eq_of_ratForm_of_multiplicityOne`

`Thm_Module_End_exists_mem_adjoin_aeval_ne_zero_mul_eq_of_ratForm_of_multiplicityOne` — Good operators generate at a multiplicity-one eigenvector

```lean
theorem Module.End.exists_mem_adjoin_aeval_ne_zero_mul_eq_of_ratForm_of_multiplicityOne
    {L V σ : Type} [Field L] [CharZero L] [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    [Module ℚ V] [IsScalarTower ℚ L V]
    (VQ : Submodule ℚ V)
    (hli : ∀ (n : ℕ) (v : Fin n → V), (∀ i, v i ∈ VQ) →
      LinearIndependent ℚ v → LinearIndependent L v)
    (hspan : Submodule.span L (VQ : Set V) = ⊤)
    (ρ : MvPolynomial σ ℤ →+* Module.End L V)
    (hrat : ∀ (i : σ) (v : V), v ∈ VQ → ρ (MvPolynomial.X i) v ∈ VQ)
    (G : Set σ)
    (hss : ∀ i ∈ G, ∃ P : Polynomial ℚ, P.Separable ∧
      Polynomial.aeval (ρ (MvPolynomial.X i)) (P.map (algebraMap ℚ L)) = 0)
    (lam : σ → L) (v₀ : V) (hv₀ : v₀ ≠ 0)
    (heig : ∀ i ∈ G, ρ (MvPolynomial.X i) v₀ = lam i • v₀)
    (hmult : ∀ w : V, (∀ i ∈ G, ρ (MvPolynomial.X i) w = lam i • w) → ∃ c : L, w = c • v₀)
    (t : MvPolynomial σ ℤ) :
    ∃ s ∈ Algebra.adjoin ℤ (MvPolynomial.X '' G : Set (MvPolynomial σ ℤ)),
      ∃ u ∈ Algebra.adjoin ℤ (MvPolynomial.X '' G : Set (MvPolynomial σ ℤ)),
        MvPolynomial.aeval lam s ≠ 0 ∧ ρ s * ρ t = ρ u
```

### `Module.End.exists_mem_adjoin_apply_eq_self_and_apply_eq_zero_of_forall_ne_exists_ne`

`Thm_Module_End_exists_mem_adjoin_apply_eq_self_and_apply_eq_zero_of_forall_ne_exists_ne` — Idempotent-like operators from scalar actions separating indices

```lean
theorem Module.End.exists_mem_adjoin_apply_eq_self_and_apply_eq_zero_of_forall_ne_exists_ne
    {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : ι → Submodule K V) (𝒯 : Set (Module.End K V)) (c : Module.End K V → ι → K)
    (hT : ∀ T ∈ 𝒯, ∀ (i : ι), ∀ v ∈ W i, T v = c T i • v)
    (hsep : ∀ i j : ι, i ≠ j → ∃ T ∈ 𝒯, c T i ≠ c T j) (i : ι) :
    ∃ e ∈ Algebra.adjoin K 𝒯, (∀ v ∈ W i, e v = v) ∧ ∀ j : ι, j ≠ i → ∀ v ∈ W j, e v = 0
```

### `Module.End.exists_monic_map_eq_charpoly_and_charpoly_eq_sq_of_span_real_dual_eq_top`

`Thm_Module_End_exists_monic_map_eq_charpoly_and_charpoly_eq_sq_of_span_real_dual_eq_top` — Rational and analytic characteristic polynomials of a complex torus endomorphism

```lean
theorem Module.End.exists_monic_map_eq_charpoly_and_charpoly_eq_sq_of_span_real_dual_eq_top
    {S : Type*} [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]
    (T : S →ₗ[ℂ] S) (hreal : T.charpoly.map (starRingEnd ℂ) = T.charpoly)
    (Λ : Submodule ℤ (Module.Dual ℂ S)) [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    {n : ℕ} (b : Module.Basis (Fin n) ℤ Λ)
    (hli : LinearIndependent ℝ (fun i => ((b i : Λ) : Module.Dual ℂ S)))
    (hsp : Submodule.span ℝ (Set.range fun i => ((b i : Λ) : Module.Dual ℂ S)) = ⊤)
    (τ : Module.End ℤ Λ)
    (hτ : ∀ x : Λ, ((τ x : Λ) : Module.Dual ℂ S) = (x : Module.Dual ℂ S) ∘ₗ T) :
    ∃ Q : Polynomial ℤ, Q.Monic ∧ Q.map (algebraMap ℤ ℂ) = T.charpoly ∧ τ.charpoly = Q ^ 2
```

### `Module.End.exists_ne_zero_forall_apply_eq_smul_iff_exists_ne_zero_forall_dualMap_apply_eq_smul`

`Thm_Module_End_exists_ne_zero_forall_apply_eq_smul_iff_exists_ne_zero_forall_dualMap_apply_eq_smul` — Joint eigenvectors exist iff joint dual eigenvectors exist

```lean
theorem Module.End.exists_ne_zero_forall_apply_eq_smul_iff_exists_ne_zero_forall_dualMap_apply_eq_smul
    {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {ι : Type*} (T : ι → Module.End K V) (hT : ∀ i j, Commute (T i) (T j)) (μ : ι → K) :
    (∃ v : V, v ≠ 0 ∧ ∀ i, T i v = μ i • v) ↔
      ∃ φ : Module.Dual K V, φ ≠ 0 ∧ ∀ i, (T i).dualMap φ = μ i • φ
```

### `Module.End.exists_ne_zero_forall_apply_eq_smul_of_dual_comp_eq_smul`

`Thm_Module_End_exists_ne_zero_forall_apply_eq_smul_of_dual_comp_eq_smul` — From a simultaneous dual eigenvector to a simultaneous eigenvector

```lean
theorem Module.End.exists_ne_zero_forall_apply_eq_smul_of_dual_comp_eq_smul
    {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    {R : Type*} [CommRing R] (T : R →+* Module.End K M) (a : R →+* K)
    (μ : Module.Dual K M) (hμ : μ ≠ 0) (hco : ∀ r : R, μ ∘ₗ (T r : M →ₗ[K] M) = a r • μ) :
    ∃ m : M, m ≠ 0 ∧ ∀ r : R, T r m = a r • m
```

### `Module.End.exists_ne_zero_forall_apply_eq_smul_of_forall_sub_smul_mem`

`Thm_Module_End_exists_ne_zero_forall_apply_eq_smul_of_forall_sub_smul_mem` — Joint eigenvectors lift from a quotient to the whole space

```lean
theorem Module.End.exists_ne_zero_forall_apply_eq_smul_of_forall_sub_smul_mem
    {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {ι : Type*} (T : ι → Module.End K V) (hT : ∀ i j, Commute (T i) (T j))
    (W : Submodule K V) (hW : ∀ i, ∀ w ∈ W, T i w ∈ W)
    (mu : ι → K) (v : V) (hv : v ∉ W) (heig : ∀ i, T i v - mu i • v ∈ W) :
    ∃ u : V, u ≠ 0 ∧ ∀ i, T i u = mu i • u
```

### `Module.End.exists_ne_zero_forall_apply_eq_smul_of_ringHom`

`Thm_Module_End_exists_ne_zero_forall_apply_eq_smul_of_ringHom` — Characters of a ring stabilising a faithful lattice are eigenvalue systems

```lean
theorem Module.End.exists_ne_zero_forall_apply_eq_smul_of_ringHom {K V T : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V] [CommRing T] (ρ : T →+* Module.End K V) (L : Submodule ℤ V) (hL : L.FG) (hstab : ∀ (t : T), ∀ x ∈ L, ρ t x ∈ L) (hfaith : ∀ t : T, (∀ x ∈ L, ρ t x = 0) → t = 0) (hfree : ∀ (n : ℕ) (y : Fin n → V), (∀ i, y i ∈ L) → LinearIndependent ℤ y → LinearIndependent K y) (χ : T →+* K) : ∃ v : V, v ≠ 0 ∧ ∀ t : T, ρ t v = χ t • v
```

### `Module.End.exists_primitive_strings_basis_of_sl2_of_iSup_eigenspace_eq_top`

`Thm_Module_End_exists_primitive_strings_basis_of_sl2_of_iSup_eigenspace_eq_top` — Basis of mathfraksl₂-strings from primitive vectors

```lean
theorem Module.End.exists_primitive_strings_basis_of_sl2_of_iSup_eigenspace_eq_top
    (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (e f h : V →ₗ[ℂ] V)
    (hhe : h ∘ₗ e - e ∘ₗ h = (2 : ℂ) • e) (hhf : h ∘ₗ f - f ∘ₗ h = -((2 : ℂ) • f)) (hef : e ∘ₗ f - f ∘ₗ e = h)
    (hdiag : ⨆ μ : ℂ, Module.End.eigenspace h μ = ⊤) :
    ∃ (r : ℕ) (t : Fin r → V) (n : Fin r → ℕ),
      (∀ i, e (t i) = 0 ∧ h (t i) = (n i : ℂ) • t i ∧ (f ^ (n i + 1)) (t i) = 0) ∧
      (∀ i (p : ℕ), p ≤ n i →
        h ((f ^ p) (t i)) = ((n i : ℂ) - 2 * (p : ℂ)) • (f ^ p) (t i) ∧
        e ((f ^ (p + 1)) (t i)) = (((p : ℂ) + 1) * ((n i : ℂ) - (p : ℂ))) • (f ^ p) (t i)) ∧
      LinearIndependent ℂ (fun x : (Σ i : Fin r, Fin (n i + 1)) => (f ^ (x.2 : ℕ)) (t x.1)) ∧
      Submodule.span ℂ (Set.range (fun x : (Σ i : Fin r, Fin (n i + 1)) => (f ^ (x.2 : ℕ)) (t x.1))) = ⊤
```

### `Module.End.finrank_iInf_eigenspace_baseChange_complex_eq_add`

`Thm_Module_End_finrank_iInf_eigenspace_baseChange_complex_eq_add` — Common eigenspaces in the complexification of a real lattice

```lean
theorem Module.End.finrank_iInf_eigenspace_baseChange_complex_eq_add
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (Λ : Submodule ℤ V) {n : ℕ} (b : Module.Basis (Fin n) ℤ Λ)
    (hli : ∀ r : Fin n → ℝ, ∑ i, ((r i : ℂ)) • ((b i : Λ) : V) = 0 → r = 0)
    (hsp : ∀ v : V, ∃ r : Fin n → ℝ, ∑ i, ((r i : ℂ)) • ((b i : Λ) : V) = v)
    {ι : Type*} (D : ι → Module.End ℂ V) (A : ι → Module.End ℤ Λ)
    (hA : ∀ (i : ι) (x : Λ), ((A i x : Λ) : V) = D i (x : V)) (c : ι → ℂ) :
    Module.finrank ℂ ↥(⨅ i, Module.End.eigenspace ((A i).baseChange ℂ) (c i)) =
      Module.finrank ℂ ↥(⨅ i, Module.End.eigenspace (D i) (c i)) +
        Module.finrank ℂ ↥(⨅ i, Module.End.eigenspace (D i) (starRingEnd ℂ (c i)))
```

### `Module.End.finrank_iInf_eigenspace_baseChange_eq`

`Thm_Module_End_finrank_iInf_eigenspace_baseChange_eq` — Common eigenspace dimension is invariant under field base change

```lean
theorem Module.End.finrank_iInf_eigenspace_baseChange_eq
    (F L : Type*) [Field F] [Field L] [Algebra F L]
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {ι : Type*} (T : ι → Module.End F W) (c : ι → F) :
    Module.finrank L ↥(⨅ i, Module.End.eigenspace ((T i).baseChange L) (algebraMap F L (c i))) =
      Module.finrank F ↥(⨅ i, Module.End.eigenspace (T i) (c i))
```

### `Module.End.finrank_iInf_maxGenEigenspace_baseChange_eq_mul_prod_rootMultiplicity_of_isAlgClosed`

`Thm_Module_End_finrank_iInf_maxGenEigenspace_baseChange_eq_mul_prod_rootMultiplicity_of_isAlgClosed` — Joint generalised eigenspace dimensions are independent of the extension field

```lean
theorem Module.End.finrank_iInf_maxGenEigenspace_baseChange_eq_mul_prod_rootMultiplicity_of_isAlgClosed
    {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {Q : Type} [Fintype Q] (U : Q → Module.End K W) (P : Q → Polynomial K) (c : ℕ)
    (Ω₁ : Type) [Field Ω₁] [Algebra K Ω₁] [IsAlgClosed Ω₁]
    (h₁ : ∀ μ : Q → Ω₁, Module.finrank Ω₁
        ↥(⨅ q, Module.End.maxGenEigenspace ((U q).baseChange Ω₁) (μ q)) =
      c * ∏ q, Polynomial.rootMultiplicity (μ q) ((P q).map (algebraMap K Ω₁)))
    (Ω₂ : Type) [Field Ω₂] [Algebra K Ω₂] (lam : Q → Ω₂) :
    Module.finrank Ω₂ ↥(⨅ q, Module.End.maxGenEigenspace ((U q).baseChange Ω₂) (lam q)) =
      c * ∏ q, Polynomial.rootMultiplicity (lam q) ((P q).map (algebraMap K Ω₂))
```

### `Module.End.finrank_iInf_maxGenEigenspace_eq_prod_rootMultiplicity_of_apply_eq_sum_update`

`Thm_Module_End_finrank_iInf_maxGenEigenspace_eq_prod_rootMultiplicity_of_apply_eq_sum_update` — Joint generalised eigenspace of coordinate operators on a box

```lean
theorem Module.End.finrank_iInf_maxGenEigenspace_eq_prod_rootMultiplicity_of_apply_eq_sum_update
    {F : Type} [Field F] {Q : Type} [Fintype Q] [DecidableEq Q] (ι : Q → Type)
    [∀ q, Fintype (ι q)] [∀ q, DecidableEq (ι q)]
    (C : (q : Q) → Matrix (ι q) (ι q) F)
    (U : Q → Module.End F (((q : Q) → ι q) → F))
    (hU : ∀ (q : Q) (v : ((q : Q) → ι q) → F) (j : (q : Q) → ι q),
      U q v j = ∑ i : ι q, C q (j q) i * v (Function.update j q i))
    (lam : Q → F) :
    Module.finrank F ↥(⨅ q, Module.End.maxGenEigenspace (U q) (lam q)) =
      ∏ q, ((C q).charpoly).rootMultiplicity (lam q)
```

### `Module.End.finrank_iInf_maxGenEigenspace_map_tensorProduct_eq_mul`

`Thm_Module_End_finrank_iInf_maxGenEigenspace_map_tensorProduct_eq_mul` — Dimension of simultaneous generalised eigenspaces on a tensor product

```lean
theorem Module.End.finrank_iInf_maxGenEigenspace_map_tensorProduct_eq_mul
    (F : Type) [Field F]
    (V W : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {ι κ : Type} (A : ι → Module.End F V) (μ : ι → F) (B : κ → Module.End F W) (ν : κ → F) :
    Module.finrank F
      ↥((⨅ i : ι, Module.End.maxGenEigenspace (TensorProduct.map (A i) (LinearMap.id : W →ₗ[F] W)) (μ i)) ⊓
        (⨅ j : κ, Module.End.maxGenEigenspace (TensorProduct.map (LinearMap.id : V →ₗ[F] V) (B j)) (ν j))) =
    Module.finrank F ↥(⨅ i : ι, Module.End.maxGenEigenspace (A i) (μ i)) *
      Module.finrank F ↥(⨅ j : κ, Module.End.maxGenEigenspace (B j) (ν j))
```

### `Module.End.forall_isSemisimple_and_isReduced_adjoin_of_commute`

`Thm_Module_End_forall_isSemisimple_and_isReduced_adjoin_of_commute` — Adjoin of commuting semisimple endomorphisms: semisimple and reduced

```lean
theorem Module.End.forall_isSemisimple_and_isReduced_adjoin_of_commute
    {K : Type*} [Field K] [PerfectField K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {s : Set (Module.End K V)} (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x)
    (hs : ∀ x ∈ s, Module.End.IsSemisimple x) :
    (∀ a ∈ Algebra.adjoin K s, Module.End.IsSemisimple a) ∧ IsReduced ↥(Algebra.adjoin K s)
```

### `Module.End.isNilpotent_of_mem_adjoin_of_forall_eigenvector_apply_eq_zero`

`Thm_Module_End_isNilpotent_of_mem_adjoin_of_forall_eigenvector_apply_eq_zero` — Killing all common eigenvectors forces nilpotence

```lean
theorem Module.End.isNilpotent_of_mem_adjoin_of_forall_eigenvector_apply_eq_zero
    {K : Type*} [Field K] [IsAlgClosed K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {ι : Type*} (t : ι → Module.End K V) (ht : ∀ i j, Commute (t i) (t j))
    (a : Module.End K V) (ha : a ∈ Algebra.adjoin K (Set.range t))
    (h : ∀ (χ : ι → K) (v : V), v ≠ 0 → (∀ i, t i v = χ i • v) → a v = 0) :
    IsNilpotent a
```

### `Module.End.maxGenEigenspace_baseChange_le_eigenspace_of_isAlgClosed`

`Thm_Module_End_maxGenEigenspace_baseChange_le_eigenspace_of_isAlgClosed` — Semisimplicity of a base change descends and spreads to all extensions

```lean
theorem Module.End.maxGenEigenspace_baseChange_le_eigenspace_of_isAlgClosed
    {K : Type} [Field K] [CharZero K] {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (T : Module.End K W)
    (Ω₁ : Type) [Field Ω₁] [Algebra K Ω₁] [IsAlgClosed Ω₁]
    (h₁ : ∀ μ : Ω₁, Module.End.maxGenEigenspace (T.baseChange Ω₁) μ ≤
      Module.End.eigenspace (T.baseChange Ω₁) μ)
    (Ω₂ : Type) [Field Ω₂] [Algebra K Ω₂] (μ : Ω₂) :
    Module.End.maxGenEigenspace (T.baseChange Ω₂) μ ≤ Module.End.eigenspace (T.baseChange Ω₂) μ
```

### `Module.End.mem_ideal_of_forall_apply_eq_zero_zmod`

`Thm_Module_End_mem_ideal_of_forall_apply_eq_zero_zmod` — Left ideals of End(M) are double annihilators over ℤ/n

```lean
theorem Module.End.mem_ideal_of_forall_apply_eq_zero_zmod
    {n : ℕ} [NeZero n] {M : Type*} [AddCommGroup M] [Module (ZMod n) M]
    [Module.Free (ZMod n) M] [Module.Finite (ZMod n) M]
    (J : Ideal (Module.End (ZMod n) M)) (b : Module.End (ZMod n) M)
    (hb : ∀ m : M, (∀ j ∈ J, j m = 0) → b m = 0) :
    b ∈ J
```

### `Module.End.mem_span_prod_apply_and_finrank_iInf_eigenspace_le_one_of_divisorString`

`Thm_Module_End_mem_span_prod_apply_and_finrank_iInf_eigenspace_le_one_of_divisorString` — Divisor-string modules are cyclic with one-dimensional joint eigenspaces

```lean
theorem Module.End.mem_span_prod_apply_and_finrank_iInf_eigenspace_le_one_of_divisorString
    (D : ℕ) (hD : D ≠ 0)
    (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (e : ℕ → V)
    (hli : LinearIndependent ℂ (fun d : Nat.divisors D => e (d : ℕ)))
    (hspan : Submodule.span ℂ (Set.range fun d : Nat.divisors D => e (d : ℕ)) = ⊤)
    (U : ℕ → Module.End ℂ V)
    (hcomm : ∀ p q : ℕ, p.Prime → q.Prime → p ∣ D → q ∣ D → Commute (U p) (U q))
    (hdown : ∀ q : ℕ, q.Prime → q ∣ D → ∀ d : ℕ, d ∣ D → q ∣ d → U q (e d) = e (d / q))
    (hbase : ∀ q : ℕ, q.Prime → q ∣ D → ∃ a b : ℂ, ∀ d : ℕ, d ∣ D → ¬ q ∣ d →
      U q (e d) = a • e d + b • e (d * q)) :
    (∀ d : ℕ, d ∣ D → ∃ T ∈ Algebra.adjoin ℂ {A : Module.End ℂ V | ∃ q : ℕ, q.Prime ∧ q ∣ D ∧ A = U q},
      e d = T (e D)) ∧
    ∀ lam : ℕ → ℂ,
      Module.finrank ℂ ↥(⨅ q ∈ D.primeFactors, Module.End.eigenspace (U q) (lam q)) ≤ 1
```

### `Module.End.nonempty_basis_fin_one_and_finrank_iInf_eigenspace_eq_one_of_iSupIndep_of_cyclic`

`Thm_Module_End_nonempty_basis_fin_one_and_finrank_iInf_eigenspace_eq_one_of_iSupIndep_of_cyclic` — Rank-one freeness and multiplicity one for a commutative operator algebra

```lean
theorem Module.End.nonempty_basis_fin_one_and_finrank_iInf_eigenspace_eq_one_of_iSupIndep_of_cyclic
    {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {ι : Type*} [Fintype ι]
    (V : ι → Submodule K W) (hVind : iSupIndep V) (hVtop : iSup V = ⊤)
    (A : Subalgebra K (Module.End K W))
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hstab : ∀ a ∈ A, ∀ (i : ι), ∀ v ∈ V i, a v ∈ V i)
    (e : ι → ↥A) (he₁ : ∀ (i : ι), ∀ v ∈ V i, (e i : Module.End K W) v = v)
    (he₀ : ∀ (i j : ι), j ≠ i → ∀ v ∈ V j, (e i : Module.End K W) v = 0)
    (w : ι → W) (hw : ∀ i, w i ∈ V i)
    (hcyc : ∀ (i : ι), ∀ v ∈ V i, ∃ a : ↥A, (a : Module.End K W) (w i) = v)
    (hle : ∀ (i : ι) (χ : ↥A →ₐ[K] K),
      Module.finrank K ↥(V i ⊓ ⨅ a : ↥A, Module.End.eigenspace (a : Module.End K W) (χ a)) ≤ 1) :
    Nonempty (Module.Basis (Fin 1) ↥A W) ∧
    ∀ χ : ↥A →ₐ[K] K,
      Module.finrank K ↥(⨅ a : ↥A, Module.End.eigenspace (a : Module.End K W) (χ a)) = 1
```

### `Module.End.pow_eq_one_of_isNilpotent_pow_sub_one_of_forall_commute_of_forall_isUnit_of_finrank_eq`

`Thm_Module_End_pow_eq_one_of_isNilpotent_pow_sub_one_of_forall_commute_of_forall_isUnit_of_finrank_eq` — Quasi-unipotent operator commuting with a division algebra has g^e=1

```lean
theorem Module.End.pow_eq_one_of_isNilpotent_pow_sub_one_of_forall_commute_of_forall_isUnit_of_finrank_eq
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {D : Type*} [Ring D] [Algebra F D] (hD : ∀ x : D, x ≠ 0 → IsUnit x)
    (ι : D →ₐ[F] Module.End F V) (hdim : Module.finrank F D = Module.finrank F V)
    {g : Module.End F V} (hcomm : ∀ d : D, Commute (ι d) g) {e : ℕ}
    (he : IsNilpotent (g ^ e - 1)) : g ^ e = 1
```

### `Module.End.rank_le_one_of_countable_of_commute_of_forall_invariant_eq_bot_or_eq_top`

`Thm_Module_End_rank_le_one_of_countable_of_commute_of_forall_invariant_eq_bot_or_eq_top` — Dixmier's Schur lemma over ℂ in countable dimension

```lean
theorem Module.End.rank_le_one_of_countable_of_commute_of_forall_invariant_eq_bot_or_eq_top
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (hV : Module.rank ℂ V ≤ Cardinal.aleph0)
    (𝒜 : Set (Module.End ℂ V))
    (hcomm : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A * B = B * A)
    (hirr : ∀ W : Submodule ℂ V, (∀ A ∈ 𝒜, ∀ x ∈ W, A x ∈ W) → W = ⊥ ∨ W = ⊤) :
    Module.rank ℂ V ≤ 1
```

### `Module.End.sub_one_pow_eq_zero_of_pow_sub_one_pow_eq_zero_of_eq_one_add_pow_smul`

`Thm_Module_End_sub_one_pow_eq_zero_of_pow_sub_one_pow_eq_zero_of_eq_one_add_pow_smul` — Minkowski–Serre rigidity modulo ℓᵃ≥ 3

```lean
theorem Module.End.sub_one_pow_eq_zero_of_pow_sub_one_pow_eq_zero_of_eq_one_add_pow_smul
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {ℓ : ℕ} (hℓ : ℓ.Prime) {a : ℕ} (ha : 3 ≤ ℓ ^ a)
    (htf : ∀ x : M, (ℓ : R) • x = 0 → x = 0)
    (hsep : ∀ x : M, (∀ k : ℕ, ∃ z : M, (ℓ : R) ^ k • z = x) → x = 0)
    {m : ℕ} (hm : 0 < m) (hunit : ∀ r : ℕ, r.Prime → r ∣ m → r ≠ ℓ → IsUnit (r : R))
    (g y : Module.End R M) (hg : g = 1 + ((ℓ : R) ^ a) • y)
    {n : ℕ} (hn : (g ^ m - 1) ^ n = 0) : (g - 1) ^ n = 0
```

### `Module.End.sum_range_pow_eq_zero_of_pow_eq_one_of_mul_dvd`

`Thm_Module_End_sum_range_pow_eq_zero_of_pow_eq_one_of_mul_dvd` — Geometric sums of a finite-order endomorphism vanish in characteristic p

```lean
theorem Module.End.sum_range_pow_eq_zero_of_pow_eq_one_of_mul_dvd {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (p : ℕ) [CharP R p] (T : Module.End R V) {d n : ℕ} (hd : T ^ d = 1) (hdn : p * d ∣ n) :
    ∑ i ∈ Finset.range n, T ^ i = 0
```

### `Module.End.trace_eq_of_mul_self_sub_smul_add_smul_eq_zero`

`Thm_Module_End_trace_eq_of_mul_self_sub_smul_add_smul_eq_zero` — Trace from a quadratic relation in dimension 2

```lean
theorem Module.End.trace_eq_of_mul_self_sub_smul_add_smul_eq_zero {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V] (b : Module.Basis (Fin 2) k V) {f : Module.End k V} {a c : k} (hrel : f * f - a • f + c • 1 = 0) (hdet : LinearMap.det f = c) (hc : c ≠ 0) : LinearMap.trace k V f = a
```

### `Module.FaithfullyFlat.exists_algebraMap_eq_of_tmul_one_eq_one_tmul`

`Thm_Module_FaithfullyFlat_exists_algebraMap_eq_of_tmul_one_eq_one_tmul` — Degree-zero exactness of the Amitsur complex

```lean
theorem Module.FaithfullyFlat.exists_algebraMap_eq_of_tmul_one_eq_one_tmul
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] {b : B} (hb : b ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] b) :
    ∃ a : A, algebraMap A B a = b
```

### `Module.FaithfullyFlat.exists_completeOrthogonalIdempotents_eq_sum_tmul_of_isBaseChange`

`Thm_Module_FaithfullyFlat_exists_completeOrthogonalIdempotents_eq_sum_tmul_of_isBaseChange` — Split twisted forms of ℤ^G over ℤ are coboundaries

```lean
theorem Module.FaithfullyFlat.exists_completeOrthogonalIdempotents_eq_sum_tmul_of_isBaseChange
    (A : Type u) [CommRing A] [Module.FaithfullyFlat ℤ A]
    {G : Type v} [AddCommGroup G] [Fintype G]
    (e : G → A ⊗[ℤ] A) (he : CompleteOrthogonalIdempotents e)
    (M : Submodule ℤ (G → A))
    (hM : ∀ f : G → A, f ∈ M ↔ ∀ k, ∑ m, e m * (f (k - m) ⊗ₜ[ℤ] 1) = 1 ⊗ₜ[ℤ] f k)
    (hbc : IsBaseChange A M.subtype) :
    ∃ d : G → A, CompleteOrthogonalIdempotents d ∧ ∀ k, e k = ∑ i, d i ⊗ₜ[ℤ] d (i - k)
```

### `Module.FaithfullyFlat.exists_eq_inv_tmul_of_amitsur_cocycle`

`Thm_Module_FaithfullyFlat_exists_eq_inv_tmul_of_amitsur_cocycle` — Amitsur 1-cocycles of units split when Pic R is trivial

```lean
theorem Module.FaithfullyFlat.exists_eq_inv_tmul_of_amitsur_cocycle
    {R : Type u} [CommRing R] [Subsingleton (CommRing.Pic R)]
    {A : Type v} [CommRing A] [Algebra R A] [Module.FaithfullyFlat R A]
    (u : (A ⊗[R] A)ˣ)
    (hu : Algebra.TensorProduct.map (AlgHom.id R A)
          (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A) (u : A ⊗[R] A) *
        (Algebra.TensorProduct.includeRight : A ⊗[R] A →ₐ[R] A ⊗[R] (A ⊗[R] A)) (u : A ⊗[R] A) =
      Algebra.TensorProduct.map (AlgHom.id R A)
          (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A) (u : A ⊗[R] A)) :
    ∃ a : Aˣ, (u : A ⊗[R] A) = (↑a⁻¹ : A) ⊗ₜ[R] (a : A)
```

### `Module.FaithfullyFlat.exists_eq_tmul_one_sub_one_tmul_of_amitsur_cocycle`

`Thm_Module_FaithfullyFlat_exists_eq_tmul_one_sub_one_tmul_of_amitsur_cocycle` — Additive Amitsur 1-cocycles are coboundaries (faithfully flat descent)

```lean
theorem Module.FaithfullyFlat.exists_eq_tmul_one_sub_one_tmul_of_amitsur_cocycle
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    (c : S ⊗[R] S)
    (hc : Algebra.TensorProduct.map (AlgHom.id R S)
            (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S) c +
          (Algebra.TensorProduct.includeRight : S ⊗[R] S →ₐ[R] S ⊗[R] (S ⊗[R] S)) c =
        Algebra.TensorProduct.map (AlgHom.id R S)
            (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S) c) :
    ∃ s : S, c = s ⊗ₜ[R] (1 : S) - (1 : S) ⊗ₜ[R] s
```

### `Module.FaithfullyFlat.exists_isAlgClosed_algebra_isScalarTower_of_isAlgClosed`

`Thm_Module_FaithfullyFlat_exists_isAlgClosed_algebra_isScalarTower_of_isAlgClosed` — Geometric points lift along a faithfully flat algebra

```lean
theorem Module.FaithfullyFlat.exists_isAlgClosed_algebra_isScalarTower_of_isAlgClosed
    (R W k : Type) [CommRing R] [CommRing W] [Algebra R W] [Module.FaithfullyFlat R W]
    [Field k] [IsAlgClosed k] [Algebra R k] :
    ∃ (k' : Type) (_ : Field k') (_ : IsAlgClosed k') (_ : Algebra R k') (_ : Algebra W k') (_ : Algebra k k'),
      IsScalarTower R W k' ∧ IsScalarTower R k k'
```

### `Module.FaithfullyFlat.exists_ringHom_comp_algebraMap_eq_of_finiteType_of_isAlgClosed`

`Thm_Module_FaithfullyFlat_exists_ringHom_comp_algebraMap_eq_of_finiteType_of_isAlgClosed` — Lifting geometric points along a faithfully flat finite-type algebra

```lean
theorem Module.FaithfullyFlat.exists_ringHom_comp_algebraMap_eq_of_finiteType_of_isAlgClosed
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
    [Module.FaithfullyFlat S S'] [Algebra.FiniteType S S']
    (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) :
    ∃ σ : S' →+* k, σ.comp (algebraMap S S') = sk
```

### `Module.FaithfullyFlat.exists_ringHom_isAlgClosed_comp_algebraMap_eq`

`Thm_Module_FaithfullyFlat_exists_ringHom_isAlgClosed_comp_algebraMap_eq` — Points with values in fields lift along faithfully flat algebras

```lean
theorem Module.FaithfullyFlat.exists_ringHom_isAlgClosed_comp_algebraMap_eq
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    (k : Type u) [Field k] (sk : S →+* k) :
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (j : k →+* K) (sK : S' →+* K),
      sK.comp (algebraMap S S') = j.comp sk
```

### `Module.FaithfullyFlat.exists_submodule_forall_mem_iff_sum_mul_tmul_isBaseChange`

`Thm_Module_FaithfullyFlat_exists_submodule_forall_mem_iff_sum_mul_tmul_isBaseChange` — Effective descent along an idempotent Amitsur cocycle

```lean
theorem Module.FaithfullyFlat.exists_submodule_forall_mem_iff_sum_mul_tmul_isBaseChange
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.FaithfullyFlat R A]
    {G : Type v} [AddCommGroup G] [Fintype G]
    (e : G → A ⊗[R] A) (he : CompleteOrthogonalIdempotents e)
    (hcoc : ∀ k, ∑ i, (c₁₂ R A).hom (e i) * (c₂₃ R A).hom (e (k - i)) = (c₁₃ R A).hom (e k)) :
    ∃ M : Submodule R (G → A),
      (∀ f : G → A, f ∈ M ↔ ∀ k, ∑ m, e m * (f (k - m) ⊗ₜ[R] 1) = 1 ⊗ₜ[R] f k) ∧
      IsBaseChange A M.subtype
```

### `Module.FaithfullyFlat.exists_submodule_isBaseChange_of_cocycle`

`Thm_Module_FaithfullyFlat_exists_submodule_isBaseChange_of_cocycle` — Effective faithfully flat descent for modules

```lean
theorem Module.FaithfullyFlat.exists_submodule_isBaseChange_of_cocycle
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    (N : Type u) [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (φ' : (ModuleCat.extendScalars (i₁ A B).hom).obj (ModuleCat.of B N) ≅
      (ModuleCat.extendScalars (i₂ A B).hom).obj (ModuleCat.of B N))
    (hcocycle : Cocycle (ModuleCat.of B N) φ'.hom) :
    ∃ M : Submodule A N,
      (∀ n : N, n ∈ M ↔
        φ'.hom (((1 : B ⊗[A] B) ⊗ₜ[B] n : (ModuleCat.extendScalars (i₁ A B).hom).obj (ModuleCat.of B N))) =
          ((1 : B ⊗[A] B) ⊗ₜ[B] n : (ModuleCat.extendScalars (i₂ A B).hom).obj (ModuleCat.of B N))) ∧
      IsBaseChange B M.subtype ∧
      (∃ θ : (ModuleCat.extendScalars (algebraMap A B)).obj (ModuleCat.of A M) ≅ ModuleCat.of B N,
        (∀ (b : B) (m : M),
          θ.hom ((b ⊗ₜ[A] m : (ModuleCat.extendScalars (algebraMap A B)).obj (ModuleCat.of A M))) = b • (m : N)) ∧
        (ModuleCat.extendScalars (i₁ A B).hom).map θ.hom ≫ φ'.hom =
          canonical A B (ModuleCat.of A M) ≫ (ModuleCat.extendScalars (i₂ A B).hom).map θ.hom) ∧
      (Module.Invertible B N → Module.Invertible A M)
```

### `Module.FaithfullyFlat.isBaseChange_eqLocus_of_descentDatum`

`Thm_Module_FaithfullyFlat_isBaseChange_eqLocus_of_descentDatum` — Effectivity of descent data for modules along a faithfully flat extension

```lean
theorem Module.FaithfullyFlat.isBaseChange_eqLocus_of_descentDatum
    {A : Type u} [CommRing A] (B : Type v) [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    {N : Type w} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (φ : TensorProduct A N B ≃ₗ[A] TensorProduct A B N)
    (hφ₁ : ∀ (b : B) (x : TensorProduct A N B), φ (b • x) = b • φ x)
    (hφ₂ : ∀ (b : B) (x : TensorProduct A N B),
      φ ((LinearMap.mulLeft A b).lTensor N x) = (DistribSMul.toLinearMap A N b).lTensor B (φ x))
    (hcocycle :
      (φ : TensorProduct A N B →ₗ[A] TensorProduct A B N).lTensor B ∘ₗ
          (TensorProduct.assoc A B N B).toLinearMap ∘ₗ
          (φ : TensorProduct A N B →ₗ[A] TensorProduct A B N).rTensor B =
        (TensorProduct.comm A N B).toLinearMap.lTensor B ∘ₗ
          (TensorProduct.assoc A B N B).toLinearMap ∘ₗ
          (φ : TensorProduct A N B →ₗ[A] TensorProduct A B N).rTensor B ∘ₗ
          (TensorProduct.assoc A N B B).symm.toLinearMap ∘ₗ
          (TensorProduct.comm A B B).toLinearMap.lTensor N ∘ₗ
          (TensorProduct.assoc A N B B).toLinearMap) :
    IsBaseChange B (LinearMap.eqLocus
        ((φ : TensorProduct A N B →ₗ[A] TensorProduct A B N) ∘ₗ (TensorProduct.mk A N B).flip 1)
        (TensorProduct.mk A B N 1)).subtype ∧
      ∀ (b b' : B) (m : N), φ (m ⊗ₜ[A] 1) = 1 ⊗ₜ[A] m →
        φ ((b • m) ⊗ₜ[A] b') = b ⊗ₜ[A] (b' • m)
```

### `Module.FaithfullyFlat.of_forall_isMaximal_exists_flat_algebra`

`Thm_Module_FaithfullyFlat_of_forall_isMaximal_exists_flat_algebra` — Faithful flatness from flat algebras reviving each maximal ideal

```lean
theorem Module.FaithfullyFlat.of_forall_isMaximal_exists_flat_algebra
    (B : Type u) [CommRing B] (H : Type v) [AddCommGroup H] [Module B H]
    (h : ∀ (M : Ideal B), M.IsMaximal →
      ∃ (C : Type u) (_ : CommRing C) (_ : Algebra B C) (_ : Module.Flat B C),
        M.map (algebraMap B C) ≠ ⊤ ∧ Module.FaithfullyFlat C (TensorProduct B C H)) :
    Module.FaithfullyFlat B H
```

### `Module.FaithfullyFlat.of_forall_isMaximal_exists_ringHom_field`

`Thm_Module_FaithfullyFlat_of_forall_isMaximal_exists_ringHom_field` — Flatness plus field-valued points over all maximal ideals gives faithful flatness

```lean
theorem Module.FaithfullyFlat.of_forall_isMaximal_exists_ringHom_field
    {B : Type u} {S : Type v} [CommRing B] [CommRing S] [Algebra B S] [Module.Flat B S]
    (h : ∀ m : Ideal B, m.IsMaximal →
      ∃ (K : Type w) (_ : Field K) (ψ : S →+* K), m ≤ RingHom.ker (ψ.comp (algebraMap B S))) :
    Module.FaithfullyFlat B S
```

### `Module.FaithfullyFlat.of_isAdicComplete_of_forall_pow_maximalIdeal`

`Thm_Module_FaithfullyFlat_of_isAdicComplete_of_forall_pow_maximalIdeal` — Faithful flatness of a complete local ring with the same adic quotients

```lean
theorem Module.FaithfullyFlat.of_isAdicComplete_of_forall_pow_maximalIdeal
    (R B : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing B] [IsLocalRing B] [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [Algebra R B] [IsLocalHom (algebraMap R B)]
    (hinj : ∀ (n : ℕ) (r : R), algebraMap R B r ∈ IsLocalRing.maximalIdeal B ^ n → r ∈ IsLocalRing.maximalIdeal R ^ n)
    (hsurj : ∀ (n : ℕ) (b : B), ∃ r : R, b - algebraMap R B r ∈ IsLocalRing.maximalIdeal B ^ n) :
    Module.FaithfullyFlat R B
```

### `Module.FaithfullyFlat.of_isLocalized_span`

`Thm_Module_FaithfullyFlat_of_isLocalized_span` — Faithful flatness is local on the base

```lean
theorem Module.FaithfullyFlat.of_isLocalized_span
    {R : Type*} [CommRing R] (s : Set R) (spn : Ideal.span s = ⊤)
    {M : Type*} [AddCommGroup M] [Module R M]
    (Rₛ : s → Type*) [∀ r : s, CommRing (Rₛ r)] [∀ r : s, Algebra R (Rₛ r)]
    [∀ r : s, IsLocalization.Away r.1 (Rₛ r)]
    (Mₛ : s → Type*) [∀ r : s, AddCommGroup (Mₛ r)] [∀ r : s, Module R (Mₛ r)] [∀ r : s, Module (Rₛ r) (Mₛ r)]
    [∀ r : s, IsScalarTower R (Rₛ r) (Mₛ r)]
    (g : ∀ r : s, M →ₗ[R] Mₛ r) [∀ r : s, IsLocalizedModule.Away r.1 (g r)]
    (H : ∀ r : s, Module.FaithfullyFlat (Rₛ r) (Mₛ r)) :
    Module.FaithfullyFlat R M
```

### `Module.FaithfullyFlat.pi_and_finitePresentation_pi_of_span_eq_top`

`Thm_Module_FaithfullyFlat_pi_and_finitePresentation_pi_of_span_eq_top` — Finite product over a Zariski cover is faithfully flat, finitely presented

```lean
theorem Module.FaithfullyFlat.pi_and_finitePresentation_pi_of_span_eq_top
    {S : Type} [CommRing S] {ι : Type} [Fintype ι] [DecidableEq ι] (g : ι → S) (hg : Ideal.span (Set.range g) = ⊤)
    (C : ι → Type) [∀ i, CommRing (C i)] [∀ i, Algebra S (C i)] [∀ i, Algebra (Localization.Away (g i)) (C i)]
    [∀ i, IsScalarTower S (Localization.Away (g i)) (C i)]
    (hff : ∀ i, Module.FaithfullyFlat (Localization.Away (g i)) (C i))
    (hfp : ∀ i, Algebra.FinitePresentation (Localization.Away (g i)) (C i)) :
    Module.FaithfullyFlat S (∀ i, C i) ∧ Algebra.FinitePresentation S (∀ i, C i)
```

### `Module.Finite.existsUnique_forall_mkQ_comp_eq_of_forall_factor_comp_eq`

`Thm_Module_Finite_existsUnique_forall_mkQ_comp_eq_of_forall_factor_comp_eq` — Compatible families M → N/Iⁿ⁺¹N come uniquely from widehatHom(M,N)

```lean
theorem Module.Finite.existsUnique_forall_mkQ_comp_eq_of_forall_factor_comp_eq
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Finite A M] [Module.Finite A N]
    (ψ : ∀ n : ℕ, M →ₗ[A] N ⧸ (I ^ (n + 1) • (⊤ : Submodule A N)))
    (hψ : ∀ n : ℕ,
      Submodule.factor (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))) ∘ₗ ψ (n + 1) = ψ n) :
    ∃! Φ : ∀ n : ℕ, (M →ₗ[A] N) ⧸ (I ^ (n + 1) • (⊤ : Submodule A (M →ₗ[A] N))),
      (∀ n : ℕ, Submodule.factor (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))) (Φ (n + 1)) = Φ n) ∧
      (∀ (n : ℕ) (g : M →ₗ[A] N), Submodule.Quotient.mk g = Φ n →
        (Submodule.mkQ (I ^ (n + 1) • (⊤ : Submodule A N))) ∘ₗ g = ψ n)
```

### `Module.Finite.exists_trace_end_eq_sum_dual_apply_of_projective`

`Thm_Module_Finite_exists_trace_end_eq_sum_dual_apply_of_projective` — Trace via dual families on finitely generated projective modules

```lean
theorem Module.Finite.exists_trace_end_eq_sum_dual_apply_of_projective
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Module.Projective A M] :
    ∃ τ : (M →ₗ[A] M) →ₗ[A] A,
      ∀ (n : ℕ) (x : Fin n → M) (φ : Fin n → (M →ₗ[A] A)),
        (∀ m : M, ∑ i, φ i m • x i = m) →
          ∀ f : M →ₗ[A] M, τ f = ∑ i, φ i (f (x i))
```

### `Module.Finite.of_algHom_equiv_isIdempotentElem_tensorProduct_of_etale_of_rankAtStalk_eq`

`Thm_Module_Finite_of_algHom_equiv_isIdempotentElem_tensorProduct_of_etale_of_rankAtStalk_eq` — Finiteness of an algebra representing idempotents of Q

```lean
theorem Module.Finite.of_algHom_equiv_isIdempotentElem_tensorProduct_of_etale_of_rankAtStalk_eq
    (R : Type u) [CommRing R] (Q : Type u) [CommRing Q] [Algebra R Q] [Module.Finite R Q] [Algebra.Etale R Q]
    (r : ℕ) (hr : ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) Q p = r)
    (C : Type u) [CommRing C] [Algebra R C]
    (η : ∀ (S : Type u) [CommRing S] [Algebra R S], (C →ₐ[R] S) ≃ {e : S ⊗[R] Q // IsIdempotentElem e})
    (hη : ∀ (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] (g : S →ₐ[R] T) (c : C →ₐ[R] S),
        ((η T (g.comp c) : {e : T ⊗[R] Q // IsIdempotentElem e}) : T ⊗[R] Q) =
          Algebra.TensorProduct.map g (AlgHom.id R Q) ((η S c : {e : S ⊗[R] Q // IsIdempotentElem e}) : S ⊗[R] Q)) :
    Module.Finite R C
```

### `Module.Finite.of_finite_quotient_map_maximalIdeal`

`Thm_Module_Finite_of_finite_quotient_map_maximalIdeal` — Finiteness over a precomplete local ring from the special fibre

```lean
theorem Module.Finite.of_finite_quotient_map_maximalIdeal
    {𝒪 : Type u} {A : Type v} [CommRing 𝒪] [IsLocalRing 𝒪] [IsPrecomplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    [CommRing A] [Algebra 𝒪 A] [IsLocalRing A] [IsHausdorff (IsLocalRing.maximalIdeal A) A]
    [IsLocalHom (algebraMap 𝒪 A)]
    (hfin : Module.Finite 𝒪 (A ⧸ (IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A))) :
    Module.Finite 𝒪 A
```

### `Module.Finite.of_isAdicComplete_of_isHausdorff_of_quotient`

`Thm_Module_Finite_of_isAdicComplete_of_isHausdorff_of_quotient` — Complete Nakayama lemma for adically Hausdorff modules

```lean
theorem Module.Finite.of_isAdicComplete_of_isHausdorff_of_quotient
    {R : Type u} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (M : Type v) [AddCommGroup M] [Module R M] [IsHausdorff I M]
    (h : Module.Finite R (M ⧸ (I • ⊤ : Submodule R M))) :
    Module.Finite R M
```

### `Module.Finite.of_ker_le_range_of_isNoetherianRing`

`Thm_Module_Finite_of_ker_le_range_of_isNoetherianRing` — Finiteness sandwich over a Noetherian ring

```lean
theorem Module.Finite.of_ker_le_range_of_isNoetherianRing {R : Type*} [CommRing R] [IsNoetherianRing R] {M N₁ N₂ : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂] [Module.Finite R N₁] [Module.Finite R N₂] (α : N₁ →ₗ[R] M) (β : M →ₗ[R] N₂) (h : LinearMap.ker β ≤ LinearMap.range α) : Module.Finite R M
```

### `Module.Finite.quotient_of_isUnit_leadingCoeff_of_mem`

`Thm_Module_Finite_quotient_of_isUnit_leadingCoeff_of_mem` — Finiteness over R of A/I when I contains a polynomial with unit leading coefficient

```lean
theorem Module.Finite.quotient_of_isUnit_leadingCoeff_of_mem
    (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A] [Algebra R[X] A]
    [IsScalarTower R R[X] A] [Module.Finite R[X] A]
    (N : R[X]) (hN : IsUnit N.leadingCoeff) (I : Ideal A) (hNI : algebraMap R[X] A N ∈ I) :
    Module.Finite R (A ⧸ I)
```

### `Module.FinitePresentation.exists_notMem_basis_localizedModule_of_basis_residueField_tensor`

`Thm_Module_FinitePresentation_exists_notMem_basis_localizedModule_of_basis_residueField_tensor` — Spreading a fibre basis to a basic open neighbourhood

```lean
theorem Module.FinitePresentation.exists_notMem_basis_localizedModule_of_basis_residueField_tensor
    {T : Type u} [CommRing T] {M : Type u} [AddCommGroup M] [Module T M] [Module.FinitePresentation T M]
    (p : Ideal T) [hp : p.IsPrime] (hfree : (⟨p, hp⟩ : PrimeSpectrum T) ∈ Module.freeLocus T M)
    {ι : Type} [Finite ι] (m : ι → M)
    (b : Module.Basis ι p.ResidueField (p.ResidueField ⊗[T] M)) (hb : ∀ i, b i = (1 : p.ResidueField) ⊗ₜ[T] m i) :
    ∃ (t : T) (_ : t ∉ p)
      (b' : Module.Basis ι (Localization.Away t) (LocalizedModule (Submonoid.powers t) M)),
      ∀ i, b' i = LocalizedModule.mkLinearMap (Submonoid.powers t) M (m i)
```

### `Module.Flat.bijective_kerBaseChangeHom_and_nonempty_homology_baseChange_linearEquiv`

`Thm_Module_Flat_bijective_kerBaseChangeHom_and_nonempty_homology_baseChange_linearEquiv` — Flat base change commutes with kernels and homology

```lean
theorem Module.Flat.bijective_kerBaseChangeHom_and_nonempty_homology_baseChange_linearEquiv
    {R : Type u} [CommRing R] (T : Type u) [CommRing T] [Algebra R T] [Module.Flat R T]
    {M N P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hfg : g ∘ₗ f = 0) :
    letI : AddCommGroup ↥(LinearMap.ker (g.baseChange T)) :=
      Submodule.addCommGroup (M := T ⊗[R] N) (LinearMap.ker (g.baseChange T))
    Function.Bijective (TwoChartCech.kerBaseChangeHom g T) ∧
    Nonempty
      (T ⊗[R] (LinearMap.ker g ⧸ (LinearMap.range f).comap (LinearMap.ker g).subtype) ≃ₗ[T]
        (↥(LinearMap.ker (g.baseChange T)) ⧸
          (LinearMap.range (f.baseChange T)).comap (LinearMap.ker (g.baseChange T)).subtype)) ∧
    ((LinearMap.ker (g.baseChange T) ≤ LinearMap.range (f.baseChange T)) ↔
        Subsingleton (T ⊗[R] (LinearMap.ker g ⧸ (LinearMap.range f).comap (LinearMap.ker g).subtype))) ∧
    (Module.Finite R (LinearMap.ker g ⧸ (LinearMap.range f).comap (LinearMap.ker g).subtype) →
        Module.Finite T (↥(LinearMap.ker (g.baseChange T)) ⧸
          (LinearMap.range (f.baseChange T)).comap (LinearMap.ker (g.baseChange T)).subtype))
```

### `Module.Flat.exists_fg_subalgebra_flat_localization_tensorProduct`

`Thm_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct` — Descent of flatness at a prime to a finitely generated subalgebra

```lean
theorem Module.Flat.exists_fg_subalgebra_flat_localization_tensorProduct
    {R₀ R B₀ : Type*} [CommRing R₀] [CommRing R] [CommRing B₀]
    [Algebra R₀ R] [Algebra R₀ B₀] [IsNoetherianRing R₀] [Algebra.FiniteType R₀ B₀]
    (P : Ideal (R ⊗[R₀] B₀)) [P.IsPrime]
    [Module.Flat R (Localization.AtPrime P)] :
    ∃ R₁ : Subalgebra R₀ R, R₁.FG ∧
      Module.Flat R₁ (Localization.AtPrime
        (P.comap (Algebra.TensorProduct.map R₁.val (AlgHom.id R₀ B₀)).toRingHom))
```

### `Module.Flat.exists_fg_subalgebra_flat_tensorProduct`

`Thm_Module_Flat_exists_fg_subalgebra_flat_tensorProduct` — Flatness descends to a finitely generated subalgebra of the base

```lean
theorem Module.Flat.exists_fg_subalgebra_flat_tensorProduct
    {R₀ R B₀ : Type*} [CommRing R₀] [CommRing R] [CommRing B₀]
    [Algebra R₀ R] [Algebra R₀ B₀] [Algebra.FinitePresentation R₀ B₀]
    [Module.Flat R (R ⊗[R₀] B₀)] (s : Finset R) :
    ∃ R₁ : Subalgebra R₀ R, R₁.FG ∧ (↑s : Set R) ⊆ R₁ ∧ Module.Flat R₁ (R₁ ⊗[R₀] B₀)
```

### `Module.Flat.exists_forall_isUnit_ker_baseChange_le_range_of_ker_baseChange_residueField_le_range`

`Thm_Module_Flat_exists_forall_isUnit_ker_baseChange_le_range_of_ker_baseChange_residueField_le_range` — Fibrewise exactness of a bounded flat complex spreads out

```lean
theorem Module.Flat.exists_forall_isUnit_ker_baseChange_le_range_of_ker_baseChange_residueField_le_range
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbd : ∀ i, n ≤ i → Subsingleton (C i))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype))
    (𝔭 : PrimeSpectrum R)
    (hfib : ∀ i : ℕ,
      LinearMap.ker ((d (i + 1)).baseChange 𝔭.asIdeal.ResidueField) ≤
        LinearMap.range ((d i).baseChange 𝔭.asIdeal.ResidueField)) :
    ∃ g : R, g ∉ 𝔭.asIdeal ∧
      ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalization.Away g S],
        ∀ i : ℕ, LinearMap.ker ((d (i + 1)).baseChange S) ≤ LinearMap.range ((d i).baseChange S)
```

### `Module.Flat.exists_forall_isUnit_projective_ker_baseChange_of_ker_baseChange_residueField_le_range`

`Thm_Module_Flat_exists_forall_isUnit_projective_ker_baseChange_of_ker_baseChange_residueField_le_range` — Universal acyclicity and projectivity near a good fibre

```lean
theorem Module.Flat.exists_forall_isUnit_projective_ker_baseChange_of_ker_baseChange_residueField_le_range
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbd : ∀ i, n ≤ i → Subsingleton (C i))
    (hfin0 : Module.Finite R (LinearMap.ker (d 0)))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype))
    (𝔭 : PrimeSpectrum R)
    (hfib : ∀ i : ℕ,
      LinearMap.ker ((d (i + 1)).baseChange 𝔭.asIdeal.ResidueField) ≤
        LinearMap.range ((d i).baseChange 𝔭.asIdeal.ResidueField)) :
    ∃ g : R, g ∉ 𝔭.asIdeal ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A], IsUnit (algebraMap R A g) →
        Module.Finite A (LinearMap.ker ((d 0).baseChange A)) ∧
        Module.Projective A (LinearMap.ker ((d 0).baseChange A)) ∧
        (∀ i : ℕ, LinearMap.ker ((d (i + 1)).baseChange A) ≤ LinearMap.range ((d i).baseChange A)) ∧
        Function.Bijective (TwoChartCech.kerBaseChangeHom (d 0) A) ∧
        (∀ 𝔮 : PrimeSpectrum A,
          Module.rankAtStalk (LinearMap.ker ((d 0).baseChange A)) 𝔮 =
            Module.finrank 𝔭.asIdeal.ResidueField (LinearMap.ker ((d 0).baseChange 𝔭.asIdeal.ResidueField)))
```

### `Module.Flat.exists_mem_smul_top_map_eq_of_ker_baseChange_le_range`

`Thm_Module_Flat_exists_mem_smul_top_map_eq_of_ker_baseChange_le_range` — Cocycles in I C₁ come from I C₀

```lean
theorem Module.Flat.exists_mem_smul_top_map_eq_of_ker_baseChange_le_range
    {R : Type u} [CommRing R] (k : Type u) [Field k] [Algebra R k] (hk : Function.Surjective (algebraMap R k))
    (I : Ideal R) (hI : I * RingHom.ker (algebraMap R k) = ⊥)
    {C₀ C₁ C₂ : Type u} [AddCommGroup C₀] [Module R C₀] [AddCommGroup C₁] [Module R C₁] [AddCommGroup C₂] [Module R C₂]
    [Module.Flat R C₁] [Module.Flat R C₂]
    (d₀ : C₀ →ₗ[R] C₁) (d₁ : C₁ →ₗ[R] C₂)
    (hex : LinearMap.ker (d₁.baseChange k) ≤ LinearMap.range (d₀.baseChange k))
    (c : C₁) (hc : c ∈ I • (⊤ : Submodule R C₁)) (hdc : d₁ c = 0) :
    ∃ b ∈ I • (⊤ : Submodule R C₀), d₀ b = c
```

### `Module.Flat.exists_ne_zero_flat_localization_tensorProduct`

`Thm_Module_Flat_exists_ne_zero_flat_localization_tensorProduct` — Generic flatness over a Noetherian domain

```lean
theorem Module.Flat.exists_ne_zero_flat_localization_tensorProduct
    {A B M : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [Module.Finite B M] :
    ∃ a : A, a ≠ 0 ∧
      Module.Flat A (Localization (Submonoid.powers (algebraMap A B a)) ⊗[B] M)
```

### `Module.Flat.finite_free_finrank_quotient_tensorProduct_of_map_maximalIdeal_eq`

`Thm_Module_Flat_finite_free_finrank_quotient_tensorProduct_of_map_maximalIdeal_eq` — Truncations of a flat unramified local extension are finite free

```lean
theorem Module.Flat.finite_free_finrank_quotient_tensorProduct_of_map_maximalIdeal_eq
    (V : Type) [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    (D : Type) [CommRing D] [IsLocalRing D] [Algebra V D] [IsLocalHom (algebraMap V D)] [Module.Flat V D]
    (hVD : (maximalIdeal V).map (algebraMap V D) = maximalIdeal D)
    [Module.Finite (ResidueField V) (ResidueField D)]
    (m : ℕ) (hm : 0 < m) :
    Module.Finite (V ⧸ maximalIdeal V ^ m) ((V ⧸ maximalIdeal V ^ m) ⊗[V] D) ∧ Module.Free (V ⧸ maximalIdeal V ^ m) ((V ⧸ maximalIdeal V ^ m) ⊗[V] D) ∧
      Module.finrank (V ⧸ maximalIdeal V ^ m) ((V ⧸ maximalIdeal V ^ m) ⊗[V] D) = Module.finrank (ResidueField V) (ResidueField D)
```

### `Module.Flat.flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range`

`Thm_Module_Flat_flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range` — Bounded flat complexes: flatness of ker d⁰ and base change

```lean
theorem Module.Flat.flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range
    {R : Type u} [CommRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbd : ∀ i, n ≤ i → Subsingleton (C i))
    (hex : ∀ i : ℕ, LinearMap.ker (d (i + 1)) ≤ LinearMap.range (d i)) :
    Module.Flat R (LinearMap.ker (d 0)) ∧
      (∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Bijective (TwoChartCech.kerBaseChangeHom (d 0) A)) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A] (i : ℕ),
        LinearMap.ker ((d (i + 1)).baseChange A) ≤ LinearMap.range ((d i).baseChange A)
```

### `Module.Flat.isOpen_setOf_flat_localization_atPrime`

`Thm_Module_Flat_isOpen_setOf_flat_localization_atPrime` — Openness of the flat locus for finite type algebras

```lean
theorem Module.Flat.isOpen_setOf_flat_localization_atPrime
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [Algebra.FiniteType A B] :
    IsOpen {Q : PrimeSpectrum B | Module.Flat A (Localization.AtPrime Q.asIdeal)}
```

### `Module.Flat.ker_baseChange_eq_bot_and_ker_le_range_of_flat_of_exact`

`Thm_Module_Flat_ker_baseChange_eq_bot_and_ker_le_range_of_flat_of_exact` — Base change of a bounded exact complex of flat modules

```lean
theorem Module.Flat.ker_baseChange_eq_bot_and_ker_le_range_of_flat_of_exact
    {R : Type u} [CommRing R] (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)]
    [∀ i, Module.Flat R (C i)] (d : ∀ i, C i →ₗ[R] C (i + 1))
    (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0) (n : ℕ) (hbd : ∀ i, n ≤ i → Subsingleton (C i))
    (h0 : LinearMap.ker (d 0) = ⊥) (hex : ∀ i, LinearMap.ker (d (i + 1)) ≤ LinearMap.range (d i))
    (A : Type u) [CommRing A] [Algebra R A] :
    LinearMap.ker ((d 0).baseChange A) = ⊥ ∧
      ∀ i, LinearMap.ker ((d (i + 1)).baseChange A) ≤ LinearMap.range ((d i).baseChange A)
```

### `Module.Flat.ker_baseChange_le_range_of_forall_ker_baseChange_residueField_le_range`

`Thm_Module_Flat_ker_baseChange_le_range_of_forall_ker_baseChange_residueField_le_range` — Exactness over a local ring from exactness on the residue field

```lean
theorem Module.Flat.ker_baseChange_le_range_of_forall_ker_baseChange_residueField_le_range
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbd : ∀ i, n ≤ i → Subsingleton (C i))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype))
    (hfib : ∀ i : ℕ,
      LinearMap.ker ((d (i + 1)).baseChange (IsLocalRing.ResidueField R)) ≤
        LinearMap.range ((d i).baseChange (IsLocalRing.ResidueField R))) :
    (∀ i : ℕ, LinearMap.ker (d (i + 1)) ≤ LinearMap.range (d i)) ∧
      ∀ (K : Type u) [Field K] [Algebra R K] (i : ℕ),
        LinearMap.ker ((d (i + 1)).baseChange K) ≤ LinearMap.range ((d i).baseChange K)
```

### `Module.Flat.ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range`

`Thm_Module_Flat_ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range` — Fibrewise exactness implies exactness for bounded flat complexes

```lean
theorem Module.Flat.ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbd : ∀ i, n ≤ i → Subsingleton (C i))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype))
    (hfib : ∀ (𝔪 : Ideal R) [𝔪.IsMaximal] (i : ℕ),
      LinearMap.ker ((d (i + 1)).baseChange (R ⧸ 𝔪)) ≤ LinearMap.range ((d i).baseChange (R ⧸ 𝔪))) :
    ∀ i : ℕ, LinearMap.ker (d (i + 1)) ≤ LinearMap.range (d i)
```

### `Module.Flat.ker_of_surjective_of_flat`

`Thm_Module_Flat_ker_of_surjective_of_flat` — Kernel of a surjection of flat modules is flat

```lean
theorem Module.Flat.ker_of_surjective_of_flat
    {R : Type u} [CommRing R] {M P : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    [Module.Flat R M] [Module.Flat R P] (g : M →ₗ[R] P) (hg : Function.Surjective g) :
    Module.Flat R (LinearMap.ker g)
```

### `Module.Flat.lTensor_injective_of_exact_of_surjective_of_flat`

`Thm_Module_Flat_lTensor_injective_of_exact_of_surjective_of_flat` — Left exactness after tensoring when the cokernel is flat

```lean
theorem Module.Flat.lTensor_injective_of_exact_of_surjective_of_flat
    {R : Type u} [CommRing R] {N M P : Type u}
    [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    (f : N →ₗ[R] M) (g : M →ₗ[R] P) (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) [Module.Flat R P]
    (A : Type u) [AddCommGroup A] [Module R A] :
    Function.Injective (f.lTensor A)
```

### `Module.Flat.mem_nonZeroDivisors_and_flat_quotient_span_of_forall_isAlgClosed`

`Thm_Module_Flat_mem_nonZeroDivisors_and_flat_quotient_span_of_forall_isAlgClosed` — Nonzerodivisor on all geometric fibres: flatness of B/gB

```lean
theorem Module.Flat.mem_nonZeroDivisors_and_flat_quotient_span_of_forall_isAlgClosed
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing B]
    [Module.Flat A B] (g : B)
    (hg : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra A K],
      (g ⊗ₜ[A] (1 : K)) ∈ nonZeroDivisors (B ⊗[A] K)) :
    g ∈ nonZeroDivisors B ∧ Module.Flat A (B ⧸ Ideal.span {g})
```

### `Module.Flat.of_finitePresentation_of_forall_flat_residueField_tensorProduct`

`Thm_Module_Flat_of_finitePresentation_of_forall_flat_residueField_tensorProduct` — Fibrewise criterion of flatness over a general base, affine form

```lean
theorem Module.Flat.of_finitePresentation_of_forall_flat_residueField_tensorProduct
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.FinitePresentation R A] [Algebra.FinitePresentation R B] [Module.Flat R B]
    (hfib : ∀ (p : Ideal R) [p.IsPrime],
      (Algebra.TensorProduct.map (AlgHom.id p.ResidueField p.ResidueField)
        (IsScalarTower.toAlgHom R A B)).toRingHom.Flat) :
    Module.Flat A B
```

### `Module.Flat.of_finite_of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_eq`

`Thm_Module_Flat_of_finite_of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_eq` — Miracle flatness for finite local maps of regular local rings

```lean
theorem Module.Flat.of_finite_of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_eq
    (R S : Type*) [CommRing R] [CommRing S] [IsNoetherianRing R]
    [IsRegularLocalRing R] [IsRegularLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Finite R S]
    (hdim : ringKrullDim S = ringKrullDim R) :
    Module.Flat R S
```

### `Module.Flat.of_flat_of_faithfullyFlat_right`

`Thm_Module_Flat_of_flat_of_faithfullyFlat_right` — Flatness descends along a faithfully flat ring extension

```lean
theorem Module.Flat.of_flat_of_faithfullyFlat_right (R S T : Type*) [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Module.FaithfullyFlat S T] [Module.Flat R T] : Module.Flat R S
```

### `Module.Flat.of_forall_flat_quotient_pow_tensor_of_map_le_jacobson`

`Thm_Module_Flat_of_forall_flat_quotient_pow_tensor_of_map_le_jacobson` — Flatness from flatness modulo all powers of I

```lean
theorem Module.Flat.of_forall_flat_quotient_pow_tensor_of_map_le_jacobson
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A] [IsNoetherianRing B]
    (I : Ideal A) (hI : I.map (algebraMap A B) ≤ (⊥ : Ideal B).jacobson)
    (h : ∀ n : ℕ, Module.Flat (A ⧸ I ^ n) ((A ⧸ I ^ n) ⊗[A] B)) :
    Module.Flat A B
```

### `Module.Flat.of_forall_flat_residueField_tensorProduct_of_isPrincipalIdealRing`

`Thm_Module_Flat_of_forall_flat_residueField_tensorProduct_of_isPrincipalIdealRing` — Fibrewise flatness criterion over a principal ideal domain

```lean
theorem Module.Flat.of_forall_flat_residueField_tensorProduct_of_isPrincipalIdealRing
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {A : Type v} [CommRing A] [Algebra R A] {B : Type w} [CommRing B] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B] [Module.Flat R A] [Module.Flat R B]
    (hfib : ∀ (p : Ideal R) [p.IsPrime],
      (Algebra.TensorProduct.map (AlgHom.id p.ResidueField p.ResidueField)
        (IsScalarTower.toAlgHom R A B)).toRingHom.Flat) :
    Module.Flat A B
```

### `Module.Flat.of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero`

`Thm_Module_Flat_of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero` — Miracle flatness for a local map of regular local rings

```lean
theorem Module.Flat.of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero
    (R S : Type*) [CommRing R] [CommRing S] [IsNoetherianRing S]
    [IsRegularLocalRing R] [IsRegularLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)]
    (hfib : ringKrullDim (S ⧸ (maximalIdeal R).map (algebraMap R S)) = 0)
    (hdim : ringKrullDim S = ringKrullDim R) :
    Module.Flat R S
```

### `Module.Flat.of_module_fractionRing_of_isReduced_baseChange`

`Thm_Module_Flat_of_module_fractionRing_of_isReduced_baseChange` — Flatness over a finite flat algebra with reduced generic fibre

```lean
theorem Module.Flat.of_module_fractionRing_of_isReduced_baseChange
    (R : Type u) [CommRing R] [IsDomain R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (B₁ : Type w) [CommRing B₁] [Algebra R B₁] [Module.Finite R B₁] [Module.Flat R B₁]
    [IsReduced (TensorProduct R K B₁)]
    (M : Type x) [AddCommGroup M] [Module R M] [Module K M] [Module B₁ M]
    [IsScalarTower R K M] [IsScalarTower R B₁ M] [SMulCommClass K B₁ M] :
    Module.Flat B₁ M
```

### `Module.Flat.projective_ker_and_bijective_kerBaseChangeHom_of_forall_ker_baseChange_le_range`

`Thm_Module_Flat_projective_ker_and_bijective_kerBaseChangeHom_of_forall_ker_baseChange_le_range` — Base change for a bounded complex of flat modules

```lean
theorem Module.Flat.projective_ker_and_bijective_kerBaseChangeHom_of_forall_ker_baseChange_le_range
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbd : ∀ i, n ≤ i → Subsingleton (C i))
    (hfin0 : Module.Finite R (LinearMap.ker (d 0)))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype))
    (hfib : ∀ (K : Type u) [Field K] [Algebra R K] (i : ℕ),
      LinearMap.ker ((d (i + 1)).baseChange K) ≤ LinearMap.range ((d i).baseChange K)) :
    Module.Projective R (LinearMap.ker (d 0)) ∧
      (∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Bijective (TwoChartCech.kerBaseChangeHom (d 0) A)) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A] (i : ℕ),
        LinearMap.ker ((d (i + 1)).baseChange A) ≤ LinearMap.range ((d i).baseChange A)
```

### `Module.Flat.projective_ker_baseChange_of_isLocalizationAway_of_ker_baseChange_le_range`

`Thm_Module_Flat_projective_ker_baseChange_of_isLocalizationAway_of_ker_baseChange_le_range` — Base change of ker d⁰ where g becomes invertible

```lean
theorem Module.Flat.projective_ker_baseChange_of_isLocalizationAway_of_ker_baseChange_le_range
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbd : ∀ i, n ≤ i → Subsingleton (C i))
    (hfin0 : Module.Finite R (LinearMap.ker (d 0)))
    (g : R) (S : Type u) [CommRing S] [Algebra R S] [IsLocalization.Away g S]
    (hex : ∀ i : ℕ, LinearMap.ker ((d (i + 1)).baseChange S) ≤ LinearMap.range ((d i).baseChange S))
    (A : Type u) [CommRing A] [Algebra R A] (hA : IsUnit (algebraMap R A g)) :
    Module.Finite A (LinearMap.ker ((d 0).baseChange A)) ∧
      Module.Projective A (LinearMap.ker ((d 0).baseChange A)) ∧
      (∀ i : ℕ, LinearMap.ker ((d (i + 1)).baseChange A) ≤ LinearMap.range ((d i).baseChange A)) ∧
      Function.Bijective (TwoChartCech.kerBaseChangeHom (d 0) A)
```

### `Module.Free.of_surjective_of_smul_eq`

`Thm_Module_Free_of_surjective_of_smul_eq` — Freeness descends along a surjective ring map compatible with scalars

```lean
theorem Module.Free.of_surjective_of_smul_eq {S T N : Type*} [CommRing S] [Ring T] [AddCommGroup N] [Module S N] [Module T N] [Module.Free S N] (g : S →+* T) (hg : ∀ (s : S) (n : N), g s • n = s • n) (hsurj : Function.Surjective g) : Module.Free T N
```

### `Module.Invertible.bijective_localizedModule_map_of_not_range_le`

`Thm_Module_Invertible_bijective_localizedModule_map_of_not_range_le` — Bijectivity at a prime of a map of invertible modules

```lean
theorem Module.Invertible.bijective_localizedModule_map_of_not_range_le
    {R : Type*} [CommRing R] {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [Module.Invertible R P] [Module.Invertible R Q] (f : P →ₗ[R] Q) (x : PrimeSpectrum R)
    (hx : ¬ LinearMap.range f ≤ x.asIdeal • (⊤ : Submodule R Q)) :
    Function.Bijective (LocalizedModule.map x.asIdeal.primeCompl f)
```

### `Module.Invertible.exists_notMem_and_forall_exists_pow_smul_eq_smul`

`Thm_Module_Invertible_exists_notMem_and_forall_exists_pow_smul_eq_smul` — Invertible modules are cyclic over a basic open set

```lean
theorem Module.Invertible.exists_notMem_and_forall_exists_pow_smul_eq_smul
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] [Module.Invertible R M]
    (p : Ideal R) [p.IsPrime] :
    ∃ t : R, t ∉ p ∧ ∃ m₀ : M, ∀ m : M, ∃ (n : ℕ) (r : R), t ^ n • m = r • m₀
```

### `Module.Invertible.of_invertible_baseChange_of_surjective_of_isNilpotent_ker`

`Thm_Module_Invertible_of_invertible_baseChange_of_surjective_of_isNilpotent_ker` — Invertibility descends along a nilpotent surjection

```lean
theorem Module.Invertible.of_invertible_baseChange_of_surjective_of_isNilpotent_ker
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (hπ : Function.Surjective (algebraMap R S)) (hker : IsNilpotent (RingHom.ker (algebraMap R S)))
    (P : Type w) [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
    (h : Module.Invertible S (S ⊗[R] P)) : Module.Invertible R P
```

### `Module.Invertible.of_invertible_tensorProduct_of_faithfullyFlat`

`Thm_Module_Invertible_of_invertible_tensorProduct_of_faithfullyFlat` — Faithfully flat descent of invertibility of modules

```lean
theorem Module.Invertible.of_invertible_tensorProduct_of_faithfullyFlat
    {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    {M : Type w} [AddCommGroup M] [Module R M]
    [Module.Invertible S (TensorProduct R S M)] :
    Module.Invertible R M
```

### `Module.Invertible.of_isLocalizedModule_of_span_eq_top`

`Thm_Module_Invertible_of_isLocalizedModule_of_span_eq_top` — Invertibility of a module is Zariski-local

```lean
theorem Module.Invertible.of_isLocalizedModule_of_span_eq_top
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (s : Set R) (hs : Ideal.span s = ⊤)
    {Mₚ : ∀ (_ : s), Type*} [∀ (g : s), AddCommGroup (Mₚ g)] [∀ (g : s), Module R (Mₚ g)]
    {Rₚ : ∀ (_ : s), Type*} [∀ (g : s), CommRing (Rₚ g)] [∀ (g : s), Algebra R (Rₚ g)]
    [∀ (g : s), IsLocalization.Away g.val (Rₚ g)]
    [∀ (g : s), Module (Rₚ g) (Mₚ g)] [∀ (g : s), IsScalarTower R (Rₚ g) (Mₚ g)]
    (ϕ : ∀ (g : s), M →ₗ[R] Mₚ g) [∀ (g : s), IsLocalizedModule (Submonoid.powers g.val) (ϕ g)]
    (h : ∀ (g : s), Module.Invertible (Rₚ g) (Mₚ g)) :
    Module.Invertible R M
```

### `Module.Invertible.of_isLocalizedModule_of_span_range_eq_top`

`Thm_Module_Invertible_of_isLocalizedModule_of_span_range_eq_top` — Invertibility is local on a finite basic-open cover

```lean
theorem Module.Invertible.of_isLocalizedModule_of_span_range_eq_top
    {B : Type u} [CommRing B] {k : ℕ} (f : Fin k → B) (hf : Ideal.span (Set.range f) = ⊤)
    (N : Type u) [AddCommGroup N] [Module B N]
    (M : Fin k → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module B (M i)]
    (R : Fin k → Type u) [∀ i, CommRing (R i)] [∀ i, Algebra B (R i)] [∀ i, IsLocalization.Away (f i) (R i)]
    [∀ i, Module (R i) (M i)] [∀ i, IsScalarTower B (R i) (M i)]
    (π : ∀ i, N →ₗ[B] M i) (hπ : ∀ i, IsLocalizedModule (Submonoid.powers (f i)) (π i))
    (h : ∀ i, Module.Invertible (R i) (M i)) :
    Module.Invertible B N
```

### `Module.Invertible.of_isLocalizedModule_span`

`Thm_Module_Invertible_of_isLocalizedModule_span` — Invertibility of a module is Zariski-local

```lean
theorem Module.Invertible.of_isLocalizedModule_span
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (s : Set R) (hs : Ideal.span s = ⊤)
    (Rₚ : ↥s → Type*) [∀ r : ↥s, CommRing (Rₚ r)] [∀ r : ↥s, Algebra R (Rₚ r)]
    [∀ r : ↥s, IsLocalization.Away (r.1 : R) (Rₚ r)]
    (Mₚ : ↥s → Type*) [∀ r : ↥s, AddCommGroup (Mₚ r)] [∀ r : ↥s, Module R (Mₚ r)] [∀ r : ↥s, Module (Rₚ r) (Mₚ r)]
    [∀ r : ↥s, IsScalarTower R (Rₚ r) (Mₚ r)]
    (φ : ∀ r : ↥s, M →ₗ[R] Mₚ r) [∀ r : ↥s, IsLocalizedModule (Submonoid.powers (r.1 : R)) (φ r)]
    (H : ∀ r : ↥s, Module.Invertible (Rₚ r) (Mₚ r)) : Module.Invertible R M
```

### `Module.Invertible.of_localization_maximal`

`Thm_Module_Invertible_of_localization_maximal` — Invertibility of a finitely presented module is local

```lean
theorem Module.Invertible.of_localization_maximal
    {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
    (H : ∀ (P : Ideal R) [P.IsMaximal], Module.Invertible (Localization.AtPrime P) (LocalizedModule P.primeCompl M)) :
    Module.Invertible R M
```

### `Module.Invertible.of_projective_of_forall_finrank_eq_one`

`Thm_Module_Invertible_of_projective_of_forall_finrank_eq_one` — Finitely generated projectives of rank one at all fields are invertible

```lean
theorem Module.Invertible.of_projective_of_forall_finrank_eq_one
    {A : Type u} [CommRing A] (P : Type v) [AddCommGroup P] [Module A P]
    [Module.Finite A P] [Module.Projective A P]
    (h : ∀ (K : Type u) [Field K] [Algebra A K], Module.finrank K (TensorProduct A K P) = 1) :
    Module.Invertible A P
```

### `Module.Invertible.of_ringEquiv`

`Thm_Module_Invertible_of_ringEquiv` — Invertibility of a module transports along a ring isomorphism

```lean
theorem Module.Invertible.of_ringEquiv
    {R R' : Type u} [CommRing R] [CommRing R'] (σ : R ≃+* R')
    (M : Type v) [AddCommGroup M] [Module R' M] [Module.Invertible R' M]
    [Module R M] (hσ : ∀ (r : R) (m : M), r • m = σ r • m) :
    Module.Invertible R M
```

### `Module.Invertible.quotient_span_rTensor_mem_and_span_image_eq_of_valuationRing`

`Thm_Module_Invertible_quotient_span_rTensor_mem_and_span_image_eq_of_valuationRing` — Saturation over a valuation ring of a co-invertible subspace

```lean
theorem Module.Invertible.quotient_span_rTensor_mem_and_span_image_eq_of_valuationRing
    {𝒪 : Type u} [CommRing 𝒪]
    (V : Type v) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra 𝒪 V]
    (L : Type v) [Field L] [Algebra 𝒪 L] [Algebra V L] [IsScalarTower 𝒪 V L] [IsFractionRing V L]
    (M : Type w) [AddCommGroup M] [Module 𝒪 M] [Module.Finite 𝒪 M]
    (N : Submodule L (L ⊗[𝒪] M)) (hN : Module.Invertible L ((L ⊗[𝒪] M) ⧸ N)) :
    Module.Invertible V ((V ⊗[𝒪] M) ⧸ Submodule.span V
        {x : V ⊗[𝒪] M | LinearMap.rTensor M (IsScalarTower.toAlgHom 𝒪 V L).toLinearMap x ∈ N}) ∧
      Submodule.span L (LinearMap.rTensor M (IsScalarTower.toAlgHom 𝒪 V L).toLinearMap ''
        (Submodule.span V {x : V ⊗[𝒪] M | LinearMap.rTensor M (IsScalarTower.toAlgHom 𝒪 V L).toLinearMap x ∈ N} :
          Set (V ⊗[𝒪] M))) = N
```

### `Module.Invertible.range_le_smul_top_or_of_comp_eq_smul`

`Thm_Module_Invertible_range_le_smul_top_or_of_comp_eq_smul` — Composite equal to a scalar in 𝔭: one image lies in 𝔭

```lean
theorem Module.Invertible.range_le_smul_top_or_of_comp_eq_smul
    {R : Type*} [CommRing R] {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [Module.Invertible R P] [Module.Invertible R Q] (f : P →ₗ[R] Q) (g : Q →ₗ[R] P) (a : R)
    (hfg : g ∘ₗ f = a • LinearMap.id) (x : PrimeSpectrum R) (ha : a ∈ x.asIdeal) :
    LinearMap.range f ≤ x.asIdeal • (⊤ : Submodule R Q) ∨ LinearMap.range g ≤ x.asIdeal • (⊤ : Submodule R P)
```

### `Module.IsDirectLimit.exists_invertible_linearEquiv_baseChange`

`Thm_Module_IsDirectLimit_exists_invertible_linearEquiv_baseChange` — Invertible modules over a directed colimit descend to a stage

```lean
theorem Module.IsDirectLimit.exists_invertible_linearEquiv_baseChange
    {ι : Type v} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {B₀ : Type u} [CommRing B₀]
    (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra B₀ (B i)]
    (τ : ∀ i j, i ≤ j → B i →ₐ[B₀] B j) [DirectedSystem B (fun i j h => τ i j h)]
    (Bω : Type u) [CommRing Bω] [Algebra B₀ Bω] (g : ∀ i, B i →ₐ[B₀] Bω)
    (hg : ∀ i j (h : i ≤ j), (g j).comp (τ i j h) = g i)
    (hsurj : ∀ b : Bω, ∃ i x, g i x = b)
    (hzero : ∀ i (x : B i), g i x = 0 → ∃ (j : ι) (h : i ≤ j), τ i j h x = 0)
    (Y : Type w) [AddCommGroup Y] [Module Bω Y] [Module.Invertible Bω Y] :
    ∃ (i : ι) (L : Type u) (_ : AddCommGroup L) (_ : Module (B i) L),
      Module.Invertible (B i) L ∧
      Nonempty (letI := (g i).toRingHom.toAlgebra; TensorProduct (B i) Bω L ≃ₗ[Bω] Y)
```

### `Module.IsDirectLimit.exists_linearEquiv_of_finitePresentation`

`Thm_Module_IsDirectLimit_exists_linearEquiv_of_finitePresentation` — Isomorphisms of finitely presented modules descend to a stage

```lean
theorem Module.IsDirectLimit.exists_linearEquiv_of_finitePresentation
    {ι : Type v} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {B₀ : Type u} [CommRing B₀]
    (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra B₀ (B i)]
    (τ : ∀ i j, i ≤ j → B i →ₐ[B₀] B j) [DirectedSystem B (fun i j h => τ i j h)]
    (Bω : Type u) [CommRing Bω] [Algebra B₀ Bω] (g : ∀ i, B i →ₐ[B₀] Bω)
    (hg : ∀ i j (h : i ≤ j), (g j).comp (τ i j h) = g i)
    (hsurj : ∀ b : Bω, ∃ i x, g i x = b)
    (hzero : ∀ i (x : B i), g i x = 0 → ∃ (j : ι) (h : i ≤ j), τ i j h x = 0)
    (P Q : Type w) [AddCommGroup P] [Module B₀ P] [AddCommGroup Q] [Module B₀ Q]
    [Module.FinitePresentation B₀ P] [Module.FinitePresentation B₀ Q]
    (e : TensorProduct B₀ Bω P ≃ₗ[Bω] TensorProduct B₀ Bω Q) :
    ∃ (i : ι) (eᵢ : TensorProduct B₀ (B i) P ≃ₗ[B i] TensorProduct B₀ (B i) Q),
      (e : _ →ₗ[Bω] _).restrictScalars B₀ ∘ₗ (g i).toLinearMap.rTensor P =
        (g i).toLinearMap.rTensor Q ∘ₗ (eᵢ : _ →ₗ[B i] _).restrictScalars B₀
```

### `Module.IsDirectLimit.exists_stage_linearEquiv_of_finitePresentation_compat`

`Thm_Module_IsDirectLimit_exists_stage_linearEquiv_of_finitePresentation_compat` — Descent of isomorphisms of finitely presented modules to a stage

```lean
theorem Module.IsDirectLimit.exists_stage_linearEquiv_of_finitePresentation_compat
    {ι : Type v} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {B₀ : Type u} [CommRing B₀]
    (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra B₀ (B i)]
    (τ : ∀ i j, i ≤ j → B i →ₐ[B₀] B j) [DirectedSystem B (fun i j h => τ i j h)]
    (Bω : Type u) [CommRing Bω] [Algebra B₀ Bω] (g : ∀ i, B i →ₐ[B₀] Bω)
    (hg : ∀ i j (h : i ≤ j), (g j).comp (τ i j h) = g i)
    (hsurj : ∀ b : Bω, ∃ i x, g i x = b)
    (hzero : ∀ i (x : B i), g i x = 0 → ∃ (j : ι) (h : i ≤ j), τ i j h x = 0)
    (i₀ : ι) [Algebra (B i₀) Bω] (hgi : ∀ x, algebraMap (B i₀) Bω x = g i₀ x)
    (P Q : Type w) [AddCommGroup P] [Module (B i₀) P] [AddCommGroup Q] [Module (B i₀) Q]
    [Module.FinitePresentation (B i₀) P] [Module.FinitePresentation (B i₀) Q]
    (e : TensorProduct (B i₀) Bω P ≃ₗ[Bω] TensorProduct (B i₀) Bω Q) :
    ∃ (j : ι) (hj : i₀ ≤ j) (gj : letI := (τ i₀ j hj).toRingHom.toAlgebra; B j →ₐ[B i₀] Bω) (_ : ∀ b, gj b = g j b)
      (ej : letI := (τ i₀ j hj).toRingHom.toAlgebra; TensorProduct (B i₀) (B j) P ≃ₗ[B j] TensorProduct (B i₀) (B j) Q),
      letI := (τ i₀ j hj).toRingHom.toAlgebra
      ∀ x : TensorProduct (B i₀) (B j) P, e (gj.toLinearMap.rTensor P x) = gj.toLinearMap.rTensor Q (ej x)
```

### `Module.Projective.exists_baseChange_quotient_iso_of_squareZero`

`Thm_Module_Projective_exists_baseChange_quotient_iso_of_squareZero` — Finite projective modules lift along a square-zero quotient

```lean
theorem Module.Projective.exists_baseChange_quotient_iso_of_squareZero
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ^ 2 = ⊥)
    (P : Type u) [AddCommGroup P] [Module (R ⧸ I) P]
    [Module.Projective (R ⧸ I) P] [Module.Finite (R ⧸ I) P] :
    ∃ (P' : Type u) (_ : AddCommGroup P') (_ : Module R P'),
      Module.Projective R P' ∧ Module.Finite R P' ∧
      Nonempty (((R ⧸ I) ⊗[R] P') ≃ₗ[R ⧸ I] P)
```

### `Module.Projective.exists_ideal_fg_forall_tmul_eq_zero_iff_map_eq_bot`

`Thm_Module_Projective_exists_ideal_fg_forall_tmul_eq_zero_iff_map_eq_bot` — Finitely generated vanishing ideal of a section of a projective module

```lean
theorem Module.Projective.exists_ideal_fg_forall_tmul_eq_zero_iff_map_eq_bot
    (B : Type u) [CommRing B] (M : Type v) [AddCommGroup M] [Module B M]
    [Module.Finite B M] [Module.Projective B M] (x : M) :
    ∃ J : Ideal B, J.FG ∧ ∀ (A : Type u) [CommRing A] (φ : B →+* A),
      (letI : Algebra B A := φ.toAlgebra; ((1 : A) ⊗ₜ[B] x : A ⊗[B] M) = 0) ↔ Ideal.map φ J = ⊥
```

### `Module.Projective.exists_ideal_forall_tmul_eq_zero_iff_map_eq_bot`

`Thm_Module_Projective_exists_ideal_forall_tmul_eq_zero_iff_map_eq_bot` — Vanishing ideal of an element of a projective module

```lean
theorem Module.Projective.exists_ideal_forall_tmul_eq_zero_iff_map_eq_bot
    (B : Type u) [CommRing B] (M : Type v) [AddCommGroup M] [Module B M]
    [Module.Finite B M] [Module.Projective B M] (x : M) :
    ∃ J : Ideal B, ∀ (A : Type u) [CommRing A] (φ : B →+* A),
      (letI : Algebra B A := φ.toAlgebra; ((1 : A) ⊗ₜ[B] x : A ⊗[B] M) = 0) ↔ Ideal.map φ J = ⊥
```

### `Module.Projective.exists_linearEquiv_of_baseChange_quotient_of_squareZero_of_compat`

`Thm_Module_Projective_exists_linearEquiv_of_baseChange_quotient_of_squareZero_of_compat` — Lifting isomorphisms of f.g. projectives along square-zero ideals

```lean
theorem Module.Projective.exists_linearEquiv_of_baseChange_quotient_of_squareZero_of_compat
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ^ 2 = ⊥)
    (P₁ P₂ : Type u) [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₁] [Module R P₂]
    [Module.Projective R P₁] [Module.Finite R P₁]
    [Module.Projective R P₂] [Module.Finite R P₂]
    (e : ((R ⧸ I) ⊗[R] P₁) ≃ₗ[R ⧸ I] ((R ⧸ I) ⊗[R] P₂)) :
    ∃ σ' : P₁ ≃ₗ[R] P₂, ∀ p : P₁, (1 : R ⧸ I) ⊗ₜ[R] σ' p = e ((1 : R ⧸ I) ⊗ₜ[R] p)
```

### `Module.Projective.nonempty_linearEquiv_of_baseChange_quotient_of_squareZero`

`Thm_Module_Projective_nonempty_linearEquiv_of_baseChange_quotient_of_squareZero` — Lifting isomorphisms of f.g. projectives along a square-zero quotient

```lean
theorem Module.Projective.nonempty_linearEquiv_of_baseChange_quotient_of_squareZero
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ^ 2 = ⊥)
    (P₁ P₂ : Type u) [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₁] [Module R P₂]
    [Module.Projective R P₁] [Module.Finite R P₁]
    [Module.Projective R P₂] [Module.Finite R P₂]
    (e : ((R ⧸ I) ⊗[R] P₁) ≃ₗ[R ⧸ I] ((R ⧸ I) ⊗[R] P₂)) :
    Nonempty (P₁ ≃ₗ[R] P₂)
```

### `Module.bijective_smul_of_notMem_of_isMaximal_of_pow_smul_eq_bot`

`Thm_Module_bijective_smul_of_notMem_of_isMaximal_of_pow_smul_eq_bot` — Elements outside a maximal ideal act bijectively on modules killed by a power of it

```lean
theorem Module.bijective_smul_of_notMem_of_isMaximal_of_pow_smul_eq_bot
    {T : Type*} [CommRing T] {M : Type*} [AddCommGroup M] [Module T M]
    (𝔓 : Ideal T) (h𝔓 : 𝔓.IsMaximal) (k : ℕ) (hk : ∀ (a : T), a ∈ 𝔓 ^ k → ∀ x : M, a • x = 0)
    (u : T) (hu : u ∉ 𝔓) : Function.Bijective (fun x : M => u • x)
```

### `Module.card_torsionBySet_quotient_natCast_smul_top_eq_pow_finrank_iInf_ker_baseChange`

`Thm_Module_card_torsionBySet_quotient_natCast_smul_top_eq_pow_finrank_iInf_ker_baseChange` — Counting 𝔪-torsion in M/pM via base change to k

```lean
theorem Module.card_torsionBySet_quotient_natCast_smul_top_eq_pow_finrank_iInf_ker_baseChange
    (T : Type) [CommRing T] (M : Type) [AddCommGroup M] [Module T M] [Module.Finite ℤ M]
    (𝔪 : Ideal T) (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] :
    Nat.card ↥(Submodule.torsionBySet T (M ⧸ (Ideal.span {((p : ℕ) : T)} • (⊤ : Submodule T M))) 𝔪) =
      p ^ Module.finrank k ↥(⨅ (t : T) (_ : t ∈ 𝔪),
        LinearMap.ker ((DistribSMul.toLinearMap ℤ M t).baseChange k))
```

### `Module.depth_eq_depth_of_finite_of_isLocalHom`

`Thm_Module_depth_eq_depth_of_finite_of_isLocalHom` — Depth is invariant under module-finite local base change

```lean
theorem Module.depth_eq_depth_of_finite_of_isLocalHom
    (R : Type*) (S : Type*) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [IsNoetherianRing R] [Algebra R S] [IsLocalHom (algebraMap R S)] [Module.Finite R S]
    (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M] :
    Module.depth R M = Module.depth S M
```

### `Module.depth_le_ringKrullDim`

`Thm_Module_depth_le_ringKrullDim` — Depth is bounded by Krull dimension

```lean
theorem Module.depth_le_ringKrullDim {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Nontrivial M] [Module.Finite R M] :
    .some (Module.depth R M) ≤ ringKrullDim R
```

### `Module.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes`

`Thm_Module_depth_le_ringKrullDim_quotient_of_mem_associatedPrimes` — Depth is bounded by dim R/𝔭 for associated primes

```lean
theorem Module.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    {p : Ideal R} (hp : p ∈ associatedPrimes R M) :
    (Module.depth R M : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p)
```

### `Module.depth_quotSMulTop_succ_eq`

`Thm_Module_depth_quotSMulTop_succ_eq` — Depth drops by one modulo an M-regular element of 𝔪

```lean
theorem Module.depth_quotSMulTop_succ_eq
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    {x : R} (hx : x ∈ maximalIdeal R) (hxreg : IsSMulRegular M x) :
    Module.depth R (QuotSMulTop x M) + 1 = Module.depth R M
```

### `Module.depth_quotient_eq_depth`

`Thm_Module_depth_quotient_eq_depth` — Depth is unchanged under passing to a quotient ring

```lean
theorem Module.depth_quotient_eq_depth
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R) [IsLocalRing (R ⧸ I)]
    (N : Type*) [AddCommGroup N] [Module R N] [Module (R ⧸ I) N] [IsScalarTower R (R ⧸ I) N] :
    Module.depth (R ⧸ I) N = Module.depth R N
```

### `Module.existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul`

`Thm_Module_existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul` — Unique compatible lift along an I-adic tower

```lean
theorem Module.existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul
    {R : Type u} [CommRing R] (I : Ideal R)
    (E : ℕ → Type u) [∀ k, AddCommGroup (E k)] [∀ k, Module R (E k)]
    (τ : ∀ k, E (k + 1) →ₗ[R] E k) (hτs : ∀ k, Function.Surjective (τ k))
    (hτk : ∀ k, LinearMap.ker (τ k) = I ^ (k + 1) • (⊤ : Submodule R (E (k + 1))))
    (P : ℕ → Type u) [∀ k, AddCommGroup (P k)] [∀ k, Module R (P k)] (π : ∀ k, P (k + 1) →ₗ[R] P k)
    (C : ℕ → Type u) [∀ k, AddCommGroup (C k)] [∀ k, Module R (C k)] (θ : ∀ k, P k →ₗ[R] C k)
    (u : ∀ k, E k →ₗ[R] P k) (huc : ∀ k, π k ∘ₗ u (k + 1) = u k ∘ₗ τ k)
    (hur : ∀ k, LinearMap.range (u k) = LinearMap.ker (θ k))
    (hui : ∃ c : ℕ, ∀ k : ℕ, LinearMap.ker (u (k + c)) ≤ I ^ (k + 1) • (⊤ : Submodule R (E (k + c))))
    (p : ∀ k, P k) (hp : ∀ k, π k (p (k + 1)) = p k) (hpθ : ∀ k, θ k (p k) = 0) :
    ∃! e : ∀ k, E k, (∀ k, τ k (e (k + 1)) = e k) ∧ ∀ k, u k (e k) = p k
```

### `Module.exists_away_forall_nonempty_basis_tensorProduct_of_projective_of_finite`

`Thm_Module_exists_away_forall_nonempty_basis_tensorProduct_of_projective_of_finite` — Projective finite modules are free on a basic open

```lean
theorem Module.exists_away_forall_nonempty_basis_tensorProduct_of_projective_of_finite
    {S : Type u} [CommRing S] (P : Type u) [AddCommGroup P] [Module S P] [Module.Finite S P] [Module.Projective S P]
    (p : PrimeSpectrum S) :
    ∃ r : S, r ∉ p.asIdeal ∧
      ∀ (S' : Type u) [CommRing S'] [Algebra S S'] [IsLocalization.Away r S'],
        ∃ m : ℕ, Nonempty (Module.Basis (Fin m) S' (S' ⊗[S] P))
```

### `Module.exists_basis_coe_eq_of_isAdicComplete_of_isHausdorff_of_isSMulRegular`

`Thm_Module_exists_basis_coe_eq_of_isAdicComplete_of_isHausdorff_of_isSMulRegular` — Lifting a basis of M/π M to a basis of M

```lean
theorem Module.exists_basis_coe_eq_of_isAdicComplete_of_isHausdorff_of_isSMulRegular
    {A : Type u} [CommRing A] (π : A) [IsAdicComplete (Ideal.span {π}) A]
    {M : Type v} [AddCommGroup M] [Module A M] [IsHausdorff (Ideal.span {π}) M]
    (hπ : IsSMulRegular M π) {ι : Type w} [Finite ι]
    (b : Module.Basis ι (A ⧸ Ideal.span {π}) (M ⧸ (Ideal.span {π} • ⊤ : Submodule A M)))
    (e : ι → M) (he : ∀ i, Submodule.Quotient.mk (e i) = b i) :
    ∃ b' : Module.Basis ι A M, ⇑b' = e
```

### `Module.exists_basis_padicValRat_apply_nonneg_iff_pair`

`Thm_Module_exists_basis_padicValRat_apply_nonneg_iff_pair` — Adapted basis for a nested pair of p-integral lattices

```lean
theorem Module.exists_basis_padicValRat_apply_nonneg_iff_pair
    {M : Type*} [AddCommGroup M] [Module ℚ M] [FiniteDimensional ℚ M] (p : ℕ) [Fact p.Prime]
    (a a' : ℤ → M →ₗ[ℚ] ℚ) (hinj' : ∀ x, (∀ m, a' m x = 0) → x = 0)
    (hbd : ∀ x, ∃ N : ℕ, ∀ m, 0 ≤ padicValRat p ((p : ℚ) ^ N * a m x))
    (hbd' : ∀ x, ∃ N : ℕ, ∀ m, 0 ≤ padicValRat p ((p : ℚ) ^ N * a' m x))
    (hsub : ∀ x, (∀ m, 0 ≤ padicValRat p (a m x)) → ∀ m, 0 ≤ padicValRat p (a' m x))
    (u : M) (hu : ∀ m, 0 ≤ padicValRat p (a m u))
    (hprim : ∃ m, a' m u ≠ 0 ∧ padicValRat p (a' m u) = 0) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℚ M) (e : Fin n → ℕ) (i₀ : Fin n), b i₀ = u ∧ e i₀ = 0 ∧
      (∀ c : Fin n → ℚ, (∀ m, 0 ≤ padicValRat p (a m (∑ i, c i • b i))) ↔ ∀ i, 0 ≤ padicValRat p (c i)) ∧
      (∀ c : Fin n → ℚ, (∀ m, 0 ≤ padicValRat p (a' m (∑ i, c i • b i))) ↔
        ∀ i, -(e i : ℤ) ≤ padicValRat p (c i))
```

### `Module.exists_basis_rat_eq_basis_padicInt_of_linearEquiv_baseChange`

`Thm_Module_exists_basis_rat_eq_basis_padicInt_of_linearEquiv_baseChange` — Matching ℚ- and ℤₚ-bases across a base-change isomorphism

```lean
theorem Module.exists_basis_rat_eq_basis_padicInt_of_linearEquiv_baseChange
    (p : ℕ) [Fact p.Prime]
    (A : Type*) [AddCommGroup A] [Module ℚ A] [Module.Finite ℚ A]
    (Hp : Type*) [AddCommGroup Hp] [Module ℤ_[p] Hp]
    [Module.Finite ℤ_[p] Hp] [Module.Flat ℤ_[p] Hp]
    (φ : (ℚ_[p] ⊗[ℚ] A) ≃ₗ[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] Hp)) :
    ∃ (n : ℕ) (b : Basis (Fin n) ℚ A) (bHp : Basis (Fin n) ℤ_[p] Hp),
      ∀ i, φ (1 ⊗ₜ[ℚ] (b i)) = 1 ⊗ₜ[ℤ_[p]] (bHp i)
```

### `Module.exists_forall_alternatingSum_finrank_cohomology_baseChange_eq_of_flat_complex_of_isLocalRing`

`Thm_Module_exists_forall_alternatingSum_finrank_cohomology_baseChange_eq_of_flat_complex_of_isLocalRing` — Constant Euler characteristic of fibres of a flat complex

```lean
theorem Module.exists_forall_alternatingSum_finrank_cohomology_baseChange_eq_of_flat_complex_of_isLocalRing
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbdd : ∀ i, n < i → Subsingleton (C i))
    (hfin0 : Module.Finite R (LinearMap.ker (d 0)))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype)) :
    ∃ χ₀ : ℤ, ∀ (A : Type u) [Field A] [Algebra R A]
      (H0 : Type u) [AddCommGroup H0] [Module A H0] (_e₀ : H0 ≃ₗ[A] LinearMap.ker ((d 0).baseChange A))
      (H : ℕ → Type u) [∀ i, AddCommGroup (H i)] [∀ i, Module A (H i)]
      (φ : ∀ i, LinearMap.ker ((d (i + 1)).baseChange A) →ₗ[A] H i)
      (_hφ : ∀ i, Function.Surjective (φ i))
      (_hφker : ∀ i, LinearMap.ker (φ i) =
        (LinearMap.range ((d i).baseChange A)).comap (LinearMap.ker ((d (i + 1)).baseChange A)).subtype),
      (Module.finrank A H0 : ℤ) + ∑ i ∈ Finset.range n, (-1 : ℤ) ^ (i + 1) * (Module.finrank A (H i) : ℤ) = χ₀
```

### `Module.exists_forall_bijective_of_forall_surjective_of_forall_smul_pow_eq_zero`

`Thm_Module_exists_forall_bijective_of_forall_surjective_of_forall_smul_pow_eq_zero` — Chain of surjections of torsion modules over a DVR eventually bijective

```lean
theorem Module.exists_forall_bijective_of_forall_surjective_of_forall_smul_pow_eq_zero
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (H : ℕ → Type v) [∀ n, AddCommGroup (H n)] [∀ n, Module R (H n)]
    (φ : ∀ n, H n →ₗ[R] H (n + 1)) (hφ : ∀ n, Function.Surjective (φ n))
    (N : ℕ) (hfin : ∀ n, N ≤ n → Module.Finite R (H n))
    (htors : ∀ n, N ≤ n → ∃ k : ℕ, ∀ x : H n, ϖ ^ k • x = 0) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → Function.Bijective (φ n)
```

### `Module.exists_forall_isUnit_rankAtStalk_baseChange_eq_finrank_residueField_tensor`

`Thm_Module_exists_forall_isUnit_rankAtStalk_baseChange_eq_finrank_residueField_tensor` — Locally constant rank after inverting one more element

```lean
theorem Module.exists_forall_isUnit_rankAtStalk_baseChange_eq_finrank_residueField_tensor
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (𝔭 : PrimeSpectrum R) (g : R) (hg : g ∉ 𝔭.asIdeal)
    (hproj : ∀ (A : Type u) [CommRing A] [Algebra R A], IsUnit (algebraMap R A g) → Module.Projective A (A ⊗[R] M)) :
    ∃ g' : R, g' ∉ 𝔭.asIdeal ∧
      (∀ (A : Type u) [CommRing A] [Algebra R A], IsUnit (algebraMap R A g') → IsUnit (algebraMap R A g)) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A], IsUnit (algebraMap R A g') →
        ∀ 𝔮 : PrimeSpectrum A,
          Module.rankAtStalk (A ⊗[R] M) 𝔮 =
            Module.finrank 𝔭.asIdeal.ResidueField (𝔭.asIdeal.ResidueField ⊗[R] M)
```

### `Module.exists_forall_isUnit_surjective_baseChange_of_surjective_baseChange_residueField`

`Thm_Module_exists_forall_isUnit_surjective_baseChange_of_surjective_baseChange_residueField` — Surjectivity after base change spreads from a single fibre

```lean
theorem Module.exists_forall_isUnit_surjective_baseChange_of_surjective_baseChange_residueField
    {R : Type u} [CommRing R]
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module.Finite R N]
    (f : M →ₗ[R] N) (𝔭 : PrimeSpectrum R)
    (hf : Function.Surjective (f.baseChange 𝔭.asIdeal.ResidueField)) :
    ∃ g : R, g ∉ 𝔭.asIdeal ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A], IsUnit (algebraMap R A g) →
        Function.Surjective (f.baseChange A)
```

### `Module.exists_forall_notMem_and_linearIndependent_and_smul_mem_span_of_finrank_baseChange_eq`

`Thm_Module_exists_forall_notMem_and_linearIndependent_and_smul_mem_span_of_finrank_baseChange_eq` — Constant fibre rank gives a basis after inverting one element

```lean
theorem Module.exists_forall_notMem_and_linearIndependent_and_smul_mem_span_of_finrank_baseChange_eq
    {A : Type u} [CommRing A] [IsDomain A] {P : Type v} [AddCommGroup P] [Module A P] [Module.Finite A P]
    (d : ℕ) (S : Finset (Ideal A)) (hS : ∀ 𝔭 ∈ S, 𝔭.IsMaximal) (hSne : S.Nonempty)
    (hrank : ∀ (K : Type u) [Field K] [Algebra A K], Module.finrank K (TensorProduct A K P) = d) :
    ∃ (f : A) (e : Fin d → P), (∀ 𝔭 ∈ S, f ∉ 𝔭) ∧ LinearIndependent A e ∧
      ∀ p : P, f • p ∈ Submodule.span A (Set.range e)
```

### `Module.exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker`

`Thm_Module_exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker` — Adic systems: the kernel system is the kernel module's truncation

```lean
theorem Module.exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    {M N K : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [AddCommGroup K] [Module R K]
    (ρ : M →ₗ[R] N) (ι : K →ₗ[R] M) (hι : Function.Injective ι) (hιr : LinearMap.range ι = LinearMap.ker ρ)
    (E : ℕ → Type u) [∀ k, AddCommGroup (E k)] [∀ k, Module R (E k)]
    (τ : ∀ k, E (k + 1) →ₗ[R] E k) (hτs : ∀ k, Function.Surjective (τ k))
    (hτk : ∀ k, LinearMap.ker (τ k) = I ^ (k + 1) • (⊤ : Submodule R (E (k + 1))))
    (P : ℕ → Type u) [∀ k, AddCommGroup (P k)] [∀ k, Module R (P k)] (π : ∀ k, P (k + 1) →ₗ[R] P k)
    (ψP : ∀ k, M →ₗ[R] P k) (hψPs : ∀ k, Function.Surjective (ψP k))
    (hψPk : ∀ k, LinearMap.ker (ψP k) = I ^ (k + 1) • (⊤ : Submodule R M))
    (hψPc : ∀ k, π k ∘ₗ ψP (k + 1) = ψP k)
    (C : ℕ → Type u) [∀ k, AddCommGroup (C k)] [∀ k, Module R (C k)] (γ : ∀ k, C (k + 1) →ₗ[R] C k)
    (ψC : ∀ k, N →ₗ[R] C k) (hψCs : ∀ k, Function.Surjective (ψC k))
    (hψCk : ∀ k, LinearMap.ker (ψC k) = I ^ (k + 1) • (⊤ : Submodule R N))
    (hψCc : ∀ k, γ k ∘ₗ ψC (k + 1) = ψC k)
    (θ : ∀ k, P k →ₗ[R] C k) (hθ : ∀ k, θ k ∘ₗ ψP k = ψC k ∘ₗ ρ)
    (u : ∀ k, E k →ₗ[R] P k) (huc : ∀ k, π k ∘ₗ u (k + 1) = u k ∘ₗ τ k)
    (hur : ∀ k, LinearMap.range (u k) = LinearMap.ker (θ k))
    (hui : ∃ c : ℕ, ∀ k : ℕ, LinearMap.ker (u (k + c)) ≤ I ^ (k + 1) • (⊤ : Submodule R (E (k + c)))) :
    ∃ ψ : ∀ k, K →ₗ[R] E k,
      (∀ k, Function.Surjective (ψ k)) ∧
      (∀ k, LinearMap.ker (ψ k) = I ^ (k + 1) • (⊤ : Submodule R K)) ∧
      (∀ k, τ k ∘ₗ ψ (k + 1) = ψ k) ∧
      (∀ k, u k ∘ₗ ψ k = ψP k ∘ₗ ι)
```

### `Module.exists_hom_dual_quotient_range_dualMap_linearEquiv_ker_lTensor_natural`

`Thm_Module_exists_hom_dual_quotient_range_dualMap_linearEquiv_ker_lTensor_natural` — Cokernel of the transpose corepresents ker(B ⊗ d)

```lean
theorem Module.exists_hom_dual_quotient_range_dualMap_linearEquiv_ker_lTensor_natural
    (R : Type u) [CommRing R]
    (K₀ K₁ : Type u) [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Free R K₀]
    [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Free R K₁]
    (d : K₀ →ₗ[R] K₁) :
    ∃ e : ∀ (B : Type u) [AddCommGroup B] [Module R B],
        ((Module.Dual R K₀ ⧸ LinearMap.range d.dualMap) →ₗ[R] B) ≃ₗ[R] LinearMap.ker (d.lTensor B),
      (∀ (B B' : Type u) [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B'] (u : B →ₗ[R] B')
          (g : (Module.Dual R K₀ ⧸ LinearMap.range d.dualMap) →ₗ[R] B),
          ((e B' (u ∘ₗ g) : LinearMap.ker (d.lTensor B')) : B' ⊗[R] K₀) =
            u.rTensor K₀ ((e B g : LinearMap.ker (d.lTensor B)) : B ⊗[R] K₀)) ∧
      (∀ (B : Type u) [AddCommGroup B] [Module R B] (t : LinearMap.ker (d.lTensor B)) (φ : Module.Dual R K₀),
          (e B).symm t (Submodule.Quotient.mk φ) = TensorProduct.rid R B (φ.lTensor B (t : B ⊗[R] K₀)))
```

### `Module.exists_ideal_forall_projective_and_rankAtStalk_eq_iff`

`Thm_Module_exists_ideal_forall_projective_and_rankAtStalk_eq_iff` — Universal ideal for rank-r local freeness after base change

```lean
theorem Module.exists_ideal_forall_projective_and_rankAtStalk_eq_iff
    (A : Type) [CommRing A] (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M] (r : ℕ)
    (hr : ∀ p : PrimeSpectrum A,
      Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] M) ≤ r) :
    ∃ 𝔞 : Ideal A, ∀ (B : Type) [CommRing B] [Algebra A B],
      (Module.Projective B (B ⊗[A] M) ∧ ∀ q : PrimeSpectrum B, Module.rankAtStalk (B ⊗[A] M) q = r) ↔
        ∀ a ∈ 𝔞, algebraMap A B a = 0
```

### `Module.exists_injective_linearMap_pi_and_smul_mem_range_of_finrank_torsionBySet_eq_mul`

`Thm_Module_exists_injective_linearMap_pi_and_smul_mem_range_of_finrank_torsionBySet_eq_mul` — Freeness up to finite index from constant eigen-lattice rank

```lean
theorem Module.exists_injective_linearMap_pi_and_smul_mem_range_of_finrank_torsionBySet_eq_mul
    {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    {T : Type*} [CommRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T]
    {M : Type*} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.IsTorsionFree 𝒪 M]
    {ι : Type*} [Fintype ι]
    {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, IsDomain (A i)] [∀ i, Algebra 𝒪 (A i)]
    [∀ i, Module.IsTorsionFree 𝒪 (A i)]
    (χ : ∀ i, T →ₐ[𝒪] A i) (hker : ⨅ i, RingHom.ker (χ i) = ⊥)
    (a : 𝒪) (ha : a ≠ 0) (hsurj : ∀ y : ∀ i, A i, ∃ x : T, ∀ i, χ i x = a • y i)
    (d : ℕ)
    (hrank : ∀ i, Module.finrank 𝒪 ↥(Submodule.torsionBySet T M ↑(RingHom.ker (χ i))) =
      d * Module.finrank 𝒪 (T ⧸ RingHom.ker (χ i))) :
    ∃ (f : (Fin d → T) →ₗ[T] M) (c : 𝒪), c ≠ 0 ∧ Function.Injective f ∧
      ∀ m : M, c • m ∈ LinearMap.range f
```

### `Module.exists_isArtinianRing_isReduced_faithful_baseChange_of_quadraticRelation`

`Thm_Module_exists_isArtinianRing_isReduced_faithful_baseChange_of_quadraticRelation` — Generic fibre of a faithful module with a quadratic relation

```lean
theorem Module.exists_isArtinianRing_isReduced_faithful_baseChange_of_quadraticRelation
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪]
    {R : Type} [CommRing R] [Algebra 𝒪 R] [Module.Finite 𝒪 R] [IsReduced R]
    {G : Type} [Group G]
    {Y : Type} [AddCommGroup Y] [Module R Y] [Module 𝒪 Y] [IsScalarTower 𝒪 R Y]
    [Module.Finite 𝒪 Y] [Module.IsTorsionFree 𝒪 Y]
    (hfaith : ∀ x : R, (∀ y : Y, x • y = 0) → x = 0)
    (ρY : G →* Module.End R Y)
    {Δ : Type} [CommGroup Δ] [Finite Δ] (D : Δ →* Module.End R Y)
    (hD : ∀ (d : Δ) (g : G), D d * ρY g = ρY g * D d)
    (δ : G →* Δ) (c : G →* Rˣ) (t : G → R)
    (hrel : ∀ g : G, ρY g * ρY g - (t g) • ρY g + ((c g : Rˣ) : R) • D (δ g) = 0) :
    ∃ (k : Type) (_ : CommRing k) (_ : IsArtinianRing k) (_ : IsReduced k) (_ : Algebra ℚ k)
      (_ : Algebra R k) (_ : Algebra 𝒪 k) (_ : IsScalarTower 𝒪 R k)
      (_ : Function.Injective (algebraMap R k))
      (_ : ∀ a : 𝒪, a ≠ 0 → IsUnit (algebraMap 𝒪 k a))
      (M : Type) (_ : AddCommGroup M) (_ : Module k M) (_ : Module R M) (_ : Module 𝒪 M)
      (_ : IsScalarTower R k M) (_ : IsScalarTower 𝒪 k M) (_ : IsScalarTower 𝒪 R M) (_ : Module.Finite k M)
      (_ : ∀ x : k, (∀ m : M, x • m = 0) → x = 0)
      (ρM : G →* Module.End k M) (dM : G →* kˣ)
      (_ : ∀ g : G, ρM g * ρM g - (algebraMap R k (t g)) • ρM g + ((dM g : kˣ) : k) • (1 : Module.End k M) = 0)
      (ι : Y →ₗ[R] M) (_ : Function.Injective ι)
      (_ : ∀ (g : G) (y : Y), ι (ρY g y) = ρM g (ι y)),
      ∀ m : M, ∃ a : 𝒪, a ≠ 0 ∧ a • m ∈ LinearMap.range ι
```

### `Module.exists_mem_maximalIdeal_isSMulRegular_isSMulRegular`

`Thm_Module_exists_mem_maximalIdeal_isSMulRegular_isSMulRegular` — A common regular element in 𝔪 for two modules

```lean
theorem Module.exists_mem_maximalIdeal_isSMulRegular_isSMulRegular {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (N₁ N₂ : Type*) [AddCommGroup N₁] [Module R N₁] [Module.Finite R N₁] [AddCommGroup N₂] [Module R N₂] [Module.Finite R N₂] (h₁ : ¬ IsAssociatedPrime (IsLocalRing.maximalIdeal R) N₁) (h₂ : ¬ IsAssociatedPrime (IsLocalRing.maximalIdeal R) N₂) :
    ∃ z ∈ IsLocalRing.maximalIdeal R, IsSMulRegular N₁ z ∧ IsSMulRegular N₂ z
```

### `Module.exists_mumfordTruncation_of_flat_complex`

`Thm_Module_exists_mumfordTruncation_of_flat_complex` — Mumford's truncation of a bounded flat complex

```lean
theorem Module.exists_mumfordTruncation_of_flat_complex
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbdd : ∀ i, n < i → Subsingleton (C i))
    (hfin0 : Module.Finite R (LinearMap.ker (d 0)))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype)) :
    ∃ (m₀ m₁ : ℕ) (P : Submodule R (C 0 × (Fin m₀ → R))) (ε : (Fin m₀ → R) →ₗ[R] (Fin m₁ → R)),
      Module.Finite R P ∧ Module.Flat R P ∧
      ε ∘ₗ (LinearMap.snd R (C 0) (Fin m₀ → R) ∘ₗ P.subtype) = 0 ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        (LinearMap.ker ((d 1).baseChange A) ≤ LinearMap.range ((d 0).baseChange A) →
          LinearMap.ker (ε.baseChange A)
            ≤ LinearMap.range ((LinearMap.snd R (C 0) (Fin m₀ → R) ∘ₗ P.subtype).baseChange A)) ∧
        (LinearMap.range ((LinearMap.ker (LinearMap.snd R (C 0) (Fin m₀ → R) ∘ₗ P.subtype)).subtype.baseChange A)
            = LinearMap.ker ((LinearMap.snd R (C 0) (Fin m₀ → R) ∘ₗ P.subtype).baseChange A) →
          LinearMap.range ((LinearMap.ker (d 0)).subtype.baseChange A) = LinearMap.ker ((d 0).baseChange A)) ∧
        (Function.Injective
            ((LinearMap.ker (LinearMap.snd R (C 0) (Fin m₀ → R) ∘ₗ P.subtype)).subtype.baseChange A) →
          Function.Injective ((LinearMap.ker (d 0)).subtype.baseChange A))
```

### `Module.exists_ne_zero_forall_baseChange_eq_smul_of_algHom`

`Thm_Module_exists_ne_zero_forall_baseChange_eq_smul_of_algHom` — Characters of the operator algebra give eigenvectors after base change

```lean
theorem Module.exists_ne_zero_forall_baseChange_eq_smul_of_algHom
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {F : Type*} [Field F] [Algebra R F]
    {ι : Type*} (t : ι → Module.End R M) (ht : ∀ i j, Commute (t i) (t j))
    (χ : ↥(Algebra.adjoin R (Set.range t)) →ₐ[R] F) :
    ∃ y : F ⊗[R] M, y ≠ 0 ∧
      ∀ i, (t i).baseChange F y = χ ⟨t i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ • y
```

### `Module.exists_ne_zero_forall_smul_eq_smul_of_algHom`

`Thm_Module_exists_ne_zero_forall_smul_eq_smul_of_algHom` — Characters of a faithful finite algebra have eigenvectors

```lean
theorem Module.exists_ne_zero_forall_smul_eq_smul_of_algHom {K A V : Type*} [Field K] [CommRing A] [Algebra K A] [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower K A V] [Module.Finite K V] [FaithfulSMul A V] (χ : A →ₐ[K] K) : ∃ v : V, v ≠ 0 ∧ ∀ a : A, a • v = χ a • v
```

### `Module.exists_notMem_and_free_localizedModule_of_isIntegrallyClosed_of_ringKrullDim_le_one`

`Thm_Module_exists_notMem_and_free_localizedModule_of_isIntegrallyClosed_of_ringKrullDim_le_one` — Local freeness near a point with integrally closed local ring of dimension ≤ 1

```lean
theorem Module.exists_notMem_and_free_localizedModule_of_isIntegrallyClosed_of_ringKrullDim_le_one
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] (𝔭 : Ideal A) [𝔭.IsPrime]
    (h𝔭ic : IsIntegrallyClosed (Localization.AtPrime 𝔭)) (h𝔭dim : ringKrullDim (Localization.AtPrime 𝔭) ≤ 1)
    (B : Type u) [AddCommGroup B] [Module A B] [Module.Finite A B] [NoZeroSMulDivisors A B] :
    ∃ f : A, f ∉ 𝔭 ∧ Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) B)
```

### `Module.exists_notMem_forall_smul_eq_zero_of_isMaximal_of_forall_smul_eq_zero_imp`

`Thm_Module_exists_notMem_forall_smul_eq_zero_of_isMaximal_of_forall_smul_eq_zero_imp` — Finite module without P-torsion is killed outside P

```lean
theorem Module.exists_notMem_forall_smul_eq_zero_of_isMaximal_of_forall_smul_eq_zero_imp
    {T : Type*} [CommRing T] {M : Type*} [AddCommGroup M] [Module T M] [Finite M]
    (𝔓 : Ideal T) (h𝔓 : 𝔓.IsMaximal)
    (hno : ∀ x : M, (∀ a ∈ 𝔓, a • x = 0) → x = 0) :
    ∃ s : T, s ∉ 𝔓 ∧ ∀ x : M, s • x = 0
```

### `Module.exists_pow_maximalIdeal_smul_top_baseChange_eq_bot_of_isFiniteLength_of_isPrime`

`Thm_Module_exists_pow_maximalIdeal_smul_top_baseChange_eq_bot_of_isFiniteLength_of_isPrime` — Base change of a finite-length module is killed by a power of mathfrak m_B

```lean
theorem Module.exists_pow_maximalIdeal_smul_top_baseChange_eq_bot_of_isFiniteLength_of_isPrime
    (S : Type u) [CommRing S] (H : Type v) [AddCommGroup H] [Module S H] (hH : IsFiniteLength S H)
    (𝔭 : Ideal S) [𝔭.IsPrime]
    (B : Type w) [CommRing B] [Algebra S B] [IsLocalization.AtPrime B 𝔭] [IsLocalRing B] :
    ∃ n : ℕ, IsLocalRing.maximalIdeal B ^ n • (⊤ : Submodule B (B ⊗[S] H)) = ⊥
```

### `Module.exists_pow_smul_ker_eq_zero_and_pow_smul_le_range_of_forall_exists_pow_smul`

`Thm_Module_exists_pow_smul_ker_eq_zero_and_pow_smul_le_range_of_forall_exists_pow_smul` — A power of J kills ker u and coker u

```lean
theorem Module.exists_pow_smul_ker_eq_zero_and_pow_smul_le_range_of_forall_exists_pow_smul
    {R : Type u} [CommRing R] (S : Finset R) (J : Ideal R) (hJ : Ideal.span (S : Set R) = J)
    {M : Type v} [AddCommGroup M] [Module R M] {N : Type w} [AddCommGroup N] [Module R N]
    (u : M →ₗ[R] N)
    (hker : (LinearMap.ker u).FG) (hcoker : Module.Finite R (N ⧸ LinearMap.range u))
    (hk : ∀ a ∈ S, ∀ x : M, u x = 0 → ∃ k : ℕ, a ^ k • x = 0)
    (hc : ∀ a ∈ S, ∀ y : N, ∃ (k : ℕ) (x : M), u x = a ^ k • y) :
    ∃ N₀ : ℕ,
      (∀ x : M, u x = 0 → ∀ a ∈ J ^ N₀, a • x = 0) ∧
      (∀ (y : N), ∀ a ∈ J ^ N₀, ∃ x : M, u x = a • y)
```

### `Module.exists_projective_complex_quasiIso_of_flat_complex`

`Thm_Module_exists_projective_complex_quasiIso_of_flat_complex` — Mumford's lemma: projective model of a bounded flat complex

```lean
theorem Module.exists_projective_complex_quasiIso_of_flat_complex
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbdd : ∀ i, n < i → Subsingleton (C i))
    (hfin0 : Module.Finite R (LinearMap.ker (d 0)))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype)) :
    ∃ (K : ℕ → Type u) (_ : ∀ i, AddCommGroup (K i)) (_ : ∀ i, Module R (K i))
      (_ : ∀ i, Module.Finite R (K i)) (_ : ∀ i, Module.Projective R (K i))
      (δ : ∀ i, K i →ₗ[R] K (i + 1)) (_ : ∀ i, δ (i + 1) ∘ₗ δ i = 0) (_ : ∀ i, n < i → Subsingleton (K i))
      (φ : ∀ i, K i →ₗ[R] C i) (_ : ∀ i, d i ∘ₗ φ i = φ (i + 1) ∘ₗ δ i),
      (∀ x : K 0, δ 0 x = 0 → φ 0 x = 0 → x = 0) ∧
      (∀ y : C 0, d 0 y = 0 → ∃ x : K 0, δ 0 x = 0 ∧ φ 0 x = y) ∧
      (∀ (i : ℕ) (x : K (i + 1)), δ (i + 1) x = 0 → φ (i + 1) x ∈ LinearMap.range (d i) →
        x ∈ LinearMap.range (δ i)) ∧
      (∀ (i : ℕ) (y : C (i + 1)), d (i + 1) y = 0 →
        ∃ x : K (i + 1), δ (i + 1) x = 0 ∧ φ (i + 1) x - y ∈ LinearMap.range (d i))
```

### `Module.exists_smul_smul_eq_and_smul_eq_iff_mem_iSup_torsionBySet_pow_of_finite`

`Thm_Module_exists_smul_smul_eq_and_smul_eq_iff_mem_iSup_torsionBySet_pow_of_finite` — Idempotent element projecting a finite submodule onto its P-primary part

```lean
theorem Module.exists_smul_smul_eq_and_smul_eq_iff_mem_iSup_torsionBySet_pow_of_finite
    {T : Type*} [CommRing T] {M : Type*} [AddCommGroup M] [Module T M]
    (N : Submodule T M) [Finite ↥N] (𝔓 : Ideal T) :
    ∃ t : T, (∀ x ∈ N, t • (t • x) = t • x) ∧
      ∀ x ∈ N, (t • x = x ↔ x ∈ ⨆ k : ℕ, Submodule.torsionBySet T M (↑(𝔓 ^ k) : Set T))
```

### `Module.exists_span_pair_union_ker_smul_eq_top_of_dualPairing_of_torsion_le_two`

`Thm_Module_exists_span_pair_union_ker_smul_eq_top_of_dualPairing_of_torsion_le_two` — Two generators modulo kerπ from an adjoint duality

```lean
theorem Module.exists_span_pair_union_ker_smul_eq_top_of_dualPairing_of_torsion_le_two
    {𝒪 : Type*} [CommRing 𝒪] {A : Type*} [CommRing A] [Algebra 𝒪 A]
    {k : Type*} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))
    (π : A →ₐ[𝒪] k)
    {P : Type*} [AddCommGroup P] [Module A P]
    {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W] [Module A W]
    (hπW : ∀ (r : 𝒪) (w : W), algebraMap 𝒪 A r • w = algebraMap 𝒪 k r • w)
    (β : P →+ Module.Dual k W)
    (hβA : ∀ (a : A) (m : P) (w : W), β (a • m) w = β m (a • w))
    (hβl : ∀ m : P, β m = 0 →
      m ∈ Submodule.span A {x : P | ∃ a : A, π a = 0 ∧ ∃ n : P, x = a • n})
    (hβr : ∀ w : W, (∀ m : P, β m w = 0) → w = 0)
    (h2 : ∃ u v : W, ∀ w : W, (∀ a : A, π a = 0 → a • w = 0) → ∃ c d : k, w = c • u + d • v) :
    ∃ x y : P, Submodule.span A
      ({x, y} ∪ {w : P | ∃ a : A, π a = 0 ∧ ∃ m : P, w = a • m}) = ⊤
```

### `Module.exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system`

`Thm_Module_exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system` — Inverse limit of an I-adic system of modules

```lean
theorem Module.exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)
    (E : ℕ → Type u) [∀ k, AddCommGroup (E k)] [∀ k, Module R (E k)]
    (τ : ∀ k, E (k + 1) →ₗ[R] E k) (hτs : ∀ k, Function.Surjective (τ k))
    (hτk : ∀ k, LinearMap.ker (τ k) = I ^ (k + 1) • (⊤ : Submodule R (E (k + 1)))) :
    ∃ L : Submodule R (∀ k, E k),
      (∀ e : ∀ k, E k, e ∈ L ↔ ∀ k, τ k (e (k + 1)) = e k) ∧
      (∀ k, Function.Surjective ((LinearMap.proj k).comp L.subtype : L →ₗ[R] E k)) ∧
      (∀ k, LinearMap.ker ((LinearMap.proj k).comp L.subtype : L →ₗ[R] E k) =
        I ^ (k + 1) • (⊤ : Submodule R L))
```

### `Module.exists_surjective_linearMap_ext_of_exact_of_free`

`Thm_Module_exists_surjective_linearMap_ext_of_exact_of_free` — Cocycles of a dualised finite free complex compute Ext

```lean
theorem Module.exists_surjective_linearMap_ext_of_exact_of_free
    (R : Type u) [CommRing R] (n : ℕ)
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)] [∀ i, Module.Free R (K i)]
    (δ : ∀ i, K i →ₗ[R] K (i + 1)) (hdd : ∀ i, δ (i + 1) ∘ₗ δ i = 0)
    (hex0 : ∀ z : K 0, δ 0 z = 0 → z = 0)
    (hex : ∀ i, i < n → ∀ z : K (i + 1), δ (i + 1) z = 0 → z ∈ LinearMap.range (δ i))
    (M : Type u) [AddCommGroup M] [Module R M] :
    (∃ π : (K 0 →ₗ[R] M) →ₗ[R]
        Abelian.Ext (ModuleCat.of R (K (n + 1) ⧸ LinearMap.range (δ n))) (ModuleCat.of R M) (n + 1),
      Function.Surjective π ∧ LinearMap.ker π = LinearMap.range (LinearMap.lcomp R M (δ 0))) ∧
    ∀ i : ℕ, i < n →
      ∃ π : LinearMap.ker (LinearMap.lcomp R M (δ i) : (K (i + 1) →ₗ[R] M) →ₗ[R] (K i →ₗ[R] M)) →ₗ[R]
          Abelian.Ext (ModuleCat.of R (K (n + 1) ⧸ LinearMap.range (δ n))) (ModuleCat.of R M) (n - i),
        Function.Surjective π ∧
          ∀ φ, π φ = 0 ↔ ∃ ψ : K (i + 2) →ₗ[R] M, (φ : K (i + 1) →ₗ[R] M) = ψ ∘ₗ δ (i + 1)
```

### `Module.exists_twoTermComplex_kerMapBaseChange_bijective_of_flat_complex`

`Thm_Module_exists_twoTermComplex_kerMapBaseChange_bijective_of_flat_complex` — Two-term free model computing ker d⁰ after base change

```lean
theorem Module.exists_twoTermComplex_kerMapBaseChange_bijective_of_flat_complex
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbdd : ∀ i, n < i → Subsingleton (C i))
    (hfin0 : Module.Finite R (LinearMap.ker (d 0)))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype)) :
    ∃ (G : CoherentBaseChange.TwoTermComplex.{u, u} R) (ι0 : G.C0 →ₗ[R] C 0) (ι1 : G.C1 →ₗ[R] C 1)
      (comm : d 0 ∘ₗ ι0 = ι1 ∘ₗ G.d),
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Bijective (TwoChartCech.kerMapBaseChange G.d (d 0) ι0 ι1 comm A)
```

### `Module.faithfullyFlat_pi_localizationAway_of_span_eq_top`

`Thm_Module_faithfullyFlat_pi_localizationAway_of_span_eq_top` — Finite principal Zariski covers are faithfully flat

```lean
theorem Module.faithfullyFlat_pi_localizationAway_of_span_eq_top
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤) :
    Module.FaithfullyFlat S (∀ i : Fin k, Localization.Away (r i))
```

### `Module.faithfullyFlat_pi_of_forall_faithfullyFlat`

`Thm_Module_faithfullyFlat_pi_of_forall_faithfullyFlat` — Faithful flatness of a finite product of algebras

```lean
theorem Module.faithfullyFlat_pi_of_forall_faithfullyFlat
    {k : ℕ} (C : Fin k → Type) [∀ i, CommRing (C i)] (D : Fin k → Type) [∀ i, CommRing (D i)] [∀ i, Algebra (C i) (D i)]
    [inst : Algebra (∀ i, C i) (∀ i, D i)]
    (halg : ∀ (i : Fin k) (x : ∀ i, C i), algebraMap (∀ i, C i) (∀ i, D i) x i = algebraMap (C i) (D i) (x i))
    (hff : ∀ i, Module.FaithfullyFlat (C i) (D i)) :
    @Module.FaithfullyFlat (∀ i, C i) (∀ i, D i) _ _ inst.toModule
```

### `Module.faithfullyFlat_pi_of_forall_faithfullyFlat_localizationAway_of_span_eq_top`

`Thm_Module_faithfullyFlat_pi_of_forall_faithfullyFlat_localizationAway_of_span_eq_top` — Faithful flatness of a product over a basic open cover

```lean
theorem Module.faithfullyFlat_pi_of_forall_faithfullyFlat_localizationAway_of_span_eq_top
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (S' : Fin k → Type u) [∀ i, CommRing (S' i)] [∀ i, Algebra S (S' i)]
    [∀ i, Algebra (Localization.Away (r i)) (S' i)] [∀ i, IsScalarTower S (Localization.Away (r i)) (S' i)]
    (hff : ∀ i, Module.FaithfullyFlat (Localization.Away (r i)) (S' i)) :
    Module.FaithfullyFlat S (∀ i : Fin k, S' i)
```

### `Module.finitePresentation_of_rankAtStalk_eq`

`Thm_Module_finitePresentation_of_rankAtStalk_eq` — Finite flat modules of constant stalk rank are finitely presented

```lean
theorem Module.finitePresentation_of_rankAtStalk_eq {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M] (n : ℕ)
    (h : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = n) : Module.FinitePresentation R M
```

### `Module.finite_and_faithfullyFlat_of_faithfullyFlat_tensorProduct`

`Thm_Module_finite_and_faithfullyFlat_of_faithfullyFlat_tensorProduct` — Descent of finiteness and faithful flatness along faithfully flat base change

```lean
theorem Module.finite_and_faithfullyFlat_of_faithfullyFlat_tensorProduct
    {R : Type u} [CommRing R] (W : Type v) [CommRing W] [Algebra R W] [Module.FaithfullyFlat R W]
    (M : Type w) [AddCommGroup M] [Module R M]
    [Module.Finite W (W ⊗[R] M)] [Module.FaithfullyFlat W (W ⊗[R] M)] :
    Module.Finite R M ∧ Module.FaithfullyFlat R M
```

### `Module.finite_and_finrank_eq_sum_length_localizedModule_of_forall_subsingleton`

`Thm_Module_finite_and_finrank_eq_sum_length_localizedModule_of_forall_subsingleton` — Finite-dimensionality and length formula for modules with finite support

```lean
theorem Module.finite_and_finrank_eq_sum_length_localizedModule_of_forall_subsingleton
    (k : Type u) [Field k] [IsAlgClosed k]
    (S : Type u) [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (H : Type u) [AddCommGroup H] [Module S H] [Module k H] [IsScalarTower k S H] [Module.Finite S H]
    (T : Finset (MaximalSpectrum S))
    (hT : ∀ 𝔪 : MaximalSpectrum S, 𝔪 ∉ T → Subsingleton (LocalizedModule 𝔪.asIdeal.primeCompl H)) :
    Module.Finite k H ∧ IsFiniteLength S H ∧
      (Module.finrank k H : ℕ∞) =
        ∑ 𝔪 ∈ T, Module.length (Localization.AtPrime 𝔪.asIdeal) (LocalizedModule 𝔪.asIdeal.primeCompl H)
```

### `Module.finite_projective_ker_baseChange_of_forall_exists_isUnit`

`Thm_Module_finite_projective_ker_baseChange_of_forall_exists_isUnit` — Zariski-local criterion for ker(δ⊗ A) finite projective of rank r

```lean
theorem Module.finite_projective_ker_baseChange_of_forall_exists_isUnit
    {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
    {C0 C1 F : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [AddCommGroup F] [Module R F]
    (δ : C0 →ₗ[R] C1) (Θ : F →ₗ[R] C0) (r : ℕ)
    (hloc : ∀ 𝔮 : PrimeSpectrum A, ∃ g : R, algebraMap R A g ∉ 𝔮.asIdeal ∧
      ∀ (A' : Type u) [CommRing A'] [Algebra R A'], IsUnit (algebraMap R A' g) →
        Module.Finite A' (LinearMap.ker (δ.baseChange A')) ∧
        Module.Projective A' (LinearMap.ker (δ.baseChange A')) ∧
        (∀ 𝔮' : PrimeSpectrum A', Module.rankAtStalk (LinearMap.ker (δ.baseChange A')) 𝔮' = r) ∧
        LinearMap.ker (δ.baseChange A') ≤ LinearMap.range (Θ.baseChange A')) :
    Module.Finite A (LinearMap.ker (δ.baseChange A)) ∧
    Module.Projective A (LinearMap.ker (δ.baseChange A)) ∧
    (∀ 𝔮 : PrimeSpectrum A, Module.rankAtStalk (LinearMap.ker (δ.baseChange A)) 𝔮 = r) ∧
    LinearMap.ker (δ.baseChange A) ≤ LinearMap.range (Θ.baseChange A)
```

### `Module.finrank_add_alternatingSum_finrank_eq_of_finite_complex`

`Thm_Module_finrank_add_alternatingSum_finrank_eq_of_finite_complex` — Euler characteristic of a bounded complex of finite-dimensional vector spaces

```lean
theorem Module.finrank_add_alternatingSum_finrank_eq_of_finite_complex
    (k : Type u) [Field k]
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module k (K i)] [∀ i, Module.Finite k (K i)]
    (δ : ∀ i, K i →ₗ[k] K (i + 1)) (hδδ : ∀ i, δ (i + 1) ∘ₗ δ i = 0)
    (n : ℕ) (hbdd : ∀ i, n < i → Subsingleton (K i))
    (H0 : Type u) [AddCommGroup H0] [Module k H0] (e₀ : H0 ≃ₗ[k] LinearMap.ker (δ 0))
    (H : ℕ → Type u) [∀ i, AddCommGroup (H i)] [∀ i, Module k (H i)]
    (π : ∀ i, LinearMap.ker (δ (i + 1)) →ₗ[k] H i) (hπ : ∀ i, Function.Surjective (π i))
    (hπker : ∀ i, LinearMap.ker (π i) =
      (LinearMap.range (δ i)).comap (LinearMap.ker (δ (i + 1))).subtype) :
    (Module.finrank k H0 : ℤ) + ∑ i ∈ Finset.range n, (-1 : ℤ) ^ (i + 1) * (Module.finrank k (H i) : ℤ) =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (Module.finrank k (K i) : ℤ)
```

### `Module.finrank_baseChange_eq_of_quotient_squareZero_linearEquiv`

`Thm_Module_finrank_baseChange_eq_of_quotient_squareZero_linearEquiv` — Constant rank descends along a square-zero quotient

```lean
theorem Module.finrank_baseChange_eq_of_quotient_squareZero_linearEquiv
    {R : Type u} [CommRing R] (J : Ideal R) (hJ : J ^ 2 = ⊥)
    {S : Type u} [CommRing S] (φ : R ⧸ J ≃+* S)
    (P : Type u) [AddCommGroup P] [Module S P]
    (P' : Type u) [AddCommGroup P'] [Module R P'] {n : ℕ}
    (hrk : ∀ (K : Type u) [Field K] [Algebra S K], Module.finrank K (K ⊗[S] P) = n) :
    letI : Module (R ⧸ J) P := Module.compHom P φ.toRingHom
    ((R ⧸ J) ⊗[R] P' ≃ₗ[R ⧸ J] P) →
    ∀ (K : Type u) [Field K] [Algebra R K], Module.finrank K (K ⊗[R] P') = n
```

### `Module.finrank_baseChange_eq_one_of_rankAtStalk_eq_one`

`Thm_Module_finrank_baseChange_eq_one_of_rankAtStalk_eq_one` — Constant stalk rank one gives one-dimensional fibre over any field

```lean
theorem Module.finrank_baseChange_eq_one_of_rankAtStalk_eq_one
    {R : Type u} [CommRing R] (P : Type u) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Flat R P]
    (h : ∀ 𝔭, Module.rankAtStalk (R := R) P 𝔭 = 1)
    (K : Type u) [Field K] [Algebra R K] :
    Module.finrank K (K ⊗[R] P) = 1
```

### `Module.finrank_eq_mul_of_tensorProduct_linearEquiv_baseChange`

`Thm_Module_finrank_eq_mul_of_tensorProduct_linearEquiv_baseChange` — Dimension of a faithfully flat algebra trivialised by base change

```lean
theorem Module.finrank_eq_mul_of_tensorProduct_linearEquiv_baseChange
    {κ : Type u} [Field κ] {B C D : Type u} [CommRing B] [CommRing C] [Algebra κ B] [Algebra κ C]
    [Algebra B C] [IsScalarTower κ B C] [AddCommGroup D] [Module κ D]
    [Module.Finite κ B] [Module.Finite κ C] [Module.Finite κ D] [Module.FaithfullyFlat B C]
    (e : C ⊗[B] C ≃ₗ[C] C ⊗[κ] D) :
    Module.finrank κ C = Module.finrank κ D * Module.finrank κ B
```

### `Module.finrank_iInf_ker_baseChange_eq_finrank_iInf_ker`

`Thm_Module_finrank_iInf_ker_baseChange_eq_finrank_iInf_ker` — Joint kernel dimension is invariant under field extension

```lean
theorem Module.finrank_iInf_ker_baseChange_eq_finrank_iInf_ker
    (F : Type) [Field F] (K : Type) [Field K] [Algebra F K]
    (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V]
    {ι : Type} (T : ι → (V →ₗ[F] V)) :
    Module.finrank K ↥(⨅ i, LinearMap.ker ((T i).baseChange K)) =
      Module.finrank F ↥(⨅ i, LinearMap.ker (T i))
```

### `Module.finrank_quotSMulTop_eq`

`Thm_Module_finrank_quotSMulTop_eq` — Rank is unchanged modulo a regular element

```lean
theorem Module.finrank_quotSMulTop_eq {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M] (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular M x) (hfree : Module.Free (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) :
    Module.finrank (R ⧸ Ideal.span {x}) (QuotSMulTop x M) = Module.finrank R M
```

### `Module.finrank_torsionBySet_ker_eq_finrank_quotient_mul_finrank_iInf_eigenspace_baseChange`

`Thm_Module_finrank_torsionBySet_ker_eq_finrank_quotient_mul_finrank_iInf_eigenspace_baseChange` — Rank of the kerχ-torsion submodule after base change

```lean
theorem Module.finrank_torsionBySet_ker_eq_finrank_quotient_mul_finrank_iInf_eigenspace_baseChange
    {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    {T : Type*} [CommRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T]
    {M : Type*} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.IsTorsionFree 𝒪 M]
    {A : Type*} [CommRing A] [IsDomain A] [Algebra 𝒪 A] [Module.Finite 𝒪 A]
    [Module.IsTorsionFree 𝒪 A]
    (χ : T →ₐ[𝒪] A) :
    Module.finrank 𝒪 ↥(Submodule.torsionBySet T M ↑(RingHom.ker χ)) =
      Module.finrank 𝒪 (T ⧸ RingHom.ker χ) *
        Module.finrank A ↥(⨅ t : T, Module.End.eigenspace
          (((LinearMap.lsmul T M t).restrictScalars 𝒪).baseChange A) (χ t))
```

### `Module.flat_of_comap_maximalIdeal_rTensor_injective`

`Thm_Module_flat_of_comap_maximalIdeal_rTensor_injective` — Local criterion for flatness at a contracted prime

```lean
theorem Module.flat_of_comap_maximalIdeal_rTensor_injective
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [Module.Finite S M]
    (p : Ideal R) (hp : (IsLocalRing.maximalIdeal S).comap (algebraMap R S) = p)
    (h : Function.Injective (p.subtype.rTensor M)) :
    Module.Flat R M
```

### `Module.flat_of_isLocalHom_of_finite_of_isZero_tor_one_residueField`

`Thm_Module_flat_of_isLocalHom_of_finite_of_isZero_tor_one_residueField` — Local criterion for flatness via Tor₁^R(κ_R,M)

```lean
theorem Module.flat_of_isLocalHom_of_finite_of_isZero_tor_one_residueField
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [IsNoetherianRing R] [IsNoetherianRing S]
    {M : Type u} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M]
    (hκ : IsZero (((Tor (ModuleCat.{u} R) 1).obj
      (ModuleCat.of R (ResidueField R))).obj (ModuleCat.of R M))) :
    Module.Flat R M
```

### `Module.flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero`

`Thm_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero` — Local criterion for flatness via Tor₁ over the residue field

```lean
theorem Module.flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero
    {R : Type} [CommRing R] {S : Type} [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [IsNoetherianRing R] [IsNoetherianRing S]
    {M : Type} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M]
    (hκ : IsZero (((Tor (ModuleCat.{0} R) 1).obj
      (ModuleCat.of R (IsLocalRing.ResidueField R))).obj (ModuleCat.of R M))) :
    Module.Flat R M
```

### `Module.flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero_univ`

`Thm_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero_univ` — Local criterion for flatness via Tor₁

```lean
theorem Module.flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero_univ
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [IsNoetherianRing R] [IsNoetherianRing S]
    {M : Type u} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M]
    (hκ : IsZero (((Tor (ModuleCat.{u} R) 1).obj
      (ModuleCat.of R (IsLocalRing.ResidueField R))).obj (ModuleCat.of R M))) :
    Module.Flat R M
```

### `Module.flat_of_maximalIdeal_rTensor_injective_of_isLocalHom`

`Thm_Module_flat_of_maximalIdeal_rTensor_injective_of_isLocalHom` — Local flatness criterion for a finite module over a local extension

```lean
theorem Module.flat_of_maximalIdeal_rTensor_injective_of_isLocalHom
    {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (M : Type u) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M] [Module.Finite B M]
    (h : Function.Injective (LinearMap.rTensor M (maximalIdeal A).subtype)) :
    Module.Flat A M
```

### `Module.forall_baseChange_localization_eq_zero_and_mem_range_of_forall_baseChange_field`

`Thm_Module_forall_baseChange_localization_eq_zero_and_mem_range_of_forall_baseChange_field` — Acyclicity over the residue field gives acyclicity after localisation

```lean
theorem Module.forall_baseChange_localization_eq_zero_and_mem_range_of_forall_baseChange_field
    (S : Type u) [CommRing S] (𝔪 : Ideal S) [𝔪.IsMaximal] (n : ℕ)
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module S (K i)]
    [∀ i, Module.Finite S (K i)] [∀ i, Module.Projective S (K i)]
    (hbdd : ∀ i, n < i → Subsingleton (K i))
    (δ : ∀ i, K i →ₗ[S] K (i + 1)) (hdd : ∀ i, δ (i + 1) ∘ₗ δ i = 0)
    (B : Type u) [Field B] [Algebra S B] (hB : Function.Surjective (algebraMap S B))
    (h𝔪 : 𝔪 ≤ RingHom.ker (algebraMap S B))
    (h0 : ∀ z : B ⊗[S] K 0, (δ 0).baseChange B z = 0 → z = 0)
    (hS : ∀ (i : ℕ) (z : B ⊗[S] K (i + 1)), (δ (i + 1)).baseChange B z = 0 →
      z ∈ LinearMap.range ((δ i).baseChange B)) :
    (∀ z : Localization.AtPrime 𝔪 ⊗[S] K 0, (δ 0).baseChange (Localization.AtPrime 𝔪) z = 0 → z = 0) ∧
      ∀ (i : ℕ) (z : Localization.AtPrime 𝔪 ⊗[S] K (i + 1)),
        (δ (i + 1)).baseChange (Localization.AtPrime 𝔪) z = 0 →
          z ∈ LinearMap.range ((δ i).baseChange (Localization.AtPrime 𝔪))
```

### `Module.forall_eq_zero_and_mem_range_of_forall_baseChange_residueField_of_finite_free`

`Thm_Module_forall_eq_zero_and_mem_range_of_forall_baseChange_residueField_of_finite_free` — Nakayama acyclicity for complexes of finite free modules

```lean
theorem Module.forall_eq_zero_and_mem_range_of_forall_baseChange_residueField_of_finite_free
    (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ)
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)]
    [∀ i, Module.Finite R (K i)] [∀ i, Module.Free R (K i)]
    (hbdd : ∀ i, n < i → Subsingleton (K i))
    (δ : ∀ i, K i →ₗ[R] K (i + 1)) (hdd : ∀ i, δ (i + 1) ∘ₗ δ i = 0)
    (h0 : ∀ z : (R ⧸ IsLocalRing.maximalIdeal R) ⊗[R] K 0,
      (δ 0).baseChange (R ⧸ IsLocalRing.maximalIdeal R) z = 0 → z = 0)
    (hS : ∀ (i : ℕ) (z : (R ⧸ IsLocalRing.maximalIdeal R) ⊗[R] K (i + 1)),
      (δ (i + 1)).baseChange (R ⧸ IsLocalRing.maximalIdeal R) z = 0 →
        z ∈ LinearMap.range ((δ i).baseChange (R ⧸ IsLocalRing.maximalIdeal R))) :
    (∀ z : K 0, δ 0 z = 0 → z = 0) ∧
      ∀ (i : ℕ) (z : K (i + 1)), δ (i + 1) z = 0 → z ∈ LinearMap.range (δ i)
```

### `Module.forall_eq_zero_and_mem_range_of_isWeaklyRegular_complex`

`Thm_Module_forall_eq_zero_and_mem_range_of_isWeaklyRegular_complex` — Acyclicity in degrees below the length of rs

```lean
theorem Module.forall_eq_zero_and_mem_range_of_isWeaklyRegular_complex
    (R : Type u) [CommRing R] (rs : List R)
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)]
    (hreg : ∀ i, RingTheory.Sequence.IsWeaklyRegular (K i) rs)
    (δ : ∀ i, K i →ₗ[R] K (i + 1)) (hdd : ∀ i, δ (i + 1) ∘ₗ δ i = 0)
    (htors0 : ∃ N : ℕ, ∀ a ∈ Ideal.ofList rs ^ N, ∀ z : K 0, δ 0 z = 0 → a • z = 0)
    (htors : ∀ i, ∃ N : ℕ, ∀ a ∈ Ideal.ofList rs ^ N, ∀ z : K (i + 1), δ (i + 1) z = 0 →
      a • z ∈ LinearMap.range (δ i)) :
    (0 < rs.length → ∀ z : K 0, δ 0 z = 0 → z = 0) ∧
      ∀ i : ℕ, i + 1 < rs.length → ∀ z : K (i + 1), δ (i + 1) z = 0 → z ∈ LinearMap.range (δ i)
```

### `Module.free_and_finrank_eq_of_finrank_eq_mul_of_finrank_residueField_tensor_le`

`Thm_Module_free_and_finrank_eq_of_finrank_eq_mul_of_finrank_residueField_tensor_le` — Freeness over a local algebra from a rank count

```lean
theorem Module.free_and_finrank_eq_of_finrank_eq_mul_of_finrank_residueField_tensor_le
    {𝒪 A M : Type*} [CommRing 𝒪] [IsDomain 𝒪] [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
    [Module.Finite 𝒪 A] [Module.Free 𝒪 A]
    [AddCommGroup M] [Module 𝒪 M] [Module A M] [IsScalarTower 𝒪 A M]
    [Module.Finite 𝒪 M] [Module.Free 𝒪 M]
    (d : ℕ) (hd : Module.finrank (ResidueField A) (ResidueField A ⊗[A] M) ≤ d)
    (hM : Module.finrank 𝒪 M = d * Module.finrank 𝒪 A) :
    Module.Free A M ∧ Module.finrank A M = d
```

### `Module.free_and_finrank_eq_of_finrank_residueField_tensor_eq_of_finrank_fractionRing_tensor_eq`

`Thm_Module_free_and_finrank_eq_of_finrank_residueField_tensor_eq_of_finrank_fractionRing_tensor_eq` — Equal residue- and generic-fibre dimensions force freeness

```lean
theorem Module.free_and_finrank_eq_of_finrank_residueField_tensor_eq_of_finrank_fractionRing_tensor_eq
    {A : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    {C : Type*} [AddCommGroup C] [Module A C] [Module.Finite A C] (n : ℕ)
    (hκ : Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A ⊗[A] C) = n)
    (hK : Module.finrank (FractionRing A) (FractionRing A ⊗[A] C) = n) :
    Module.Free A C ∧ Module.finrank A C = n
```

### `Module.free_and_finrank_tensorProduct_quot_span_tmul_pow_sub_eq_mul`

`Thm_Module_free_and_finrank_tensorProduct_quot_span_tmul_pow_sub_eq_mul` — Degree of a power of a finite map: rank nm

```lean
theorem Module.free_and_finrank_tensorProduct_quot_span_tmul_pow_sub_eq_mul
    (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] (a : A) (m n : ℕ) (hn : 1 ≤ n)
    (hfin : (Polynomial.aeval a : R[X] →ₐ[R] A).toRingHom.Finite)
    (h : ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S),
      Module.Finite S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] a - s ⊗ₜ[R] (1 : A)}) ∧
      Module.Free S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] a - s ⊗ₜ[R] (1 : A)}) ∧
      Module.finrank S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] a - s ⊗ₜ[R] (1 : A)}) = m)
    (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S) :
    Module.Finite S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] (a ^ n) - s ⊗ₜ[R] (1 : A)}) ∧
      Module.Free S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] (a ^ n) - s ⊗ₜ[R] (1 : A)}) ∧
      Module.finrank S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] (a ^ n) - s ⊗ₜ[R] (1 : A)}) = n * m
```

### `Module.free_coker_and_ker_baseChange_of_ker_le_range_residueField`

`Thm_Module_free_coker_and_ker_baseChange_of_ker_le_range_residueField` — Base change in degree 0 for a complex with finite free tail

```lean
theorem Module.free_coker_and_ker_baseChange_of_ker_le_range_residueField
    (R : Type u) [CommRing R] [IsLocalRing R]
    {C0 C1 C2 : Type v} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [AddCommGroup C2] [Module R C2] [Module.Finite R C1] [Module.Free R C1] [Module.Finite R C2] [Module.Free R C2]
    (d0 : C0 →ₗ[R] C1) (d1 : C1 →ₗ[R] C2) (hdd : d1 ∘ₗ d0 = 0)
    (hH1 : LinearMap.ker (d1.baseChange (IsLocalRing.ResidueField R)) ≤
      LinearMap.range (d0.baseChange (IsLocalRing.ResidueField R))) :
    Module.Free R (C1 ⧸ LinearMap.range d0) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        LinearMap.range ((LinearMap.ker d0).subtype.baseChange A) = LinearMap.ker (d0.baseChange A) ∧
          Function.Injective ((LinearMap.ker d0).subtype.baseChange A)
```

### `Module.free_of_depth_eq_ringKrullDim_of_isRegularLocalRing`

`Thm_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing` — Finite modules of depth dim R over regular local rings are free

```lean
theorem Module.free_of_depth_eq_ringKrullDim_of_isRegularLocalRing
    (R : Type*) [CommRing R] [IsRegularLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (H : (Module.depth R M : WithBot ℕ∞) = ringKrullDim R) : Module.Free R M
```

### `Module.free_of_isIntegrallyClosed_of_finite_of_isRegularLocalRing_of_ringKrullDim_le_two`

`Thm_Module_free_of_isIntegrallyClosed_of_finite_of_isRegularLocalRing_of_ringKrullDim_le_two` — Normal domains finite over regular local rings of dimension ≤ 2 are free

```lean
theorem Module.free_of_isIntegrallyClosed_of_finite_of_isRegularLocalRing_of_ringKrullDim_le_two
    (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R] (hdim : ringKrullDim R ≤ 2)
    (B : Type u) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra R B] [Module.Finite R B]
    [FaithfulSMul R B] :
    Module.Free R B
```

### `Module.free_of_isRegular_of_span_eq_maximalIdeal`

`Thm_Module_free_of_isRegular_of_span_eq_maximalIdeal` — Regular sequence generating 𝔪 forces freeness

```lean
theorem Module.free_of_isRegular_of_span_eq_maximalIdeal
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (rs : List A) (hA : RingTheory.Sequence.IsRegular A rs) (hspan : Ideal.ofList rs = IsLocalRing.maximalIdeal A)
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] (hM : RingTheory.Sequence.IsRegular M rs) :
    Module.Free A M
```

### `Module.free_of_isWeaklyRegular_of_isRegular_ofList_eq_maximalIdeal`

`Thm_Module_free_of_isWeaklyRegular_of_isRegular_ofList_eq_maximalIdeal` — Freeness from a full-length weakly regular sequence

```lean
theorem Module.free_of_isWeaklyRegular_of_isRegular_ofList_eq_maximalIdeal
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (xs : List R) (hxs : RingTheory.Sequence.IsRegular R xs)
    (hspan : Ideal.ofList xs = IsLocalRing.maximalIdeal R)
    (s : List R) (hs : ∀ r ∈ s, r ∈ IsLocalRing.maximalIdeal R)
    (hreg : RingTheory.Sequence.IsWeaklyRegular M s) (hlen : s.length = xs.length)
    (hfl : IsFiniteLength R (M ⧸ (Ideal.ofList s • ⊤ : Submodule R M))) :
    Module.Free R M
```

### `Module.free_of_quotSMulTop_free`

`Thm_Module_free_of_quotSMulTop_free` — Freeness descends from M/xM along a regular element

```lean
theorem Module.free_of_quotSMulTop_free {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M] (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular M x) (hfree : Module.Free (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) :
    Module.Free R M
```

### `Module.free_of_torsionBySet_eq_annihilator_smul`

`Thm_Module_free_of_torsionBySet_eq_annihilator_smul` — Freeness over T from saturation, duality and rank equality

```lean
theorem Module.free_of_torsionBySet_eq_annihilator_smul
    {𝒪 : Type u} {T : Type w} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    [CommRing T] [IsLocalRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (πT : T →ₐ[𝒪] 𝒪) (hη : (RingHom.ker πT).annihilator.map πT ≠ ⊥)
    (C : T →ₗ[𝒪] T →ₗ[𝒪] 𝒪) (hC : ∀ s t u : T, C (s * t) u = C t (s * u)) (hCb : Function.Bijective C)
    (M : Type x) [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.Free 𝒪 M]
    (B : M →ₗ[𝒪] M →ₗ[𝒪] 𝒪) (hB : ∀ (t : T) (m n : M), B (t • m) n = B m (t • n))
    (hBb : Function.Bijective B)
    (hrank : Module.finrank 𝒪 M =
      Module.finrank 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) * Module.finrank 𝒪 T)
    (hsat : Submodule.torsionBySet T M ↑(RingHom.ker πT) = (RingHom.ker πT).annihilator • ⊤) :
    Module.Free T M
```

### `Module.free_quotient_range_of_ker_baseChange_residueField_le`

`Thm_Module_free_quotient_range_of_ker_baseChange_residueField_le` — Cokernel of a map to a finite free module is free when residual relations lift

```lean
theorem Module.free_quotient_range_of_ker_baseChange_residueField_le
    {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type v} {N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] [Module.Free R N] (f : M →ₗ[R] N)
    (h : LinearMap.ker (f.baseChange (IsLocalRing.ResidueField R)) ≤
      LinearMap.range ((LinearMap.ker f).subtype.baseChange (IsLocalRing.ResidueField R))) :
    Module.Free R (N ⧸ LinearMap.range f)
```

### `Module.isClosed_setOf_le_finrank_cohomology_baseChange_residueField_of_projective`

`Thm_Module_isClosed_setOf_le_finrank_cohomology_baseChange_residueField_of_projective` — Upper semicontinuity of Čech cohomology ranks over Spec R

```lean
theorem Module.isClosed_setOf_le_finrank_cohomology_baseChange_residueField_of_projective
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)]
    [∀ i, Module.Finite R (K i)] [∀ i, Module.Projective R (K i)]
    (δ : ∀ i, K i →ₗ[R] K (i + 1)) (hδδ : ∀ i, δ (i + 1) ∘ₗ δ i = 0) (r : ℕ) :
    IsClosed {q : PrimeSpectrum R | r ≤ Module.finrank q.asIdeal.ResidueField
        ↥(LinearMap.ker ((δ 0).baseChange q.asIdeal.ResidueField))} ∧
      ∀ i : ℕ, IsClosed {q : PrimeSpectrum R |
        r + Module.finrank q.asIdeal.ResidueField
            ↥((LinearMap.range ((δ i).baseChange q.asIdeal.ResidueField)).comap
              (LinearMap.ker ((δ (i + 1)).baseChange q.asIdeal.ResidueField)).subtype) ≤
          Module.finrank q.asIdeal.ResidueField
            ↥(LinearMap.ker ((δ (i + 1)).baseChange q.asIdeal.ResidueField))}
```

### `Module.isClosed_setOf_range_le_smul_top`

`Thm_Module_isClosed_setOf_range_le_smul_top` — Closedness of the locus where im f ⊆ 𝔭 Q

```lean
theorem Module.isClosed_setOf_range_le_smul_top
    {R : Type*} [CommRing R] {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [Module.Finite R Q] [Module.Projective R Q] (f : P →ₗ[R] Q) :
    IsClosed {x : PrimeSpectrum R | LinearMap.range f ≤ x.asIdeal • (⊤ : Submodule R Q)}
```

### `Module.ker_baseChange_field_of_subsingleton_H1`

`Thm_Module_ker_baseChange_field_of_subsingleton_H1` — Degree-zero cohomology and base change when H¹ vanishes

```lean
theorem Module.ker_baseChange_field_of_subsingleton_H1
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbdd : ∀ i, n < i → Subsingleton (C i))
    (hfin0 : Module.Finite R (LinearMap.ker (d 0)))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype))
    (K : Type u) [Field K] [Algebra R K]
    (hH1 : LinearMap.ker ((d 1).baseChange K) ≤ LinearMap.range ((d 0).baseChange K)) :
    LinearMap.range ((LinearMap.ker (d 0)).subtype.baseChange K) = LinearMap.ker ((d 0).baseChange K) ∧
      Function.Injective ((LinearMap.ker (d 0)).subtype.baseChange K)
```

### `Module.ker_baseChange_field_of_subsingleton_H1_of_projective`

`Thm_Module_ker_baseChange_field_of_subsingleton_H1_of_projective` — Degree-zero base change to a field with vanishing H¹

```lean
theorem Module.ker_baseChange_field_of_subsingleton_H1_of_projective
    (R : Type u) [CommRing R]
    {C0 C1 C2 : Type v} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [AddCommGroup C2] [Module R C2]
    [Module.Finite R C1] [Module.Projective R C1] [Module.Finite R C2] [Module.Projective R C2]
    (d0 : C0 →ₗ[R] C1) (d1 : C1 →ₗ[R] C2) (hdd : d1 ∘ₗ d0 = 0)
    (K : Type u) [Field K] [Algebra R K]
    (hH1 : LinearMap.ker (d1.baseChange K) ≤ LinearMap.range (d0.baseChange K)) :
    LinearMap.range ((LinearMap.ker d0).subtype.baseChange K) = LinearMap.ker (d0.baseChange K) ∧
      Function.Injective ((LinearMap.ker d0).subtype.baseChange K)
```

### `Module.ker_baseChange_le_range_and_finrank_eq_of_field_extension`

`Thm_Module_ker_baseChange_le_range_and_finrank_eq_of_field_extension` — Descent of exactness and ker dimension along K ⊆ K'

```lean
theorem Module.ker_baseChange_le_range_and_finrank_eq_of_field_extension
    {R : Type u} [CommRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1))
    {F : Type u} [AddCommGroup F] [Module R F] (Θ : F →ₗ[R] C 0)
    (K : Type u) [Field K] [Algebra R K] (K' : Type u) [Field K'] [Algebra R K'] [Algebra K K']
    [IsScalarTower R K K'] (r : ℕ)
    (h1 : ∀ i : ℕ, LinearMap.ker ((d (i + 1)).baseChange K') ≤ LinearMap.range ((d i).baseChange K'))
    (h2 : LinearMap.ker ((d 0).baseChange K') ≤ LinearMap.range (Θ.baseChange K'))
    (h3 : Module.finrank K' (LinearMap.ker ((d 0).baseChange K')) = r) :
    (∀ i : ℕ, LinearMap.ker ((d (i + 1)).baseChange K) ≤ LinearMap.range ((d i).baseChange K)) ∧
    LinearMap.ker ((d 0).baseChange K) ≤ LinearMap.range (Θ.baseChange K) ∧
    Module.finrank K (LinearMap.ker ((d 0).baseChange K)) = r
```

### `Module.length_quotient_comap_span_columns_eq_length_quotient_range_mulVecLin`

`Thm_Module_length_quotient_comap_span_columns_eq_length_quotient_range_mulVecLin` — Colength of a column span read in a rank-two basis

```lean
theorem Module.length_quotient_comap_span_columns_eq_length_quotient_range_mulVecLin
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
    (P : Submodule R M) (e : Fin 2 → M) (he : ∀ r, e r ∈ P)
    (heb : ∀ m ∈ P, ∃! w : Fin 2 → R, m = ∑ r, w r • e r)
    (A : Matrix (Fin 2) (Fin 2) R) :
    Module.length R (↥P ⧸ Submodule.comap P.subtype
        (Submodule.span R (Set.range fun s : Fin 2 => ∑ r, A r s • e r))) =
      Module.length R ((Fin 2 → R) ⧸ LinearMap.range (Matrix.mulVecLin A))
```

### `Module.length_quotient_le_of_ker_le`

`Thm_Module_length_quotient_le_of_ker_le` — Length of M/K bounded by length of N when ker f ⊆ K

```lean
theorem Module.length_quotient_le_of_ker_le
    {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (K : Submodule R M) (f : M →ₗ[R] N) (h : LinearMap.ker f ≤ K) :
    Module.length R (M ⧸ K) ≤ Module.length R N
```

### `Module.length_quotient_range_eq_length_dual_quotient_of_isRegular_of_exact`

`Thm_Module_length_quotient_range_eq_length_dual_quotient_of_isRegular_of_exact` — Length duality for top cokernels of finite free complexes

```lean
theorem Module.length_quotient_range_eq_length_dual_quotient_of_isRegular_of_exact
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (n : ℕ) (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (hlen : rs.length = n + 1)
    (hmax : Ideal.ofList rs = IsLocalRing.maximalIdeal R)
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)]
    [∀ i, Module.Finite R (K i)] [∀ i, Module.Free R (K i)]
    (hbdd : ∀ i, n + 1 < i → Subsingleton (K i))
    (δ : ∀ i, K i →ₗ[R] K (i + 1)) (hdd : ∀ i, δ (i + 1) ∘ₗ δ i = 0)
    (hex0 : ∀ z : K 0, δ 0 z = 0 → z = 0)
    (hex : ∀ i, i < n → ∀ z : K (i + 1), δ (i + 1) z = 0 → z ∈ LinearMap.range (δ i))
    (htors : ∃ N : ℕ, ∀ a ∈ IsLocalRing.maximalIdeal R ^ N, ∀ q : K (n + 1) ⧸ LinearMap.range (δ n), a • q = 0) :
    Module.length R (K (n + 1) ⧸ LinearMap.range (δ n)) =
      Module.length R (Module.Dual R (K 0) ⧸ LinearMap.range (δ 0).dualMap)
```

### `Module.length_quotient_torsionBySet_sup_eq_add_of_map_torsionBySet_eq`

`Thm_Module_length_quotient_torsionBySet_sup_eq_add_of_map_torsionBySet_eq` — Congruence module length growth along an adjoint pair

```lean
theorem Module.length_quotient_torsionBySet_sup_eq_add_of_map_torsionBySet_eq
    {𝒪 : Type u} {T T' : Type w} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    [CommRing T] [Algebra 𝒪 T] [CommRing T'] [Algebra 𝒪 T']
    (πT : T →ₐ[𝒪] 𝒪) (hη : (RingHom.ker πT).annihilator.map πT ≠ ⊥)
    (πT' : T' →ₐ[𝒪] 𝒪) (hη' : (RingHom.ker πT').annihilator.map πT' ≠ ⊥)
    (M : Type x) [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.Free 𝒪 M]
    (B : M →ₗ[𝒪] M →ₗ[𝒪] 𝒪) (hB : ∀ (t : T) (m n : M), B (t • m) n = B m (t • n))
    (hBb : Function.Bijective B)
    (M' : Type x) [AddCommGroup M'] [Module T' M'] [Module 𝒪 M'] [IsScalarTower 𝒪 T' M']
    [Module.Finite 𝒪 M'] [Module.Free 𝒪 M']
    (B' : M' →ₗ[𝒪] M' →ₗ[𝒪] 𝒪) (hB' : ∀ (t : T') (m n : M'), B' (t • m) n = B' m (t • n))
    (hBb' : Function.Bijective B')
    (i : M →ₗ[𝒪] M') (j : M' →ₗ[𝒪] M) (hadj : ∀ (m' : M') (m : M), B (j m') m = B' m' (i m))
    (Δ : T) (hji : ∀ m : M, j (i m) = Δ • m) (hΔ : πT Δ ≠ 0)
    (h℘ : Submodule.map i ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪) =
      (Submodule.torsionBySet T' M' ↑(RingHom.ker πT')).restrictScalars 𝒪) :
    Module.finrank 𝒪 (Submodule.torsionBySet T' M' ↑(RingHom.ker πT')) =
        Module.finrank 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) ∧
      Module.length 𝒪 (M' ⧸ (Submodule.torsionBySet T' M' ↑(RingHom.ker πT') ⊔
          Submodule.torsionBySet T' M' ↑(RingHom.ker πT').annihilator)) =
        Module.length 𝒪 (M ⧸ (Submodule.torsionBySet T M ↑(RingHom.ker πT) ⊔
          Submodule.torsionBySet T M ↑(RingHom.ker πT).annihilator)) +
        (Module.finrank 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) : ℕ∞) *
          Module.length 𝒪 (𝒪 ⧸ Ideal.span {πT Δ})
```

### `Module.length_quotient_torsionBySet_sup_eq_iff`

`Thm_Module_length_quotient_torsionBySet_sup_eq_iff` — Equality in the congruence-module bound iff M[wp]=I· M

```lean
theorem Module.length_quotient_torsionBySet_sup_eq_iff
    {𝒪 : Type u} {T : Type w} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    [CommRing T] [Algebra 𝒪 T] [Module.Free 𝒪 T]
    (πT : T →ₐ[𝒪] 𝒪) (hη : (RingHom.ker πT).annihilator.map πT ≠ ⊥)
    (M : Type x) [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.Free 𝒪 M] :
    Module.length 𝒪 (M ⧸ (Submodule.torsionBySet T M ↑(RingHom.ker πT) ⊔
        Submodule.torsionBySet T M ↑(RingHom.ker πT).annihilator)) =
      (Module.finrank 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) : ℕ∞) *
        Module.length 𝒪 (𝒪 ⧸ (RingHom.ker πT).annihilator.map πT) ↔
    Submodule.torsionBySet T M ↑(RingHom.ker πT) = (RingHom.ker πT).annihilator • ⊤
```

### `Module.length_quotient_torsionBySet_sup_le`

`Thm_Module_length_quotient_torsionBySet_sup_le` — Length bound for M/(M[wp]+M[I]) via the congruence ideal

```lean
theorem Module.length_quotient_torsionBySet_sup_le
    {𝒪 : Type u} {T : Type w} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    [CommRing T] [Algebra 𝒪 T] [Module.Free 𝒪 T]
    (πT : T →ₐ[𝒪] 𝒪) (hη : (RingHom.ker πT).annihilator.map πT ≠ ⊥)
    (M : Type x) [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.Free 𝒪 M] :
    Module.length 𝒪 (M ⧸ (Submodule.torsionBySet T M ↑(RingHom.ker πT) ⊔
        Submodule.torsionBySet T M ↑(RingHom.ker πT).annihilator)) ≤
      (Module.finrank 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) : ℕ∞) *
        Module.length 𝒪 (𝒪 ⧸ (RingHom.ker πT).annihilator.map πT)
```

### `Module.nonempty_dual_quotient_range_dualMap_linearEquiv_quotient_of_forall_surjective_iff`

`Thm_Module_nonempty_dual_quotient_range_dualMap_linearEquiv_quotient_of_forall_surjective_iff` — Cokernel of d^* is R/I under a kernel-lifting criterion

```lean
theorem Module.nonempty_dual_quotient_range_dualMap_linearEquiv_quotient_of_forall_surjective_iff
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (K₀ K₁ : Type u) [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Free R K₀]
    [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Free R K₁]
    (d : K₀ →ₗ[R] K₁)
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R) (hIN : ∃ N : ℕ, IsLocalRing.maximalIdeal R ^ N ≤ I)
    (hU : Module.finrank (R ⧸ IsLocalRing.maximalIdeal R)
      (LinearMap.ker (d.baseChange (R ⧸ IsLocalRing.maximalIdeal R))) = 1)
    (hW : ∀ (J' : Ideal R) (hJ' : J' ≤ IsLocalRing.maximalIdeal R), (∃ N : ℕ, IsLocalRing.maximalIdeal R ^ N ≤ J') →
      ((∀ z : (R ⧸ IsLocalRing.maximalIdeal R) ⊗[R] K₀, d.baseChange (R ⧸ IsLocalRing.maximalIdeal R) z = 0 →
          ∃ w : (R ⧸ J') ⊗[R] K₀, d.baseChange (R ⧸ J') w = 0 ∧
            LinearMap.rTensor K₀ (Submodule.factor hJ') w = z) ↔ I ≤ J')) :
    Nonempty ((Module.Dual R K₀ ⧸ LinearMap.range d.dualMap) ≃ₗ[R] (R ⧸ I))
```

### `Module.nonempty_linearEquiv_of_forall_exists_quotient_pow_smul_linearEquiv`

`Thm_Module_nonempty_linearEquiv_of_forall_exists_quotient_pow_smul_linearEquiv` — Guralnick's lifting theorem for varpi-torsion-free modules

```lean
theorem Module.nonempty_linearEquiv_of_forall_exists_quotient_pow_smul_linearEquiv
    {A : Type*} [CommRing A] [IsNoetherianRing A] (ϖ : A) (hϖ : ϖ ∈ Ideal.jacobson (⊥ : Ideal A))
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
    (hM : ∀ m : M, ϖ • m = 0 → m = 0) (hN : ∀ n : N, ϖ • n = 0 → n = 0)
    (h : ∀ k₀ : ℕ, ∃ k : ℕ, k₀ ≤ k ∧
      Nonempty ((M ⧸ LinearMap.range (ϖ ^ k • (LinearMap.id : M →ₗ[A] M))) ≃ₗ[A]
        (N ⧸ LinearMap.range (ϖ ^ k • (LinearMap.id : N →ₗ[A] N))))) :
    Nonempty (M ≃ₗ[A] N)
```

### `Module.nonempty_linearEquiv_of_linearEquiv_baseChange_of_finite`

`Thm_Module_nonempty_linearEquiv_of_linearEquiv_baseChange_of_finite` — Noether–Deuring theorem over a finite base field

```lean
theorem Module.nonempty_linearEquiv_of_linearEquiv_baseChange_of_finite
    (K : Type*) [Field K] [Finite K] (L : Type*) [CommRing L] [Nontrivial L] [Algebra K L]
    (A : Type*) [Ring A] [Algebra K A]
    (M N : Type*) [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]
    [Module.Finite K M]
    [AddCommGroup N] [Module A N] [Module K N] [IsScalarTower K A N] [Module.Finite K N]
    (e : L ⊗[K] M ≃ₗ[L] L ⊗[K] N)
    (he : ∀ (a : A) (x : L ⊗[K] M),
      e ((DistribSMul.toLinearMap K M a).baseChange L x) =
        (DistribSMul.toLinearMap K N a).baseChange L (e x)) :
    Nonempty (M ≃ₗ[A] N)
```

### `Module.projective_of_isReduced_of_finrank_fiber_const`

`Thm_Module_projective_of_isReduced_of_finrank_fiber_const` — Constant fibre dimension over a reduced ring implies projectivity

```lean
theorem Module.projective_of_isReduced_of_finrank_fiber_const {R : Type u} [CommRing R]
    [IsReduced R] {M : Type v} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
    {e : ℕ} (h : ∀ 𝔭 : PrimeSpectrum R,
      Module.finrank 𝔭.asIdeal.ResidueField (𝔭.asIdeal.ResidueField ⊗[R] M) = e) :
    Module.Projective R M
```

### `Module.quasiIso_baseChange_of_quasiIso_of_flat`

`Thm_Module_quasiIso_baseChange_of_quasiIso_of_flat` — Base change preserves quasi-isomorphisms of bounded flat complexes

```lean
theorem Module.quasiIso_baseChange_of_quasiIso_of_flat
    (R : Type u) [CommRing R]
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)] [∀ i, Module.Flat R (K i)]
    (δ : ∀ i, K i →ₗ[R] K (i + 1)) (hδδ : ∀ i, δ (i + 1) ∘ₗ δ i = 0)
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hKbdd : ∀ i, n < i → Subsingleton (K i)) (hCbdd : ∀ i, n < i → Subsingleton (C i))
    (φ : ∀ i, K i →ₗ[R] C i) (hφ : ∀ i, d i ∘ₗ φ i = φ (i + 1) ∘ₗ δ i)
    (h0inj : ∀ x : K 0, δ 0 x = 0 → φ 0 x = 0 → x = 0)
    (h0surj : ∀ y : C 0, d 0 y = 0 → ∃ x : K 0, δ 0 x = 0 ∧ φ 0 x = y)
    (hinj : ∀ (i : ℕ) (x : K (i + 1)), δ (i + 1) x = 0 → φ (i + 1) x ∈ LinearMap.range (d i) →
      x ∈ LinearMap.range (δ i))
    (hsurj : ∀ (i : ℕ) (y : C (i + 1)), d (i + 1) y = 0 →
      ∃ x : K (i + 1), δ (i + 1) x = 0 ∧ φ (i + 1) x - y ∈ LinearMap.range (d i))
    (A : Type u) [CommRing A] [Algebra R A] :
    (∀ x : A ⊗[R] K 0, (δ 0).baseChange A x = 0 → (φ 0).baseChange A x = 0 → x = 0) ∧
    (∀ y : A ⊗[R] C 0, (d 0).baseChange A y = 0 →
      ∃ x : A ⊗[R] K 0, (δ 0).baseChange A x = 0 ∧ (φ 0).baseChange A x = y) ∧
    (∀ (i : ℕ) (x : A ⊗[R] K (i + 1)), (δ (i + 1)).baseChange A x = 0 →
      (φ (i + 1)).baseChange A x ∈ LinearMap.range ((d i).baseChange A) →
        x ∈ LinearMap.range ((δ i).baseChange A)) ∧
    (∀ (i : ℕ) (y : A ⊗[R] C (i + 1)), (d (i + 1)).baseChange A y = 0 →
      ∃ x : A ⊗[R] K (i + 1), (δ (i + 1)).baseChange A x = 0 ∧
        (φ (i + 1)).baseChange A x - y ∈ LinearMap.range ((d i).baseChange A))
```

### `Module.rankAtStalk_eq_of_forall_localizedModule_equiv`

`Thm_Module_rankAtStalk_eq_of_forall_localizedModule_equiv` — Rank at stalk is invariant under local isomorphism

```lean
theorem Module.rankAtStalk_eq_of_forall_localizedModule_equiv
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A]
    (M N : Type u) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    [Module.Finite R M] [Module.Flat R M]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    [Module.Finite R N] [Module.Flat R N] (s : Set A) (hs : Ideal.span s = ⊤)
    (H : ∀ h ∈ s, Nonempty
      (LocalizedModule (Submonoid.powers h) M ≃ₗ[A] LocalizedModule (Submonoid.powers h) N)) :
    Module.rankAtStalk (R := R) M = Module.rankAtStalk N
```

### `Module.span_det_submatrix_eq_of_ker_eq_span_range`

`Thm_Module_span_det_submatrix_eq_of_ker_eq_span_range` — Independence of the zeroth determinantal ideal of a presentation

```lean
theorem Module.span_det_submatrix_eq_of_ker_eq_span_range
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {k l : ℕ} (π : (Fin k → R) →ₗ[R] M) (hπ : Function.Surjective π)
    (X : Matrix (Fin k) (Fin l) R) (hX : LinearMap.ker π = Submodule.span R (Set.range fun j : Fin l => fun i => X i j))
    {k' l' : ℕ} (π' : (Fin k' → R) →ₗ[R] M) (hπ' : Function.Surjective π')
    (X' : Matrix (Fin k') (Fin l') R)
    (hX' : LinearMap.ker π' = Submodule.span R (Set.range fun j : Fin l' => fun i => X' i j)) :
    Ideal.span (Set.range fun c : Fin k → Fin l => (X.submatrix id c).det) =
      Ideal.span (Set.range fun c : Fin k' → Fin l' => (X'.submatrix id c).det)
```

### `Module.subsingleton_ext_and_length_ext_eq_length_of_isWeaklyRegular_of_ofList_eq_maximalIdeal`

`Thm_Module_subsingleton_ext_and_length_ext_eq_length_of_isWeaklyRegular_of_ofList_eq_maximalIdeal` — Length of Ext^g(N,R) over a regular local ring

```lean
theorem Module.subsingleton_ext_and_length_ext_eq_length_of_isWeaklyRegular_of_ofList_eq_maximalIdeal
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (rs : List R)
    (hreg : RingTheory.Sequence.IsWeaklyRegular R rs)
    (hmax : Ideal.ofList rs = IsLocalRing.maximalIdeal R)
    (N : Type u) [AddCommGroup N] [Module R N] [Module.Finite R N]
    (htors : ∃ k : ℕ, ∀ a ∈ IsLocalRing.maximalIdeal R ^ k, ∀ z : N, a • z = 0) :
    (∀ i : ℕ, i ≠ rs.length → Subsingleton (Abelian.Ext (ModuleCat.of R N) (ModuleCat.of R R) i)) ∧
      Module.length R (Abelian.Ext (ModuleCat.of R N) (ModuleCat.of R R) rs.length) = Module.length R N
```

### `Module.sum_dual_apply_eq_natCast_of_rankAtStalk_eq`

`Thm_Module_sum_dual_apply_eq_natCast_of_rankAtStalk_eq` — Dual family trace equals the constant stalk rank

```lean
theorem Module.sum_dual_apply_eq_natCast_of_rankAtStalk_eq
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    {n : ℕ} (x : Fin n → M) (φ : Fin n → (M →ₗ[A] A)) (hxφ : ∀ m : M, ∑ i, φ i m • x i = m)
    (d : ℕ) (hd : ∀ p : PrimeSpectrum A, Module.rankAtStalk M p = d) :
    ∑ i, φ i (x i) = (d : A)
```

### `Module.toNat_length_ker_add_sum_neg_one_pow_toNat_length_eq_neg_one_pow_mul_toNat_length_quotient`

`Thm_Module_toNat_length_ker_add_sum_neg_one_pow_toNat_length_eq_neg_one_pow_mul_toNat_length_quotient` — Local alternating length formula for a bounded free complex

```lean
theorem Module.toNat_length_ker_add_sum_neg_one_pow_toNat_length_eq_neg_one_pow_mul_toNat_length_quotient
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (g : ℕ) (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (hlen : rs.length = g)
    (hmax : Ideal.ofList rs = IsLocalRing.maximalIdeal R)
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)]
    [∀ i, Module.Finite R (K i)] [∀ i, Module.Free R (K i)]
    (hbdd : ∀ i, g < i → Subsingleton (K i))
    (δ : ∀ i, K i →ₗ[R] K (i + 1)) (hdd : ∀ i, δ (i + 1) ∘ₗ δ i = 0)
    (N : ℕ)
    (htors0 : ∀ a ∈ IsLocalRing.maximalIdeal R ^ N, ∀ z : LinearMap.ker (δ 0), a • z = 0)
    (htors : ∀ (i : ℕ), ∀ a ∈ IsLocalRing.maximalIdeal R ^ N,
      ∀ q : LinearMap.ker (δ (i + 1)) ⧸ (LinearMap.range (δ i)).comap (LinearMap.ker (δ (i + 1))).subtype, a • q = 0)
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R) (hIN : IsLocalRing.maximalIdeal R ^ N ≤ I)
    (hU : Module.finrank (R ⧸ IsLocalRing.maximalIdeal R)
      (LinearMap.ker ((δ 0).baseChange (R ⧸ IsLocalRing.maximalIdeal R))) = 1)
    (hW : ∀ (J' : Ideal R) (hJ' : J' ≤ IsLocalRing.maximalIdeal R), (∃ N : ℕ, IsLocalRing.maximalIdeal R ^ N ≤ J') →
      ((∀ z : (R ⧸ IsLocalRing.maximalIdeal R) ⊗[R] K 0, (δ 0).baseChange (R ⧸ IsLocalRing.maximalIdeal R) z = 0 →
          ∃ w : (R ⧸ J') ⊗[R] K 0, (δ 0).baseChange (R ⧸ J') w = 0 ∧
            LinearMap.rTensor (K 0) (Submodule.factor hJ') w = z) ↔ I ≤ J')) :
    ((Module.length R (LinearMap.ker (δ 0))).toNat : ℤ) +
        ∑ i ∈ Finset.range g, (-1) ^ (i + 1) *
          ((Module.length R (LinearMap.ker (δ (i + 1)) ⧸
            (LinearMap.range (δ i)).comap (LinearMap.ker (δ (i + 1))).subtype)).toNat : ℤ) =
      (-1) ^ g * ((Module.length R (R ⧸ I)).toNat : ℤ)
```

## MeasureTheory (131)

### `MeasureTheory.IsFundamentalDomain.iUnion_inv_smul_of_leftCosetRepresentatives`

`Thm_MeasureTheory_IsFundamentalDomain_iUnion_inv_smul_of_leftCosetRepresentatives` — Fundamental domain for a subgroup from coset representatives

```lean
theorem MeasureTheory.IsFundamentalDomain.iUnion_inv_smul_of_leftCosetRepresentatives
    {G X ι : Type*} [Group G] [MulAction G X] [MeasurableSpace X] [Countable ι]
    (μ : Measure X) (Γ₁ Γ₂ : Subgroup G) (hle : Γ₂ ≤ Γ₁) [Countable Γ₁]
    [MeasurableSpace G] [MeasurableSMul G X] [SMulInvariantMeasure G X μ]
    (𝓕 : Set X) (h𝓕 : IsFundamentalDomain Γ₁ 𝓕 μ)
    (R : ι → Γ₁) (hR : ∀ γ : Γ₁, ∃! i, ((R i)⁻¹ * γ : G) ∈ Γ₂) :
    IsFundamentalDomain Γ₂ (⋃ i, ((R i : G)⁻¹) • 𝓕) μ
```

### `MeasureTheory.IsFundamentalDomain.image_mulEquiv_op_subgroupOf`

`Thm_MeasureTheory_IsFundamentalDomain_image_mulEquiv_op_subgroupOf` — Transport of a right-translation fundamental domain along a group isomorphism

```lean
theorem MeasureTheory.IsFundamentalDomain.image_mulEquiv_op_subgroupOf
    {A B : Type*} [Group A] [Group B] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableMul A] [MeasurableMul B]
    (e : A ≃* B) (he : Measurable e) (he' : Measurable e.symm)
    (H : Subgroup A) (H' : Subgroup B) (hH : ∀ a : A, e a ∈ H' ↔ a ∈ H)
    (μ : Measure A) (D : Set A) (hD : IsFundamentalDomain H.op D μ) :
    IsFundamentalDomain H'.op (e '' D) (μ.map e)
```

### `MeasureTheory.IsFundamentalDomain.setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives`

`Thm_MeasureTheory_IsFundamentalDomain_setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives` — Unfolding an integral over coset translates of a fundamental domain

```lean
theorem MeasureTheory.IsFundamentalDomain.setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives
    {G X ι : Type*} [Group G] [MulAction G X] [MeasurableSpace X] [Countable ι]
    (μ : Measure X) (Γ₁ Γ₂ : Subgroup G) (hle : Γ₂ ≤ Γ₁) [Countable Γ₁]
    [MeasurableSpace G] [MeasurableSMul G X] [SMulInvariantMeasure G X μ]
    (𝓕 : Set X) (h𝓕 : IsFundamentalDomain Γ₁ 𝓕 μ)
    (R : ι → Γ₁) (hR : ∀ γ : Γ₁, ∃! i, ((R i)⁻¹ * γ : G) ∈ Γ₂) :
    (∀ f : X → ℝ≥0∞, Measurable f →
      ∫⁻ x in ⋃ i, ((R i : G)⁻¹) • 𝓕, f x ∂μ = ∫⁻ x in 𝓕, ∑' i, f ((R i : G)⁻¹ • x) ∂μ) ∧
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (h : X → E),
      AEStronglyMeasurable h μ →
      ∫⁻ x in 𝓕, ∑' i, ‖h ((R i : G)⁻¹ • x)‖ₑ ∂μ < ∞ →
      IntegrableOn h (⋃ i, ((R i : G)⁻¹) • 𝓕) μ ∧
      (∀ᵐ x ∂μ.restrict 𝓕, Summable fun i => ‖h ((R i : G)⁻¹ • x)‖) ∧
      ∫ x in ⋃ i, ((R i : G)⁻¹) • 𝓕, h x ∂μ = ∫ x in 𝓕, ∑' i, h ((R i : G)⁻¹ • x) ∂μ
```

### `MeasureTheory.L2.convolutionCLM_isSymmetric_of_conj_neg`

`Thm_MeasureTheory_L2_convolutionCLM_isSymmetric_of_conj_neg` — Convolution by a Hermitian kernel is symmetric on L²(G)

```lean
theorem MeasureTheory.L2.convolutionCLM_isSymmetric_of_conj_neg
    (G : Type*) [MeasurableSpace G] [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [CompactSpace G] [T2Space G] [BorelSpace G]
    (μ : MeasureTheory.Measure G) [μ.IsAddHaarMeasure] [MeasureTheory.IsFiniteMeasure μ]
    (f : C(G, ℂ)) (hf : ∀ x, f (-x) = star (f x))
    (T : MeasureTheory.Lp ℂ 2 μ →L[ℂ] MeasureTheory.Lp ℂ 2 μ)
    (hT : ∀ φ : MeasureTheory.Lp ℂ 2 μ, (T φ : G → ℂ) =ᵐ[μ]
      ((f : G → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] (φ : G → ℂ))) :
    LinearMap.IsSymmetric (T : MeasureTheory.Lp ℂ 2 μ →ₗ[ℂ] MeasureTheory.Lp ℂ 2 μ)
```

### `MeasureTheory.L2.exists_convolutionCLM_isCompactOperator`

`Thm_MeasureTheory_L2_exists_convolutionCLM_isCompactOperator` — Convolution by a continuous function is compact on L²

```lean
theorem MeasureTheory.L2.exists_convolutionCLM_isCompactOperator
    (G : Type*) [MeasurableSpace G] [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [CompactSpace G] [T2Space G] [BorelSpace G]
    (μ : MeasureTheory.Measure G) [μ.IsAddHaarMeasure] [MeasureTheory.IsFiniteMeasure μ]
    (f : C(G, ℂ)) :
    ∃ T : MeasureTheory.Lp ℂ 2 μ →L[ℂ] MeasureTheory.Lp ℂ 2 μ,
      (∀ φ : MeasureTheory.Lp ℂ 2 μ, (T φ : G → ℂ) =ᵐ[μ]
        ((f : G → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] (φ : G → ℂ))) ∧
      IsCompactOperator T
```

### `MeasureTheory.L2.exists_convolutionCLM_isCompactOperator_of_compactSpace`

`Thm_MeasureTheory_L2_exists_convolutionCLM_isCompactOperator_of_compactSpace` — Convolution by a Hermitian continuous kernel is compact and symmetric

```lean
theorem MeasureTheory.L2.exists_convolutionCLM_isCompactOperator_of_compactSpace
    (G : Type*) [MeasurableSpace G] [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [CompactSpace G] [T2Space G] [BorelSpace G]
    (μ : MeasureTheory.Measure G) [μ.IsAddHaarMeasure] [MeasureTheory.IsFiniteMeasure μ]
    (f : C(G, ℂ)) (hf : ∀ x, f (-x) = star (f x)) :
    ∃ T : MeasureTheory.Lp ℂ 2 μ →L[ℂ] MeasureTheory.Lp ℂ 2 μ,
      (∀ φ : MeasureTheory.Lp ℂ 2 μ, (T φ : G → ℂ) =ᵐ[μ]
        ((f : G → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] (φ : G → ℂ))) ∧
      IsCompactOperator T ∧ LinearMap.IsSymmetric (T : MeasureTheory.Lp ℂ 2 μ →ₗ[ℂ] MeasureTheory.Lp ℂ 2 μ)
```

### `MeasureTheory.Lp.finiteDimensional_and_finrank_le_of_forall_ae_norm_le_mul_norm`

`Thm_MeasureTheory_Lp_finiteDimensional_and_finrank_le_of_forall_ae_norm_le_mul_norm` — Godement's finite-dimensionality lemma for subspaces of L²

```lean
theorem MeasureTheory.Lp.finiteDimensional_and_finrank_le_of_forall_ae_norm_le_mul_norm
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ] {𝕜 : Type*} [RCLike 𝕜]
    (V : Submodule 𝕜 (Lp 𝕜 2 μ)) (C : ℝ)
    (hV : ∀ φ ∈ V, ∀ᵐ x ∂μ, ‖(φ : X → 𝕜) x‖ ≤ C * ‖φ‖) :
    FiniteDimensional 𝕜 V ∧ (Module.finrank 𝕜 V : ℝ) ≤ C ^ 2 * (μ Set.univ).toReal
```

### `MeasureTheory.Measure.exists_eq_prod_of_forall_map_add_left`

`Thm_MeasureTheory_Measure_exists_eq_prod_of_forall_map_add_left` — Translation-invariant measures on G× Y are μ⊗σ

```lean
theorem MeasureTheory.Measure.exists_eq_prod_of_forall_map_add_left
    {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : MeasureTheory.Measure G) [μ.IsAddHaarMeasure]
    {Y : Type*} [MeasurableSpace Y] (ρ : MeasureTheory.Measure (G × Y))
    (hinv : ∀ a : G, ρ.map (fun p : G × Y => (a + p.1, p.2)) = ρ)
    (hfin : ∃ B : ℕ → Set Y, (∀ n, MeasurableSet (B n)) ∧ (⋃ n, B n) = Set.univ ∧
      ∀ n (K : Set G), IsCompact K → ρ (K ×ˢ B n) < ⊤) :
    ∃ σ : MeasureTheory.Measure Y, MeasureTheory.SigmaFinite σ ∧ ρ = μ.prod σ
```

### `MeasureTheory.Measure.exists_eq_smul_map_smul_of_forall_map_smul_eq_of_isCompact_stabilizer`

`Thm_MeasureTheory_Measure_exists_eq_smul_map_smul_of_forall_map_smul_eq_of_isCompact_stabilizer` — Uniqueness of invariant measures on homogeneous spaces with compact stabilisers

```lean
theorem MeasureTheory.Measure.exists_eq_smul_map_smul_of_forall_map_smul_eq_of_isCompact_stabilizer
    {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [LocallyCompactSpace L]
    [SecondCountableTopology L] [MeasurableSpace L] [BorelSpace L]
    (μL : Measure L) [μL.IsHaarMeasure]
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [MulAction L X] [ContinuousSMul L X] [MulAction.IsPretransitive L X]
    (x₀ : X) (hx₀ : IsCompact (MulAction.stabilizer L x₀ : Set L))
    (σ : Measure X) [IsFiniteMeasureOnCompacts σ]
    (hσ : ∀ g : L, σ.map (fun x : X => g • x) = σ) :
    ∃ c : ℝ≥0∞, c ≠ ∞ ∧ σ = c • μL.map (fun g : L => g • x₀)
```

### `MeasureTheory.Measure.exists_haar_eq_smul_map_mul_prod_of_homeomorph`

`Thm_MeasureTheory_Measure_exists_haar_eq_smul_map_mul_prod_of_homeomorph` — Haar measure of a bi-invariant group factorised as T· S

```lean
theorem MeasureTheory.Measure.exists_haar_eq_smul_map_mul_prod_of_homeomorph
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (T S : Subgroup G) [MeasurableSpace T] [BorelSpace T] [MeasurableSpace S] [BorelSpace S]
    (e : T × S ≃ₜ G) (he : ∀ p : T × S, e p = (p.1 : G) * (p.2 : G))
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (τ : Measure T) [τ.IsHaarMeasure]
    (ν : Measure S) [IsFiniteMeasureOnCompacts ν] [ν.IsMulRightInvariant] [ν.IsOpenPosMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ = c • Measure.map e (τ.prod ν)
```

### `MeasureTheory.Measure.exists_haar_forall_lintegral_mul_prod_mul_indicator_eq_mul_lintegral_mul_prod_lintegral_of_restrictedProduct`

`Thm_MeasureTheory_Measure_exists_haar_forall_lintegral_mul_prod_mul_indicator_eq_mul_lintegral_mul_prod_lintegral_of_restrictedProduct` — Haar factorisation for an abstract restricted product

```lean
theorem MeasureTheory.Measure.exists_haar_forall_lintegral_mul_prod_mul_indicator_eq_mul_lintegral_mul_prod_lintegral_of_restrictedProduct
    {B α κ : Type*} [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [LocallyCompactSpace B] [T2Space B]
    [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]
    [Fintype α] {A : α → Type*} [∀ a, Group (A a)] [∀ a, TopologicalSpace (A a)]
    [∀ a, IsTopologicalGroup (A a)] [∀ a, LocallyCompactSpace (A a)] [∀ a, T2Space (A a)]
    [∀ a, SecondCountableTopology (A a)] [∀ a, MeasurableSpace (A a)] [∀ a, BorelSpace (A a)]
    {G : κ → Type*} [∀ k, Group (G k)] [∀ k, TopologicalSpace (G k)] [∀ k, IsTopologicalGroup (G k)]
    [∀ k, LocallyCompactSpace (G k)] [∀ k, T2Space (G k)] [∀ k, SecondCountableTopology (G k)]
    [∀ k, MeasurableSpace (G k)] [∀ k, BorelSpace (G k)]
    (q : ∀ a, B →* A a) (hq : ∀ a, Continuous (q a)) (p : ∀ k, B →* G k) (hp : ∀ k, Continuous (p k))
    (U : ∀ k, Subgroup (G k)) (hUc : ∀ k, IsCompact (U k : Set (G k))) (hUo : ∀ k, IsOpen (U k : Set (G k)))
    (hP : ∀ Sf : Finset κ, IsOpen {b : B | ∀ k ∉ Sf, p k b ∈ U k})
    (hsurj : ∀ (Sf : Finset κ) (y : ∀ a, A a) (x : ∀ k, G k), (∀ k ∉ Sf, x k ∈ U k) →
      ∃ b : B, (∀ a, q a b = y a) ∧ ∀ k, p k b = x k)
    (hbox : ∀ (D : ∀ a, Set (A a)) (C : ∀ k, Set (G k)), (∀ a, IsCompact (D a)) → (∀ k, IsCompact (C k)) →
      {k | C k ≠ (U k : Set (G k))}.Finite → IsCompact {b : B | (∀ a, q a b ∈ D a) ∧ ∀ k, p k b ∈ C k})
    (ν : Measure B) [ν.IsHaarMeasure] :
    ∃ (νA : Measure (∀ a, A a)) (νG : ∀ k, Measure (G k)),
      νA.IsHaarMeasure ∧ (∀ k, (νG k).IsHaarMeasure ∧ νG k (U k : Set (G k)) = 1) ∧
      ∀ (Sf : Finset κ) (g : (∀ a, A a) → ℝ≥0∞) (f : ∀ k, G k → ℝ≥0∞),
        Measurable g → (∀ k ∈ Sf, Measurable (f k)) →
        ∫⁻ b, g (fun a => q a b) * (∏ k ∈ Sf, f k (p k b)) *
            Set.indicator {b : B | ∀ k, k ∉ Sf → p k b ∈ U k} (fun _ => (1 : ℝ≥0∞)) b ∂ν =
          (∫⁻ y, g y ∂νA) * ∏ k ∈ Sf, ∫⁻ x, f k x ∂(νG k)
```

### `MeasureTheory.Measure.exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv`

`Thm_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv` — Haar measure on GL₂(ℝ) is (det)⁻² dA up to scalar

```lean
theorem MeasureTheory.Measure.exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv
    [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)]
    (μ : Measure (GL (Fin 2) ℝ)) [μ.IsHaarMeasure] :
    ∃ c : NNReal, 0 < c ∧
      μ = c • Measure.map
        (fun A : Fin 2 → Fin 2 → ℝ =>
          if h : (Matrix.of A).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of A) h
          else 1)
        ((volume.restrict {A : Fin 2 → Fin 2 → ℝ | (Matrix.of A).det ≠ 0}).withDensity
          fun A => ENNReal.ofReal (((Matrix.of A).det ^ 2)⁻¹))
```

### `MeasureTheory.Measure.exists_isHaarMeasure_map_continuousMulEquiv_eq_prod`

`Thm_MeasureTheory_Measure_exists_isHaarMeasure_map_continuousMulEquiv_eq_prod` — Splitting a Haar measure along an isomorphism onto a product

```lean
theorem MeasureTheory.Measure.exists_isHaarMeasure_map_continuousMulEquiv_eq_prod
    {G : Type u₁} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    {G₁ : Type u₂} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
      [SigmaCompactSpace G₁] [MeasurableSpace G₁] [BorelSpace G₁]
    {G₂ : Type u₃} [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [SigmaCompactSpace G₂]
      [MeasurableSpace G₂] [BorelSpace G₂]
    (μ : Measure G) [μ.IsHaarMeasure] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (e : G ≃ₜ* G₁ × G₂) :
    ∃ μ₂ : Measure G₂, μ₂.IsHaarMeasure ∧ (μ.IsMulRightInvariant → μ₂.IsMulRightInvariant) ∧
      μ.map e = μ₁.prod μ₂
```

### `MeasureTheory.Measure.exists_isHaarMeasure_subgroup_units_map_val_eq_withDensity_of_abs_det_eq`

`Thm_MeasureTheory_Measure_exists_isHaarMeasure_subgroup_units_map_val_eq_withDensity_of_abs_det_eq` — Haar measure |χ|⁻¹ dx on units of a real subalgebra

```lean
theorem MeasureTheory.Measure.exists_isHaarMeasure_subgroup_units_map_val_eq_withDensity_of_abs_det_eq
    {M : Type*} [Ring M] [Algebra ℝ M] [FiniteDimensional ℝ M]
    [TopologicalSpace M] [IsTopologicalRing M] [ContinuousSMul ℝ M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    (A : Subalgebra ℝ M) (Γ : Subgroup Mˣ) (hΓ : ∀ g : Mˣ, g ∈ Γ ↔ (g : M) ∈ A)
    (n : ℕ) (e : Fin n → M) (hli : LinearIndependent ℝ e)
    (hsp : Submodule.span ℝ (Set.range e) = Subalgebra.toSubmodule A)
    (χ : M →* ℝ) (hχ : Continuous χ)
    (hleft : ∀ g : Mˣ, g ∈ Γ → ∃ P : Matrix (Fin n) (Fin n) ℝ,
      (∀ j, (g : M) * e j = ∑ i, P i j • e i) ∧ |P.det| = |χ g|)
    (hright : ∀ g : Mˣ, g ∈ Γ → ∃ Q : Matrix (Fin n) (Fin n) ℝ,
      (∀ j, e j * (g : M) = ∑ i, Q i j • e i) ∧ |Q.det| = |χ g|) :
    letI : MeasurableSpace Γ := borel Γ
    ∃ τ : Measure Γ, τ.IsHaarMeasure ∧ τ.IsMulRightInvariant ∧
      Measure.map (fun t : Γ => ((t : Mˣ) : M)) τ =
        (Measure.map (fun c : Fin n → ℝ => ∑ i, c i • e i) volume).withDensity
          fun x => (ENNReal.ofReal |χ x|)⁻¹
```

### `MeasureTheory.Measure.exists_map_apply_out_haarQuotient_eq_smul_restrict_range_of_isOpen_range`

`Thm_MeasureTheory_Measure_exists_map_apply_out_haarQuotient_eq_smul_restrict_range_of_isOpen_range` — Weil's formula: pushforward of quotient Haar measure along open-range f

```lean
theorem MeasureTheory.Measure.exists_map_apply_out_haarQuotient_eq_smul_restrict_range_of_isOpen_range
    {G H : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
    [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure]
    (f : G →* H) (hf : Continuous f) (hopen : IsOpen (Set.range f))
    (N : Subgroup G) (hN : ∀ x : G, x ∈ N ↔ f x = 1)
    (μN : Measure N) [μN.IsHaarMeasure] :
    ∃ κ : ℝ, 0 < κ ∧
      Measure.map (fun q : MulAction.orbitRel.Quotient N G => f q.out) (HaarQuotient.measure μ N μN) =
        ENNReal.ofReal κ • ν.restrict (Set.range f)
```

### `MeasureTheory.Measure.exists_map_restrict_eq_smul_restrict_range_of_isFundamentalDomain`

`Thm_MeasureTheory_Measure_exists_map_restrict_eq_smul_restrict_range_of_isFundamentalDomain` — Pushforward of Haar measure on a fundamental domain

```lean
theorem MeasureTheory.Measure.exists_map_restrict_eq_smul_restrict_range_of_isFundamentalDomain
    {G H : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
    [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure]
    (f : G →* H) (hf : Continuous f) (hopen : IsOpen (Set.range f))
    (Γ : Subgroup G) [Countable Γ] (hΓ : Γ ≤ f.ker)
    (hker : ∃ D : Set G, IsCompact D ∧ (f.ker : Set G) ⊆ (Γ : Set G) * D)
    (Θ : Set G) (hΘ : IsFundamentalDomain Γ Θ μ) :
    ∃ κ : ℝ, 0 < κ ∧
      Measure.map f (μ.restrict Θ) = ENNReal.ofReal κ • ν.restrict (Set.range f)
```

### `MeasureTheory.Measure.exists_ne_zero_map_mulEquiv_eq_smul_pi`

`Thm_MeasureTheory_Measure_exists_ne_zero_map_mulEquiv_eq_smul_pi` — Haar pushforward along an isomorphism onto a finite product

```lean
theorem MeasureTheory.Measure.exists_ne_zero_map_mulEquiv_eq_smul_pi
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    {ι : Type*} [Fintype ι] {H : ι → Type*} [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
    [∀ i, IsTopologicalGroup (H i)] [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)]
    [∀ i, LocallyCompactSpace (H i)] [∀ i, SecondCountableTopology (H i)]
    (μ : Measure G) [μ.IsHaarMeasure] (ν : ∀ i, Measure (H i)) [∀ i, (ν i).IsHaarMeasure]
    (Θ : G ≃* (∀ i, H i)) (hΘ : Continuous Θ) (hΘs : Continuous Θ.symm) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ Measure.map Θ μ = c • Measure.pi ν
```

### `MeasureTheory.Measure.gram_smul_map_volume_eq_of_span_eq`

`Thm_MeasureTheory_Measure_gram_smul_map_volume_eq_of_span_eq` — Basis independence of the Gram-normalised Lebesgue measure

```lean
theorem MeasureTheory.Measure.gram_smul_map_volume_eq_of_span_eq
    {V : Type} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (B : LinearMap.BilinForm ℝ V) {n n' : ℕ} (e : Fin n → V) (e' : Fin n' → V)
    (he : LinearIndependent ℝ e) (he' : LinearIndependent ℝ e')
    (hspan : Submodule.span ℝ (Set.range e') = Submodule.span ℝ (Set.range e)) :
    (ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n' => B (e' i) (e' j)).det|)) •
        Measure.map (fun c : Fin n' → ℝ => ∑ i, c i • e' i) volume =
      (ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n => B (e i) (e j)).det|)) •
        Measure.map (fun c : Fin n → ℝ => ∑ i, c i • e i) volume
```

### `MeasureTheory.Measure.gram_trace_matrix_smul_map_volume_eq_pow_smul_map_of_pi_pi`

`Thm_MeasureTheory_Measure_gram_trace_matrix_smul_map_volume_eq_pow_smul_map_of_pi_pi` — Gram measure of the trace form on matrix algebras

```lean
theorem MeasureTheory.Measure.gram_trace_matrix_smul_map_volume_eq_pow_smul_map_of_pi_pi
    (R : Type) [NormedCommRing R] [NormedAlgebra ℝ R] [MeasurableSpace R] [BorelSpace R]
    (ι : Type) [Fintype ι] [MeasurableSpace (Matrix ι ι R)] [BorelSpace (Matrix ι ι R)]
    (m : ℕ) (b : Fin m → R) (hb : LinearIndependent ℝ b) (hbsp : Submodule.span ℝ (Set.range b) = ⊤)
    (μ : Measure R) [SigmaFinite μ] (κ : ENNReal) (hκ : κ ≠ ⊤)
    (hμ : (ENNReal.ofReal (Real.sqrt |(Matrix.of fun a a' : Fin m =>
          Algebra.trace ℝ R (b a * b a')).det|)) •
        Measure.map (fun c : Fin m → ℝ => ∑ a, c a • b a) volume = κ • μ)
    (n : ℕ) (e : Fin n → Matrix ι ι R) (he : LinearIndependent ℝ e)
    (hesp : Submodule.span ℝ (Set.range e) = ⊤) :
    (ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n =>
          Algebra.trace ℝ R (Matrix.trace (e i * e j))).det|)) •
        Measure.map (fun c : Fin n → ℝ => ∑ i, c i • e i) volume =
      κ ^ (Fintype.card ι * Fintype.card ι) •
        Measure.map (Matrix.of : (ι → ι → R) → Matrix ι ι R)
          (Measure.pi fun _ : ι => Measure.pi fun _ : ι => μ)
```

### `MeasureTheory.Measure.isInvInvariant_of_isMulRightInvariant`

`Thm_MeasureTheory_Measure_isInvInvariant_of_isMulRightInvariant` — Unimodular Haar measure is inversion invariant

```lean
theorem MeasureTheory.Measure.isInvInvariant_of_isMulRightInvariant
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : μ.IsInvInvariant
```

### `MeasureTheory.Measure.isMulRightInvariant_of_forall_exists_eq_mul_of_isCompact`

`Thm_MeasureTheory_Measure_isMulRightInvariant_of_forall_exists_eq_mul_of_isCompact` — Unimodularity of groups compact modulo central elements

```lean
theorem MeasureTheory.Measure.isMulRightInvariant_of_forall_exists_eq_mul_of_isCompact
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] [T2Space G]
    (Z C : Set G) (hZ : ∀ z ∈ Z, ∀ g : G, g * z = z * g)
    (hC : IsCompact C) (hcov : ∀ g : G, ∃ z ∈ Z, ∃ k ∈ C, g = z * k)
    (μ : Measure G) [μ.IsHaarMeasure] : μ.IsMulRightInvariant
```

### `MeasureTheory.Measure.map_eq_self_of_involutive_of_isHaarMeasure`

`Thm_MeasureTheory_Measure_map_eq_self_of_involutive_of_isHaarMeasure` — Continuous involutive automorphisms preserve Haar measure

```lean
theorem MeasureTheory.Measure.map_eq_self_of_involutive_of_isHaarMeasure
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (θ : G ≃* G) (hθ : Continuous θ) (hθinv : ∀ g : G, θ (θ g) = g) :
    Measure.map θ μ = μ
```

### `MeasureTheory.Measure.map_withDensity_gramMeasure_eq_of_linearEquiv_of_bilinForm_eq`

`Thm_MeasureTheory_Measure_map_withDensity_gramMeasure_eq_of_linearEquiv_of_bilinForm_eq` — Gram-normalised measure transported by a form-preserving automorphism

```lean
theorem MeasureTheory.Measure.map_withDensity_gramMeasure_eq_of_linearEquiv_of_bilinForm_eq
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    [MeasurableSpace V] [BorelSpace V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Φ : V ≃ₗ[ℝ] V) (hΦ : ∀ x y : V, B (Φ x) (Φ y) = B x y)
    {n₁ n₂ : ℕ} (e₁ : Fin n₁ → V) (e₂ : Fin n₂ → V)
    (h₁ : LinearIndependent ℝ e₁) (h₂ : LinearIndependent ℝ e₂)
    (hspan : (Submodule.span ℝ (Set.range e₂)).map (Φ : V →ₗ[ℝ] V) = Submodule.span ℝ (Set.range e₁))
    (ρ : V → ENNReal) (hρm : Measurable ρ) (hρ : ∀ x : V, ρ (Φ x) = ρ x) :
    Measure.map Φ
        (((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ => B (e₂ i) (e₂ j)).det|)) •
            Measure.map (fun a : Fin n₂ → ℝ => ∑ i, a i • e₂ i) volume).withDensity ρ) =
      ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ => B (e₁ i) (e₁ j)).det|)) •
          Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e₁ i) volume).withDensity ρ
```

### `MeasureTheory.Measure.map_withDensity_gram_trace_matrix_pi_eq_pi_of_span_eq`

`Thm_MeasureTheory_Measure_map_withDensity_gram_trace_matrix_pi_eq_pi_of_span_eq` — Gram-normalised trace measures on M₂ of a product algebra

```lean
theorem MeasureTheory.Measure.map_withDensity_gram_trace_matrix_pi_eq_pi_of_span_eq
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (E : ι → Type) [∀ i, CommRing (E i)] [∀ i, Algebra ℝ (E i)] [∀ i, Module.Free ℝ (E i)]
    [∀ i, Module.Finite ℝ (E i)] [∀ i, TopologicalSpace (E i)] [∀ i, IsTopologicalRing (E i)]
    [∀ i, ContinuousSMul ℝ (E i)] [∀ i, T2Space (E i)]
    [∀ i, MeasurableSpace (Matrix (Fin 2) (Fin 2) (E i))] [∀ i, BorelSpace (Matrix (Fin 2) (Fin 2) (E i))]
    [MeasurableSpace (Matrix (Fin 2) (Fin 2) ((i : ι) → E i))] [BorelSpace (Matrix (Fin 2) (Fin 2) ((i : ι) → E i))]
    (W : ∀ i, Submodule ℝ (Matrix (Fin 2) (Fin 2) (E i)))
    (n : ι → ℕ) (e : ∀ i, Fin (n i) → Matrix (Fin 2) (Fin 2) (E i))
    (he : ∀ i, LinearIndependent ℝ (e i) ∧ Submodule.span ℝ (Set.range (e i)) = W i)
    (hW : ∀ i, ∃ X ∈ W i, Algebra.norm ℝ (Matrix.det X) ≠ 0)
    (W' : Submodule ℝ (Matrix (Fin 2) (Fin 2) ((i : ι) → E i)))
    (hW' : ∀ X : Matrix (Fin 2) (Fin 2) ((i : ι) → E i), X ∈ W' ↔ ∀ i, X.map (Pi.evalRingHom E i) ∈ W i)
    (N : ℕ) (f : Fin N → Matrix (Fin 2) (Fin 2) ((i : ι) → E i))
    (hf : LinearIndependent ℝ f ∧ Submodule.span ℝ (Set.range f) = W') :
    Measure.map (fun X : Matrix (Fin 2) (Fin 2) ((i : ι) → E i) => fun i : ι => X.map (Pi.evalRingHom E i))
        (((ENNReal.ofReal (Real.sqrt |(Matrix.of fun a b : Fin N =>
              Algebra.trace ℝ ((i : ι) → E i) (Matrix.trace (f a * f b))).det|)) •
            Measure.map (fun c : Fin N → ℝ => ∑ a, c a • f a) volume).withDensity
          fun X : Matrix (Fin 2) (Fin 2) ((i : ι) → E i) => (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) =
      Measure.pi (fun i : ι =>
        ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun a b : Fin (n i) =>
              Algebra.trace ℝ (E i) (Matrix.trace (e i a * e i b))).det|)) •
            Measure.map (fun c : Fin (n i) → ℝ => ∑ a, c a • e i a) volume).withDensity
          fun X : Matrix (Fin 2) (Fin 2) (E i) => (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹)
```

### `MeasureTheory.Measure.measure_coe_eq_relIndex_mul_of_le_of_isAddLeftInvariant`

`Thm_MeasureTheory_Measure_measure_coe_eq_relIndex_mul_of_le_of_isAddLeftInvariant` — Relative index scaling for a left-invariant measure

```lean
theorem MeasureTheory.Measure.measure_coe_eq_relIndex_mul_of_le_of_isAddLeftInvariant
    {G : Type*} [AddGroup G] [MeasurableSpace G] [MeasurableAdd G] (μ : Measure G) [μ.IsAddLeftInvariant]
    (H H' : AddSubgroup G) (hle : H ≤ H') (hH : MeasurableSet (H : Set G)) (hfin : H.relIndex H' ≠ 0) :
    μ (H' : Set G) = (H.relIndex H' : ENNReal) * μ (H : Set G)
```

### `MeasureTheory.Measure.measure_coe_eq_relIndex_mul_of_le_of_isMulLeftInvariant`

`Thm_MeasureTheory_Measure_measure_coe_eq_relIndex_mul_of_le_of_isMulLeftInvariant` — Measure of a subgroup as relative index times measure

```lean
theorem MeasureTheory.Measure.measure_coe_eq_relIndex_mul_of_le_of_isMulLeftInvariant
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant]
    (H H' : Subgroup G) (hle : H ≤ H') (hH : MeasurableSet (H : Set G)) (hfin : H.relIndex H' ≠ 0) :
    μ (H' : Set G) = (H.relIndex H' : ENNReal) * μ (H : Set G)
```

### `MeasureTheory.Measure.sqrt_abs_det_gram_smul_map_volume_image_pi_Ico_eq_of_span_eq`

`Thm_MeasureTheory_Measure_sqrt_abs_det_gram_smul_map_volume_image_pi_Ico_eq_of_span_eq` — Gram-normalised Lebesgue measure of a parallelepiped

```lean
theorem MeasureTheory.Measure.sqrt_abs_det_gram_smul_map_volume_image_pi_Ico_eq_of_span_eq
    {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    [MeasurableSpace V] [BorelSpace V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {n₁ n₂ : ℕ} (e : Fin n₁ → V) (f : Fin n₂ → V)
    (he : LinearIndependent ℝ e) (hf : LinearIndependent ℝ f)
    (hspan : Submodule.span ℝ (Set.range e) = Submodule.span ℝ (Set.range f)) :
    ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ => B (e i) (e j)).det|)) •
        Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e i) volume)
      ((fun a : Fin n₂ → ℝ => ∑ i, a i • f i) '' Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1)) =
    ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ => B (f i) (f j)).det|)
```

### `MeasureTheory.addEquivAddHaarChar_eq_one_and_measurePreserving_of_isAddFundamentalDomain_of_forall_apply_mem_iff`

`Thm_MeasureTheory_addEquivAddHaarChar_eq_one_and_measurePreserving_of_isAddFundamentalDomain_of_forall_apply_mem_iff` — Automorphism stabilising a lattice has Haar character one

```lean
theorem MeasureTheory.addEquivAddHaarChar_eq_one_and_measurePreserving_of_isAddFundamentalDomain_of_forall_apply_mem_iff
    {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : MeasureTheory.Measure G) [μ.IsAddHaarMeasure] [μ.Regular]
    (Γ : AddSubgroup G) [Countable Γ] (F : Set G) (hF : MeasureTheory.IsAddFundamentalDomain Γ F μ)
    (hFtop : μ F ≠ ⊤) (φ : G ≃ₜ+ G) (hφ : ∀ x : G, φ x ∈ Γ ↔ x ∈ Γ) :
    MeasureTheory.addEquivAddHaarChar φ = 1 ∧ MeasureTheory.MeasurePreserving φ μ μ
```

### `MeasureTheory.ae_prod_eq_zero_of_forall_setIntegral_prod_eq_zero_of_iUnion`

`Thm_MeasureTheory_ae_prod_eq_zero_of_forall_setIntegral_prod_eq_zero_of_iUnion` — Kernels vanishing on rectangles in an exhaustion vanish a.e.

```lean
theorem MeasureTheory.ae_prod_eq_zero_of_forall_setIntegral_prod_eq_zero_of_iUnion
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    (k : X × X → ℂ)
    (S : ℕ → Set X) (hS : ∀ n, MeasurableSet (S n)) (hmono : Monotone S)
    (hcov : ∀ᵐ x ∂μ, x ∈ ⋃ n, S n)
    (hint : ∀ n, IntegrableOn k (S n ×ˢ S n) (μ.prod μ))
    (hzero : ∀ n, ∀ A ⊆ S n, MeasurableSet A → ∀ B ⊆ S n, MeasurableSet B →
      ∫ p in A ×ˢ B, k p ∂(μ.prod μ) = 0) :
    k =ᵐ[μ.prod μ] 0
```

### `MeasureTheory.aestronglyMeasurable_of_aestronglyMeasurable_sum_smul_monoidHom`

`Thm_MeasureTheory_aestronglyMeasurable_of_aestronglyMeasurable_sum_smul_monoidHom` — Measurability of characters in a measurable linear combination

```lean
theorem MeasureTheory.aestronglyMeasurable_of_aestronglyMeasurable_sum_smul_monoidHom
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] [T2Space G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    {n : ℕ} (ψ : Fin n → (G →* ℂ)) (hψ : Function.Injective ψ) (c : Fin n → ℂ) (hc : ∀ i, c i ≠ 0)
    (h : AEStronglyMeasurable (fun g => ∑ i, c i * ψ i g) μ) (i : Fin n) :
    AEStronglyMeasurable (⇑(ψ i)) μ
```

### `MeasureTheory.analyticOnNhd_integral_and_im_eq_zero_and_re_pos_of_locally_norm_le_of_re_pos_at`

`Thm_MeasureTheory_analyticOnNhd_integral_and_im_eq_zero_and_re_pos_of_locally_norm_le_of_re_pos_at` — Holomorphy and real positivity of dominated parameter integrals

```lean
theorem MeasureTheory.analyticOnNhd_integral_and_im_eq_zero_and_re_pos_of_locally_norm_le_of_re_pos_at
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] (μ : Measure Y)
    (a : ℝ) (F : ℂ → Y → ℂ)
    (hmeas : ∀ s : ℂ, AEStronglyMeasurable (F s) μ)
    (hhol : ∀ y : Y, Differentiable ℂ (fun s => F s y))
    (hdom : ∀ s₀ : ℂ, a < s₀.re → ∃ ε : ℝ, 0 < ε ∧ ∃ M : Y → ℝ, Integrable M μ ∧
      ∀ s ∈ Metric.ball s₀ ε, ∀ y : Y, ‖F s y‖ ≤ M y)
    (hreal : ∀ σ : ℝ, a < σ → ∀ y : Y, (F σ y).im = 0 ∧ 0 ≤ (F σ y).re)
    (hcont : ∀ σ : ℝ, a < σ → Continuous (F σ))
    (y₀ : Y) (hpt : ∀ σ : ℝ, a < σ → 0 < (F σ y₀).re)
    (hopen : ∀ U : Set Y, IsOpen U → y₀ ∈ U → 0 < μ U) :
    (∀ s : ℂ, a < s.re → Integrable (F s) μ) ∧
      AnalyticOnNhd ℂ (fun s : ℂ => ∫ y, F s y ∂μ) {s : ℂ | a < s.re} ∧
      (∀ σ : ℝ, a < σ → (∫ y, F σ y ∂μ).im = 0 ∧ 0 < (∫ y, F σ y ∂μ).re)
```

### `MeasureTheory.analyticOnNhd_integral_mul_abs_cpow_sub_two_of_forall_integrable`

`Thm_MeasureTheory_analyticOnNhd_integral_mul_abs_cpow_sub_two_of_forall_integrable` — Analyticity and positivity of a two-sided Mellin transform

```lean
theorem MeasureTheory.analyticOnNhd_integral_mul_abs_cpow_sub_two_of_forall_integrable
    (P : ℝ → ℝ) (x₀ : ℝ) (hP : Measurable P) (hP0 : ∀ y : ℝ, 0 ≤ P y)
    (hPint : ∀ σ : ℝ, x₀ < σ → Integrable (fun y : ℝ => P y * |y| ^ (σ - 2))) :
    AnalyticOnNhd ℂ (fun s : ℂ => ∫ y : ℝ, ((P y : ℝ) : ℂ) * ((|y| : ℝ) : ℂ) ^ (s - 2)) {s : ℂ | x₀ < s.re} ∧
    (∀ σ : ℝ, x₀ < σ →
      (∫ y : ℝ, ((P y : ℝ) : ℂ) * ((|y| : ℝ) : ℂ) ^ ((σ : ℂ) - 2)).im = 0 ∧
      0 ≤ (∫ y : ℝ, ((P y : ℝ) : ℂ) * ((|y| : ℝ) : ℂ) ^ ((σ : ℂ) - 2)).re) ∧
    ((¬ ∀ᵐ y : ℝ, P y = 0) → ∀ σ : ℝ, x₀ < σ →
      0 < (∫ y : ℝ, ((P y : ℝ) : ℂ) * ((|y| : ℝ) : ℂ) ^ ((σ : ℂ) - 2)).re)
```

### `MeasureTheory.contDiffOn_integral_mul_log_sq_add_sq_halfSpace`

`Thm_MeasureTheory_contDiffOn_integral_mul_log_sq_add_sq_halfSpace` — Smoothness of the logarithmic potential on a closed half-space

```lean
theorem MeasureTheory.contDiffOn_integral_mul_log_sq_add_sq_halfSpace
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (g : E × ℝ → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : E × ℝ => ∫ s : ℝ, g (p.1, s) * (Real.log (s ^ 2 + p.2 ^ 2) : ℂ))
      {p : E × ℝ | 0 ≤ p.2}
```

### `MeasureTheory.contDiff_and_hasCompactSupport_integral_mul_comp_of_contDiff_of_hasCompactSupport`

`Thm_MeasureTheory_contDiff_and_hasCompactSupport_integral_mul_comp_of_contDiff_of_hasCompactSupport` — Smoothness and compact support of a parametric integral

```lean
theorem MeasureTheory.contDiff_and_hasCompactSupport_integral_mul_comp_of_contDiff_of_hasCompactSupport
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {β : Type} [NormedAddCommGroup β] [NormedSpace ℝ β] [FiniteDimensional ℝ β]
    [MeasurableSpace β] [BorelSpace β]
    {α : Type} [MeasurableSpace α] (μ : Measure α)
    (G : E × β → ℂ) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G)
    (π : α → β) (hπ : Measurable π)
    (h : α → ℂ) (hh : AEStronglyMeasurable h μ)
    (A : Set α) (hA : MeasurableSet A) (hμA : μ A < ⊤)
    (C : ℝ) (hhA : ∀ a ∈ A, ‖h a‖ ≤ C) (hh0 : ∀ a, a ∉ A → h a = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : E => ∫ a, h a * G (x, π a) ∂μ) ∧
    HasCompactSupport (fun x : E => ∫ a, h a * G (x, π a) ∂μ) ∧
    ∀ x : E, x ∉ Prod.fst '' tsupport G → (∫ a, h a * G (x, π a) ∂μ) = 0
```

### `MeasureTheory.contDiff_comp_abs_of_contDiffOn_halfSpace_of_iteratedFDerivWithin_eq_zero`

`Thm_MeasureTheory_contDiff_comp_abs_of_contDiffOn_halfSpace_of_iteratedFDerivWithin_eq_zero` — Even reflection of a function flat on a half-space boundary

```lean
theorem MeasureTheory.contDiff_comp_abs_of_contDiffOn_halfSpace_of_iteratedFDerivWithin_eq_zero
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (D : E × ℝ → F) (hD : ContDiffOn ℝ (⊤ : ℕ∞) D {p : E × ℝ | 0 ≤ p.2})
    (hflat : ∀ (n : ℕ) (e : E), iteratedFDerivWithin ℝ n D {p : E × ℝ | 0 ≤ p.2} (e, 0) = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : E × ℝ => D (p.1, |p.2|))
```

### `MeasureTheory.contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport`

`Thm_MeasureTheory_contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport` — Smoothness of a parametric integral of a smooth compactly supported kernel

```lean
theorem MeasureTheory.contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [SecondCountableTopology X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    {M P E : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (c : X → M) (hc : Continuous c) (w : X → ℝ) (hw : Continuous w) (hwc : HasCompactSupport w)
    (Ψ : M × P → E) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨc : HasCompactSupport Ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : P => ∫ x, w x • Ψ (c x, p) ∂μ)
```

### `MeasureTheory.differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le`

`Thm_MeasureTheory_differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le` — Holomorphy of a locally dominated parametric integral

```lean
theorem MeasureTheory.differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    {U : Set ℂ} (hU : IsOpen U) (F : ℂ → Y → ℂ)
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (F z) ν)
    (hhol : ∀ a : Y, DifferentiableOn ℂ (fun z => F z a) U)
    (hdom : ∀ z₀ ∈ U, ∃ ε : ℝ, 0 < ε ∧ ∃ M : Y → ℝ, Integrable M ν ∧
      ∀ z ∈ Metric.ball z₀ ε, ∀ a : Y, ‖F z a‖ ≤ M a) :
    DifferentiableOn ℂ (fun z => ∫ a, F z a ∂ν) U
```

### `MeasureTheory.differentiable_and_continuous_integral_mul_cpow_of_eventually_norm_mul_rpow_add_rpow_neg_le`

`Thm_MeasureTheory_differentiable_and_continuous_integral_mul_cpow_of_eventually_norm_mul_rpow_add_rpow_neg_le` — Entirety, joint continuity and strip bounds for N^s-integrals

```lean
theorem MeasureTheory.differentiable_and_continuous_integral_mul_cpow_of_eventually_norm_mul_rpow_add_rpow_neg_le
    {X : Type*} [MeasurableSpace X] (m : MeasureTheory.Measure X)
    {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    (N : X → ℝ) (hN : AEMeasurable N m) (hNpos : ∀ x, 0 < N x)
    (h : P → X → ℂ) (hh : ∀ p, MeasureTheory.AEStronglyMeasurable (h p) m)
    (hcont : ∀ᵐ x ∂m, Continuous fun p => h p x)
    (hdom : ∀ (p₀ : P) (M : ℝ), ∃ bound : X → ℝ, MeasureTheory.Integrable bound m ∧
      ∀ᶠ p in nhds p₀, ∀ᵐ x ∂m, ‖h p x‖ * (N x ^ M + N x ^ (-M)) ≤ bound x) :
    (∀ p : P, Differentiable ℂ fun s : ℂ => ∫ x, h p x * ((N x : ℝ) : ℂ) ^ s ∂m) ∧
    (Continuous fun q : ℂ × P => ∫ x, h q.2 x * ((N x : ℝ) : ℂ) ^ q.1 ∂m) ∧
    (∀ (p : P) (M : ℝ) (s : ℂ), |s.re| ≤ M →
      MeasureTheory.Integrable (fun x => ‖h p x‖ * (N x ^ M + N x ^ (-M))) m ∧
      ‖∫ x, h p x * ((N x : ℝ) : ℂ) ^ s ∂m‖ ≤ ∫ x, ‖h p x‖ * (N x ^ M + N x ^ (-M)) ∂m)
```

### `MeasureTheory.exists_clm_opNorm_le_noAtomicMass_apply_eq_tsum_integral_mul_fourier_of_summable_of_ae_measure_fibre_eq_zero`

`Thm_MeasureTheory_exists_clm_opNorm_le_noAtomicMass_apply_eq_tsum_integral_mul_fourier_of_summable_of_ae_measure_fibre_eq_zero` — A winding functional on Tᵈ: norm, no atoms, Fourier values

```lean
theorem MeasureTheory.exists_clm_opNorm_le_noAtomicMass_apply_eq_tsum_integral_mul_fourier_of_summable_of_ae_measure_fibre_eq_zero
    (a d : ℕ) (Y : Type) [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (vol : Measure Y) (m : Measure (Fin d → AddCircle (1 : ℝ))) [IsProbabilityMeasure m]
    (n₀ : Fin d → ℤ) (P : (Fin a → ℤ) → Y → (Fin d → AddCircle (1 : ℝ))) (hP : ∀ κ, Continuous (P κ))
    (c : (Fin a → ℤ) → Y → ℂ) (hcc : ∀ κ, Continuous (c κ)) (hci : ∀ κ, Integrable (c κ) vol)
    (hcs : Summable fun κ => ∫ y, ‖c κ y‖ ∂vol)
    (hfib : ∀ (τ : Fin d → AddCircle (1 : ℝ)) (κ : Fin a → ℤ),
      ∀ᵐ y ∂vol, m {q : Fin d → AddCircle (1 : ℝ) | P κ y + q = τ} = 0) :
    ∃ μ : C((Fin d → AddCircle (1 : ℝ)), ℂ) →L[ℂ] ℂ,
      ‖μ‖ ≤ ∑' κ, ∫ y, ‖c κ y‖ ∂vol ∧
      (∀ (τ : Fin d → AddCircle (1 : ℝ)), ∀ ε > (0 : ℝ),
        ∃ U : Fin d → Set (AddCircle (1 : ℝ)), (∀ i, IsOpen (U i) ∧ τ i ∈ U i) ∧
          ∀ g : C((Fin d → AddCircle (1 : ℝ)), ℂ),
            (∀ θ, (∃ i, θ i ∉ U i) → g θ = 0) → (∀ θ, ‖g θ‖ ≤ 1) → ‖μ g‖ < ε) ∧
      ∀ (n : Fin d → ℤ) (e : C((Fin d → AddCircle (1 : ℝ)), ℂ)),
        (∀ θ, e θ = ∏ i, fourier (n i) (θ i)) →
        μ e = ∑' κ, ∫ y, c κ y * ((∏ i, fourier (n i - n₀ i) (P κ y i)) *
          ∫ q, ∏ i, fourier (n i - n₀ i) (q i) ∂m) ∂vol
```

### `MeasureTheory.exists_clm_torus_noAtomicMass_forall_apply_fourier_eq_prod_erase_ite_mul_one_add_neg_one_pow`

`Thm_MeasureTheory_exists_clm_torus_noAtomicMass_forall_apply_fourier_eq_prod_erase_ite_mul_one_add_neg_one_pow` — Atom-free functional on Tᵈ with prescribed Fourier values

```lean
theorem MeasureTheory.exists_clm_torus_noAtomicMass_forall_apply_fourier_eq_prod_erase_ite_mul_one_add_neg_one_pow
    (d : ℕ) (hd : 2 ≤ d) (p : Fin d) (q : ℕ) :
    ∃ μ : C((Fin d → AddCircle (1 : ℝ)), ℂ) →L[ℂ] ℂ,
      (∀ (τ : Fin d → AddCircle (1 : ℝ)), ∀ ε > (0 : ℝ),
        ∃ U : Fin d → Set (AddCircle (1 : ℝ)), (∀ i, IsOpen (U i) ∧ τ i ∈ U i) ∧
          ∀ g : C((Fin d → AddCircle (1 : ℝ)), ℂ),
            (∀ θ, (∃ i, θ i ∉ U i) → g θ = 0) → (∀ θ, ‖g θ‖ ≤ 1) → ‖μ g‖ < ε) ∧
      ∀ (n : Fin d → ℤ) (e : C((Fin d → AddCircle (1 : ℝ)), ℂ)),
        (∀ θ, e θ = ∏ i, fourier (n i) (θ i)) →
          μ e = (∏ i ∈ Finset.univ.erase p, (if n i = 0 then (1 : ℂ) else 0)) *
            (1 + (-1 : ℂ) ^ (q * (n p).natAbs))
```

### `MeasureTheory.exists_clm_torus_noAtomicMass_forall_apply_fourier_eq_prod_ite_eq_zero`

`Thm_MeasureTheory_exists_clm_torus_noAtomicMass_forall_apply_fourier_eq_prod_ite_eq_zero` — Haar functional on Tᵈ: box-small, Fourier values δ_{n,0}

```lean
theorem MeasureTheory.exists_clm_torus_noAtomicMass_forall_apply_fourier_eq_prod_ite_eq_zero
    (d : ℕ) (hd : 1 ≤ d) :
    ∃ μ : C((Fin d → AddCircle (1 : ℝ)), ℂ) →L[ℂ] ℂ,
      (∀ (τ : Fin d → AddCircle (1 : ℝ)), ∀ ε > (0 : ℝ),
        ∃ U : Fin d → Set (AddCircle (1 : ℝ)), (∀ i, IsOpen (U i) ∧ τ i ∈ U i) ∧
          ∀ g : C((Fin d → AddCircle (1 : ℝ)), ℂ),
            (∀ θ, (∃ i, θ i ∉ U i) → g θ = 0) → (∀ θ, ‖g θ‖ ≤ 1) → ‖μ g‖ < ε) ∧
      ∀ (n : Fin d → ℤ) (e : C((Fin d → AddCircle (1 : ℝ)), ℂ)),
        (∀ θ, e θ = ∏ i, fourier (n i) (θ i)) → μ e = ∏ i : Fin d, (if n i = 0 then (1 : ℂ) else 0)
```

### `MeasureTheory.exists_contDiff_forall_iteratedFDerivWithin_sub_sum_pow_smul_halfSpace_eq_zero`

`Thm_MeasureTheory_exists_contDiff_forall_iteratedFDerivWithin_sub_sum_pow_smul_halfSpace_eq_zero` — Taylor osculation along the boundary of a half-space

```lean
theorem MeasureTheory.exists_contDiff_forall_iteratedFDerivWithin_sub_sum_pow_smul_halfSpace_eq_zero
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (Ψ : E × ℝ → F) (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ {p : E × ℝ | 0 ≤ p.2})
    (C : Set E) (hC : IsCompact C) (hsupp : ∀ p : E × ℝ, p.1 ∉ C → Ψ p = 0) :
    ∃ a : ℕ → E → F, (∀ k, ContDiff ℝ (⊤ : ℕ∞) (a k)) ∧ (∀ k (e : E), e ∉ C → a k e = 0) ∧
      ∀ (n m : ℕ), m ≤ n → ∀ e : E,
        iteratedFDerivWithin ℝ m
          (fun p : E × ℝ => Ψ p - ∑ k ∈ Finset.range (n + 1), (p.2 ^ k / (k.factorial : ℝ)) • a k p.1)
          {p : E × ℝ | 0 ≤ p.2} (e, 0) = 0
```

### `MeasureTheory.exists_contDiff_forall_iteratedFDeriv_sub_sum_pow_smul_eq_zero`

`Thm_MeasureTheory_exists_contDiff_forall_iteratedFDeriv_sub_sum_pow_smul_eq_zero` — Borel's lemma with smooth compactly supported parameters

```lean
theorem MeasureTheory.exists_contDiff_forall_iteratedFDeriv_sub_sum_pow_smul_eq_zero
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (C : Set E) (hC : IsCompact C)
    (a : ℕ → E → F) (ha : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (a k)) (hsupp : ∀ k (e : E), e ∉ C → a k e = 0) :
    ∃ B : E × ℝ → F, ContDiff ℝ (⊤ : ℕ∞) B ∧
      ∀ (n m : ℕ), m ≤ n → ∀ e : E,
        iteratedFDeriv ℝ m
          (fun p : E × ℝ => B p - ∑ k ∈ Finset.range (n + 1), (p.2 ^ k / (k.factorial : ℝ)) • a k p.1) (e, 0) = 0
```

### `MeasureTheory.exists_contDiff_hasCompactSupport_integral_normSq_sub_integral_mul_cexp_lt_of_memLp_two`

`Thm_MeasureTheory_exists_contDiff_hasCompactSupport_integral_normSq_sub_integral_mul_cexp_lt_of_memLp_two` — Density in L²(ℝ) of exponential transforms of test functions

```lean
theorem MeasureTheory.exists_contDiff_hasCompactSupport_integral_normSq_sub_integral_mul_cexp_lt_of_memLp_two
    (G : ℝ → ℂ) (_hG : MemLp G 2) (ε : ℝ) (_hε : 0 < ε) :
    ∃ h : ℝ → ℂ, ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧
      MemLp (fun t : ℝ => ∫ x : ℝ, h x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) 2 ∧
      ∫ t : ℝ, ‖G t - ∫ x : ℝ, h x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))‖ ^ 2 < ε
```

### `MeasureTheory.exists_contDiff_integral_integral_mul_log_normSq_clm_add_normSq_eq_add_normSq_mul_log_mul_of_hasCompactSupport`

`Thm_MeasureTheory_exists_contDiff_integral_integral_mul_log_normSq_clm_add_normSq_eq_add_normSq_mul_log_mul_of_hasCompactSupport` — Parametric log-potential along a moving linear form: smooth plus ‖r‖²log‖r‖ term

```lean
theorem MeasureTheory.exists_contDiff_integral_integral_mul_log_normSq_clm_add_normSq_eq_add_normSq_mul_log_mul_of_hasCompactSupport
    {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (g : P × (ℂ × V) → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (L : P → (ℂ →L[ℝ] ℂ)) (hL : ContDiff ℝ (⊤ : ℕ∞) L) (hL0 : ∀ (p : P) (z : ℂ), L p z = 0 → z = 0)
    (φ : P → (V →L[ℝ] ℂ)) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ∃ A B : P × ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) A ∧ ContDiff ℝ (⊤ : ℕ∞) B ∧
      ∀ (p : P) (r : ℂ),
        Integrable (fun zv : ℂ × V =>
          g (p, zv) * (Real.log (‖L p zv.1 + φ p zv.2‖ ^ 2 + ‖r‖ ^ 2) : ℂ)) ((volume : Measure ℂ).prod μ) ∧
        ∫ zv : ℂ × V, g (p, zv) * (Real.log (‖L p zv.1 + φ p zv.2‖ ^ 2 + ‖r‖ ^ 2) : ℂ) ∂((volume : Measure ℂ).prod μ) =
          A (p, r) + ((‖r‖ ^ 2 * Real.log ‖r‖ : ℝ) : ℂ) * B (p, r)
```

### `MeasureTheory.exists_contDiff_integral_integral_mul_log_sq_linear_add_sq_eq_add_abs_mul_of_hasCompactSupport`

`Thm_MeasureTheory_exists_contDiff_integral_integral_mul_log_sq_linear_add_sq_eq_add_abs_mul_of_hasCompactSupport` — Parametric logarithmic potential along a moving linear form

```lean
theorem MeasureTheory.exists_contDiff_integral_integral_mul_log_sq_linear_add_sq_eq_add_abs_mul_of_hasCompactSupport
    {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (g : P × (ℝ × V) → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (c₀ : P → ℝ) (hc₀ : ContDiff ℝ (⊤ : ℕ∞) c₀) (hc₀0 : ∀ p, c₀ p ≠ 0)
    (φ : P → (V →L[ℝ] ℝ)) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ∃ A B : P × ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) A ∧ ContDiff ℝ (⊤ : ℕ∞) B ∧
      ∀ (p : P) (ρ : ℝ),
        Integrable (fun sv : ℝ × V =>
          g (p, sv) * (Real.log ((c₀ p * sv.1 + φ p sv.2) ^ 2 + ρ ^ 2) : ℂ)) ((volume : Measure ℝ).prod μ) ∧
        ∫ sv : ℝ × V, g (p, sv) * (Real.log ((c₀ p * sv.1 + φ p sv.2) ^ 2 + ρ ^ 2) : ℂ) ∂((volume : Measure ℝ).prod μ) =
          A (p, ρ) + ((|ρ| : ℝ) : ℂ) * B (p, ρ)
```

### `MeasureTheory.exists_contDiff_integral_integral_mul_log_sq_linear_add_sq_mul_sq_eq_add_abs_mul_of_hasCompactSupport`

`Thm_MeasureTheory_exists_contDiff_integral_integral_mul_log_sq_linear_add_sq_mul_sq_eq_add_abs_mul_of_hasCompactSupport` — Parametric log integral: smooth A(p,ρ)+|ρ|B(p,ρ) decomposition

```lean
theorem MeasureTheory.exists_contDiff_integral_integral_mul_log_sq_linear_add_sq_mul_sq_eq_add_abs_mul_of_hasCompactSupport
    {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (g : P × (ℝ × V) → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (c₀ : P → ℝ) (hc₀ : ContDiff ℝ (⊤ : ℕ∞) c₀) (hc₀0 : ∀ p, c₀ p ≠ 0)
    (φ : P → (V →L[ℝ] ℝ)) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (θ : P × V → ℝ) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθ0 : ∀ q, 0 ≤ θ q) :
    ∃ A B : P × ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) A ∧ ContDiff ℝ (⊤ : ℕ∞) B ∧
      ∀ (p : P) (ρ : ℝ),
        Integrable (fun sv : ℝ × V =>
          g (p, sv) * (Real.log ((c₀ p * sv.1 + φ p sv.2) ^ 2 + (ρ * θ (p, sv.2)) ^ 2) : ℂ)) ((volume : Measure ℝ).prod μ) ∧
        ∫ sv : ℝ × V, g (p, sv) * (Real.log ((c₀ p * sv.1 + φ p sv.2) ^ 2 + (ρ * θ (p, sv.2)) ^ 2) : ℂ) ∂((volume : Measure ℝ).prod μ) =
          A (p, ρ) + ((|ρ| : ℝ) : ℂ) * B (p, ρ)
```

### `MeasureTheory.exists_contDiff_integral_integral_mul_log_sq_one_sub_normSq_add_normSq_conj_add_conj_mul_eq_add_abs_mul_of_hasCompactSupport`

`Thm_MeasureTheory_exists_contDiff_integral_integral_mul_log_sq_one_sub_normSq_add_normSq_conj_add_conj_mul_eq_add_abs_mul_of_hasCompactSupport` — Smooth decomposition of a degenerating complex log potential

```lean
theorem MeasureTheory.exists_contDiff_integral_integral_mul_log_sq_one_sub_normSq_add_normSq_conj_add_conj_mul_eq_add_abs_mul_of_hasCompactSupport
    {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (g : P × (ℂ × V) → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (ϱ : P → ℂ) (hϱ : ContDiff ℝ (⊤ : ℕ∞) ϱ) :
    ∃ A B : P → ℂ, ContDiff ℝ (⊤ : ℕ∞) A ∧ ContDiff ℝ (⊤ : ℕ∞) B ∧
      ∀ p : P,
        Integrable (fun zv : ℂ × V =>
          g (p, zv) * (Real.log ((1 - ‖ϱ p‖ ^ 2) ^ 2 +
            ‖(starRingEnd ℂ) zv.1 + (starRingEnd ℂ) (ϱ p) * zv.1‖ ^ 2) : ℂ)) ((volume : Measure ℂ).prod μ) ∧
        ∫ zv : ℂ × V, g (p, zv) * (Real.log ((1 - ‖ϱ p‖ ^ 2) ^ 2 +
            ‖(starRingEnd ℂ) zv.1 + (starRingEnd ℂ) (ϱ p) * zv.1‖ ^ 2) : ℂ) ∂((volume : Measure ℂ).prod μ) =
          A p + ((|1 - ‖ϱ p‖ ^ 2| : ℝ) : ℂ) * B p
```

### `MeasureTheory.exists_contDiff_integral_mul_log_normSq_add_normSq_eq_add_normSq_mul_log_mul_of_hasCompactSupport`

`Thm_MeasureTheory_exists_contDiff_integral_mul_log_normSq_add_normSq_eq_add_normSq_mul_log_mul_of_hasCompactSupport` — Smooth splitting of logarithmic potentials with complex offset

```lean
theorem MeasureTheory.exists_contDiff_integral_mul_log_normSq_add_normSq_eq_add_normSq_mul_log_mul_of_hasCompactSupport
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (g : E × ℂ → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    ∃ A B : E × ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) A ∧ ContDiff ℝ (⊤ : ℕ∞) B ∧
      ∀ (e : E) (r : ℂ),
        ∫ z : ℂ, g (e, z) * (Real.log (‖z‖ ^ 2 + ‖r‖ ^ 2) : ℂ) =
          A (e, r) + ((‖r‖ ^ 2 * Real.log ‖r‖ : ℝ) : ℂ) * B (e, r)
```

### `MeasureTheory.exists_contDiff_integral_mul_log_sq_add_sq_eq_add_abs_mul_of_hasCompactSupport`

`Thm_MeasureTheory_exists_contDiff_integral_mul_log_sq_add_sq_eq_add_abs_mul_of_hasCompactSupport` — Logarithmic potential integral splits as A+|ρ|B

```lean
theorem MeasureTheory.exists_contDiff_integral_mul_log_sq_add_sq_eq_add_abs_mul_of_hasCompactSupport
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (g : E × ℝ → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    ∃ A B : E × ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) A ∧ ContDiff ℝ (⊤ : ℕ∞) B ∧
      ∀ (e : E) (ρ : ℝ),
        ∫ s : ℝ, g (e, s) * (Real.log (s ^ 2 + ρ ^ 2) : ℂ) = A (e, ρ) + ((|ρ| : ℝ) : ℂ) * B (e, ρ)
```

### `MeasureTheory.exists_contDiff_iteratedFDeriv_eq_iteratedFDerivWithin_halfSpace`

`Thm_MeasureTheory_exists_contDiff_iteratedFDeriv_eq_iteratedFDerivWithin_halfSpace` — Boundary jet on a half-space realised by a smooth function

```lean
theorem MeasureTheory.exists_contDiff_iteratedFDeriv_eq_iteratedFDerivWithin_halfSpace
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (Ψ : E × ℝ → F) (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ {p : E × ℝ | 0 ≤ p.2})
    (C : Set E) (hC : IsCompact C) (hsupp : ∀ p : E × ℝ, p.1 ∉ C → Ψ p = 0) :
    ∃ B : E × ℝ → F, ContDiff ℝ (⊤ : ℕ∞) B ∧
      ∀ (n : ℕ) (e : E),
        iteratedFDeriv ℝ n B (e, 0) = iteratedFDerivWithin ℝ n Ψ {p : E × ℝ | 0 ≤ p.2} (e, 0)
```

### `MeasureTheory.exists_continuous_convolution_self_eq_forall_integral_smul_isotypic`

`Thm_MeasureTheory_exists_continuous_convolution_self_eq_forall_integral_smul_isotypic` — Continuous idempotent weight projecting onto ρ-isotypic vectors

```lean
theorem MeasureTheory.exists_continuous_convolution_self_eq_forall_integral_smul_isotypic
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {n : ℕ} (ρ : K →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ) :
    ∃ e : K → ℂ, Continuous e ∧ (∀ k l : K, e (l * k * l⁻¹) = e k) ∧ (∀ k : K, e k⁻¹ = conj (e k)) ∧
      (∀ k : K, ∫ l, e l * e (l⁻¹ * k) ∂μ = e k) ∧
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (π : K →* (H →L[ℂ] H)), (∀ (k : K) (v : H), ‖π k v‖ = ‖v‖) → (∀ v : H, Continuous fun k : K => π k v) →
        ∀ A : H →L[ℂ] H, (∀ v : H, A v = ∫ k, (e k) • (π k v) ∂μ) →
          A.comp A = A ∧
          (∀ v : H, A v = v ↔
            ∃ (m : ℕ) (T : (Fin m → (Fin n → ℂ)) →L[ℂ] H),
              (∀ (k : K) (x : Fin m → (Fin n → ℂ)), T (fun i => (ρ k).mulVec (x i)) = π k (T x)) ∧
              v ∈ LinearMap.range (T : (Fin m → (Fin n → ℂ)) →ₗ[ℂ] H)) ∧
          (∀ v : H, ∃ (m : ℕ) (T : (Fin m → (Fin n → ℂ)) →L[ℂ] H),
              (∀ (k : K) (x : Fin m → (Fin n → ℂ)), T (fun i => (ρ k).mulVec (x i)) = π k (T x)) ∧
              A v ∈ LinearMap.range (T : (Fin m → (Fin n → ℂ)) →ₗ[ℂ] H))
```

### `MeasureTheory.exists_continuous_hasCompactSupport_forall_integral_comp_mul_eq_one`

`Thm_MeasureTheory_exists_continuous_hasCompactSupport_forall_integral_comp_mul_eq_one` — Truncation function with unit fibre integral along ι(H)

```lean
theorem MeasureTheory.exists_continuous_hasCompactSupport_forall_integral_comp_mul_eq_one
    {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (τ : Measure H) [τ.IsHaarMeasure] [τ.IsMulRightInvariant]
    (ι : H →* G) (hι : Topology.IsClosedEmbedding ι)
    (K : Set G) (hK : IsCompact K) :
    ∃ w : G → ℝ, Continuous w ∧ HasCompactSupport w ∧ (∀ g, 0 ≤ w g) ∧
      ∀ (h : H) (k : G), k ∈ K → ∫ h', w (ι h' * (ι h * k)) ∂τ = 1
```

### `MeasureTheory.exists_continuous_hasCompactSupport_forall_integral_subgroup_mul_eq_one_of_isInvInvariant`

`Thm_MeasureTheory_exists_continuous_hasCompactSupport_forall_integral_subgroup_mul_eq_one_of_isInvInvariant` — Bruhat function for a cocompact closed subgroup

```lean
theorem MeasureTheory.exists_continuous_hasCompactSupport_forall_integral_subgroup_mul_eq_one_of_isInvInvariant
    {T : Type*} [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
    (S : Subgroup T) (hS : IsClosed (S : Set T)) [MeasurableSpace S] [BorelSpace S]
    (τS : Measure S) [τS.IsHaarMeasure] [τS.IsInvInvariant]
    (C : Set T) (hC : IsCompact C) (hSC : ∀ t : T, ∃ s : S, ∃ c ∈ C, t = (s : T) * c) :
    ∃ β : T → ℝ, Continuous β ∧ HasCompactSupport β ∧ (∀ t, 0 ≤ β t) ∧
      ∀ t : T, ∫ s : S, β ((s : T) * t) ∂τS = 1
```

### `MeasureTheory.exists_continuous_integral_subgroup_mul_eq_one`

`Thm_MeasureTheory_exists_continuous_integral_subgroup_mul_eq_one` — Continuous cut-off with T-orbit integral one on a compact set

```lean
theorem MeasureTheory.exists_continuous_integral_subgroup_mul_eq_one
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [FirstCountableTopology G]
    (T : Subgroup G) (hT : IsClosed (T : Set G)) (hcomm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s)
    [MeasurableSpace T] [BorelSpace T] (τ : Measure T) [τ.IsHaarMeasure]
    (Ω : Set G) (hΩ : IsCompact Ω) :
    ∃ w : G → ℝ, Continuous w ∧ (∀ x, 0 ≤ w x) ∧ HasCompactSupport w ∧
      ∀ x : G, (∃ t ∈ T, ∃ d ∈ Ω, x = t * d) → ∫ t : T, w (t * x) ∂τ = 1
```

### `MeasureTheory.exists_div_le_of_le_setAverage_of_nonpos`

`Thm_MeasureTheory_exists_div_le_of_le_setAverage_of_nonpos` — Point selection from a set average on a large subset

```lean
theorem MeasureTheory.exists_div_le_of_le_setAverage_of_nonpos {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {s E : Set α} {ψ : α → ℝ} {A θ : ℝ}
    (hsm : MeasurableSet s) (hψ : MeasureTheory.IntegrableOn ψ s μ) (hψ0 : ∀ x ∈ s, ψ x ≤ 0)
    (hE : E ⊆ s) (hs0 : μ s ≠ 0) (hs : μ s ≠ ⊤) (hθ : 0 < θ) (hθE : θ * μ.real s ≤ μ.real E)
    (hA : -A ≤ ⨍ x in s, ψ x ∂μ) :
    ∃ x ∈ E, -A / θ ≤ ψ x
```

### `MeasureTheory.exists_finset_forall_exists_eLpNorm_sub_lt_of_equicontinuous_of_forall_ae_norm_le`

`Thm_MeasureTheory_exists_finset_forall_exists_eLpNorm_sub_lt_of_equicontinuous_of_forall_ae_norm_le` — Arzelà–Ascoli in Lᵖ: finite ε-nets for equicontinuous families

```lean
theorem MeasureTheory.exists_finset_forall_exists_eLpNorm_sub_lt_of_equicontinuous_of_forall_ae_norm_le
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {ι : Type*} (u : ι → X → E) (μ : Measure X) [IsFiniteMeasure μ]
    (p : ℝ≥0∞) (hp₁ : 1 ≤ p) (hp : p ≠ ∞)
    (htight : ∀ η : ℝ≥0∞, 0 < η → ∃ K : Set X, IsCompact K ∧ μ Kᶜ < η)
    (hequi : Equicontinuous u)
    (hpt : ∀ x, ∃ C₀ : ℝ, ∀ i, ‖u i x‖ ≤ C₀)
    (C : ℝ) (hbound : ∀ i, ∀ᵐ x ∂μ, ‖u i x‖ ≤ C)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ s : Finset ι, ∀ i, ∃ j ∈ s, eLpNorm (u i - u j) p μ < ε
```

### `MeasureTheory.exists_forall_contDiff_norm_iteratedDeriv_integral_cexp_mul_le_prod_of_contDiff`

`Thm_MeasureTheory_exists_forall_contDiff_norm_iteratedDeriv_integral_cexp_mul_le_prod_of_contDiff` — Uniform C² bounds for a partial Fourier transform

```lean
theorem MeasureTheory.exists_forall_contDiff_norm_iteratedDeriv_integral_cexp_mul_le_prod_of_contDiff
    (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (h : ℝ × (Fin n → ℝ) → ℂ), ContDiff ℝ (⊤ : ℕ∞) h →
        (∀ p : ℝ × (Fin n → ℝ), R < |p.1| → h p = 0) → (∀ p : ℝ × (Fin n → ℝ), (∃ k, R < |p.2 k|) → h p = 0) →
      ∀ M : ℝ, (∀ N : ℕ, N ≤ 2 * n + 2 → ∀ p : ℝ × (Fin n → ℝ), ‖iteratedFDeriv ℝ N h p‖ ≤ M) →
      ∀ ξ : Fin n → ℝ,
        ContDiff ℝ 2 (fun x : ℝ =>
          ∫ y : Fin n → ℝ, h (x, y) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * y k : ℝ) : ℂ)))) ∧
        (∀ x : ℝ, R < |x| →
          (∫ y : Fin n → ℝ, h (x, y) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * y k : ℝ) : ℂ)))) = 0) ∧
        ∀ j : ℕ, j ≤ 2 → ∀ x : ℝ,
          ‖iteratedDeriv j (fun x : ℝ =>
              ∫ y : Fin n → ℝ, h (x, y) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * y k : ℝ) : ℂ)))) x‖ ≤
            K * M * ∏ k, (1 + |ξ k|)⁻¹ ^ 2
```

### `MeasureTheory.exists_forall_contDiff_norm_iteratedFDeriv_integral_insertNth_mul_cexp_le_mul_prod`

`Thm_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_integral_insertNth_mul_cexp_le_mul_prod` — Uniform bounds for a partial Fourier transform with one free slot

```lean
theorem MeasureTheory.exists_forall_contDiff_norm_iteratedFDeriv_integral_insertNth_mul_cexp_le_mul_prod
    (n N : ℕ) (k : Fin (n + 1)) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (g : (Fin (n + 1) → ℝ) × ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) g →
      (∀ p : (Fin (n + 1) → ℝ) × ℝ, (∃ i, R < |p.1 i|) → g p = 0) →
      ∀ M : ℝ, (∀ i : ℕ, i ≤ N + 2 * n → ∀ p : (Fin (n + 1) → ℝ) × ℝ, ‖iteratedFDeriv ℝ i g p‖ ≤ M) →
      ∀ ξ' : Fin n → ℝ,
        let h : ℝ × ℝ → ℂ := fun q =>
          ∫ x' : Fin n → ℝ, g (Fin.insertNth k q.1 x', q.2) *
            Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, ξ' i * x' i : ℝ) : ℂ)))
        ContDiff ℝ (⊤ : ℕ∞) h ∧ (∀ q : ℝ × ℝ, R < |q.1| → h q = 0) ∧
          ∀ i : ℕ, i ≤ N → ∀ q : ℝ × ℝ,
            ‖iteratedFDeriv ℝ i h q‖ ≤ K * M * ∏ i', (1 + |ξ' i'|)⁻¹ ^ 2
```

### `MeasureTheory.exists_forall_contDiff_norm_iteratedFDeriv_integral_setIntegral_insertNth_mul_cexp_le_prod`

`Thm_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_integral_setIntegral_insertNth_mul_cexp_le_prod` — Mixed partial Fourier transform: smoothness and quadratic decay

```lean
theorem MeasureTheory.exists_forall_contDiff_norm_iteratedFDeriv_integral_setIntegral_insertNth_mul_cexp_le_prod
    {n d : ℕ} (W : (Fin (n + 1) → ℝ) × (Fin (d + 1) → ℝ) → ℂ) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (R : ℝ) (hR : 0 ≤ R) (hsupp : ∀ p : (Fin (n + 1) → ℝ) × (Fin (d + 1) → ℝ), (∃ k, R < |p.1 k|) → W p = 0)
    (hper : ∀ (p : (Fin (n + 1) → ℝ) × (Fin (d + 1) → ℝ)) (j : Fin (d + 1)), W (p.1, p.2 + Pi.single j 1) = W p)
    (k : Fin (n + 1)) (j : Fin (d + 1)) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (ξ' : Fin n → ℝ) (m' : Fin d → ℤ),
      let h : ℝ × ℝ → ℂ := fun q =>
        ∫ x' : Fin n → ℝ, ∫ θ' in Set.pi Set.univ (fun _ : Fin d => Set.Ico (0 : ℝ) 1),
          W (Fin.insertNth k q.1 x', Fin.insertNth j q.2 θ') *
            Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, ξ' i * x' i : ℝ) : ℂ))) *
            Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j', (m' j' : ℝ) * θ' j' : ℝ) : ℂ)))
      ContDiff ℝ (⊤ : ℕ∞) h ∧ (∀ q : ℝ × ℝ, R < |q.1| → h q = 0) ∧ (∀ q : ℝ × ℝ, h (q.1, q.2 + 1) = h q) ∧
        ∀ i : ℕ, i ≤ N → ∀ q : ℝ × ℝ,
          ‖iteratedFDeriv ℝ i h q‖ ≤ M * (∏ i', (1 + |ξ' i'|)⁻¹ ^ 2) * ∏ j', (1 + |(m' j' : ℝ)|)⁻¹ ^ 2
```

### `MeasureTheory.exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_insertNth_mul_cexp_le_prod`

`Thm_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_insertNth_mul_cexp_le_prod` — Uniform decay of partial angular Fourier modes, one angle free

```lean
theorem MeasureTheory.exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_insertNth_mul_cexp_le_prod
    {n d : ℕ} (W : (Fin (n + 1) → ℝ) × (Fin (d + 1) → ℝ) → ℂ) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (R : ℝ) (hR : 0 ≤ R) (hsupp : ∀ p : (Fin (n + 1) → ℝ) × (Fin (d + 1) → ℝ), (∃ k, R < |p.1 k|) → W p = 0)
    (hper : ∀ (p : (Fin (n + 1) → ℝ) × (Fin (d + 1) → ℝ)) (j : Fin (d + 1)), W (p.1, p.2 + Pi.single j 1) = W p)
    (j : Fin (d + 1)) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ m' : Fin d → ℤ,
      let g : (Fin (n + 1) → ℝ) × ℝ → ℂ := fun p =>
        ∫ θ' in Set.pi Set.univ (fun _ : Fin d => Set.Ico (0 : ℝ) 1),
          W (p.1, Fin.insertNth j p.2 θ') *
            Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j', (m' j' : ℝ) * θ' j' : ℝ) : ℂ)))
      ContDiff ℝ (⊤ : ℕ∞) g ∧ (∀ p : (Fin (n + 1) → ℝ) × ℝ, (∃ k, R < |p.1 k|) → g p = 0) ∧
        (∀ p : (Fin (n + 1) → ℝ) × ℝ, g (p.1, p.2 + 1) = g p) ∧
        ∀ i : ℕ, i ≤ N → ∀ p : (Fin (n + 1) → ℝ) × ℝ,
          ‖iteratedFDeriv ℝ i g p‖ ≤ M * ∏ j', (1 + |(m' j' : ℝ)|)⁻¹ ^ 2
```

### `MeasureTheory.exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_mul_cexp_le_mul_prod_of_contDiff_of_periodic`

`Thm_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_mul_cexp_le_mul_prod_of_contDiff_of_periodic` — Uniform decay of angular Fourier modes of a smooth periodic window

```lean
theorem MeasureTheory.exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_mul_cexp_le_mul_prod_of_contDiff_of_periodic
    {r c : ℕ} (W : (Fin r → ℝ) × (Fin c → ℝ) → ℂ) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (R : ℝ) (hR : 0 ≤ R) (hsupp : ∀ p : (Fin r → ℝ) × (Fin c → ℝ), (∃ k, R < |p.1 k|) → W p = 0)
    (hper : ∀ (p : (Fin r → ℝ) × (Fin c → ℝ)) (j : Fin c), W (p.1, p.2 + Pi.single j 1) = W p) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ m : Fin c → ℤ,
      ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin r → ℝ =>
        ∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
          W (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))) ∧
      (∀ x : Fin r → ℝ, (∃ k, R < |x k|) →
        (∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
          W (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))) = 0) ∧
      ∀ n : ℕ, n ≤ 2 * r → ∀ x : Fin r → ℝ,
        ‖iteratedFDeriv ℝ n (fun x : Fin r → ℝ =>
            ∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
              W (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))) x‖ ≤
          M * ∏ j, (1 + |(m j : ℝ)|)⁻¹ ^ 2
```

### `MeasureTheory.exists_forall_exists_clm_opNorm_le_noAtomicMass_forall_hasSum_fibre_mul_fourier_eq_apply_fourier_of_le_of_discrete_of_productFormula_of_fourier_decay`

`Thm_MeasureTheory_exists_forall_exists_clm_opNorm_le_noAtomicMass_forall_hasSum_fibre_mul_fourier_eq_apply_fourier_of_le_of_discrete_of_productFormula_of_fourier_decay` — Winding measures with sublattice-uniform total variation bound

```lean
theorem MeasureTheory.exists_forall_exists_clm_opNorm_le_noAtomicMass_forall_hasSum_fibre_mul_fourier_eq_apply_fourier_of_le_of_discrete_of_productFormula_of_fourier_decay
    (r d c : ℕ) (Λ : AddSubgroup ((Fin r → ℝ) × (Fin d → ℤ)))
    (hΛ : DiscreteTopology Λ)
    (s : (Fin r → ℝ) →ₗ[ℝ] ℝ) (ω : Fin d → ℝ) (hω : ω ≠ 0)
    (hpf : ∀ x ∈ Λ, s x.1 = ∑ i, ω i * (x.2 i : ℝ)) :
    ∃ K : ℝ, ∀ (Λ' : AddSubgroup ((Fin r → ℝ) × (Fin d → ℤ))) (hΛ' : Λ' ≤ Λ)
      (χ : Λ' →+ (Fin c → AddCircle (1 : ℝ))) (m : Fin c → ℤ) (θ₀ : Fin c → AddCircle (1 : ℝ))
      (Ψ : (Fin r → ℝ) → ℂ) (hΨc : Continuous Ψ) (hΨi : Integrable Ψ) (C : ℝ)
      (hΨd : ∀ x : Fin r → ℝ, ‖Ψ x‖ ≤ C * ∏ i, (1 + |x i|)⁻¹ ^ 2)
      (hΨhatd : ∀ ξ : Fin r → ℝ,
        ‖∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, ξ i * x i : ℝ) : ℂ))) * Ψ x‖ ≤
          C * ∏ i, (1 + |ξ i|)⁻¹ ^ 2)
      (x₀ : Fin r → ℝ) (n₀ : Fin d → ℤ),
    ∃ μ : C((Fin d → AddCircle (1 : ℝ)), ℂ) →L[ℂ] ℂ,
      ‖μ‖ ≤ K * C ∧
      (∀ (τ : Fin d → AddCircle (1 : ℝ)), ∀ ε > (0 : ℝ),
        ∃ U : Fin d → Set (AddCircle (1 : ℝ)), (∀ i, IsOpen (U i) ∧ τ i ∈ U i) ∧
          ∀ g : C((Fin d → AddCircle (1 : ℝ)), ℂ),
            (∀ θ, (∃ i, θ i ∉ U i) → g θ = 0) → (∀ θ, ‖g θ‖ ≤ 1) → ‖μ g‖ < ε) ∧
      ∀ (n : Fin d → ℤ) (e : C((Fin d → AddCircle (1 : ℝ)), ℂ)),
        (∀ θ, e θ = ∏ i, fourier (n i) (θ i)) →
        HasSum (fun γ : Λ' => if (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + n₀ = n
            then Ψ (x₀ + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1) * ∏ j, fourier (m j) (θ₀ j + χ γ j) else 0) (μ e)
```

### `MeasureTheory.exists_forall_norm_integral_cexp_mul_mul_le_of_norm_iteratedFDeriv_le_mul_log`

`Thm_MeasureTheory_exists_forall_norm_integral_cexp_mul_mul_le_of_norm_iteratedFDeriv_le_mul_log` — Fourier decay for a C⁴ window times a logarithmic degree-two singularity

```lean
theorem MeasureTheory.exists_forall_norm_integral_cexp_mul_mul_le_of_norm_iteratedFDeriv_le_mul_log
    (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (G : ℝ × ℝ → ℝ) (H : ℝ × ℝ → ℂ) (A B : ℝ), 0 ≤ A → 0 ≤ B →
        ContDiffOn ℝ 4 G {p : ℝ × ℝ | p ≠ 0} →
        (∀ n : ℕ, n ≤ 4 → ∀ p : ℝ × ℝ, p ≠ 0 → ‖p‖ ≤ r →
            ‖p‖ ^ n * ‖iteratedFDeriv ℝ n G p‖ ≤ A * ‖p‖ ^ 2 * (1 + |Real.log ‖p‖|)) →
        ContDiff ℝ 4 H → (∀ p : ℝ × ℝ, r ≤ ‖p‖ → H p = 0) →
        (∀ n : ℕ, n ≤ 4 → ∀ p : ℝ × ℝ, ‖iteratedFDeriv ℝ n H p‖ ≤ B) →
        ∀ ξ η : ℝ,
          ‖∫ p : ℝ × ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((ξ * p.1 + η * p.2 : ℝ) : ℂ))) *
              ((G p : ℂ) * H p)‖ ≤
            C * A * B * ((1 + |ξ| + |η|) ^ (7 / 2 : ℝ))⁻¹
```

### `MeasureTheory.exists_forall_norm_integral_integral_cexp_mul_le_of_contDiff_of_periodic`

`Thm_MeasureTheory_exists_forall_norm_integral_integral_cexp_mul_le_of_contDiff_of_periodic` — Mixed Fourier decay for C⁴ functions periodic in θ

```lean
theorem MeasureTheory.exists_forall_norm_integral_integral_cexp_mul_le_of_contDiff_of_periodic
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F : ℝ × ℝ → ℂ), ContDiff ℝ 4 F → (∀ p : ℝ × ℝ, R < |p.1| → F p = 0) →
        (∀ p : ℝ × ℝ, F (p.1, p.2 + 1) = F p) →
      ∀ B : ℝ, (∀ n : ℕ, n ≤ 4 → ∀ p : ℝ × ℝ, ‖iteratedFDeriv ℝ n F p‖ ≤ B) →
      ∀ (ξ : ℝ) (m : ℤ),
        ‖∫ x : ℝ, ∫ θ in Set.Ico (0 : ℝ) 1,
            Complex.exp (-(2 * Real.pi * Complex.I * ((ξ * x + m * θ : ℝ) : ℂ))) * F (x, θ)‖ ≤
          C * B * (1 + |ξ|)⁻¹ ^ 2 * (1 + |(m : ℝ)|)⁻¹ ^ 2
```

### `MeasureTheory.exists_forall_norm_integral_integral_cexp_mul_normSq_log_germ_mul_le`

`Thm_MeasureTheory_exists_forall_norm_integral_integral_cexp_mul_normSq_log_germ_mul_le` — Decay of a mixed Fourier transform of ρ²logρ germ

```lean
theorem MeasureTheory.exists_forall_norm_integral_integral_cexp_mul_normSq_log_germ_mul_le
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (h : ℝ × ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) h → (∀ p : ℝ × ℝ, R < |p.1| → h p = 0) →
        (∀ p : ℝ × ℝ, h (p.1, p.2 + 1) = h p) →
      ∀ M : ℝ, (∀ n : ℕ, n ≤ 6 → ∀ p : ℝ × ℝ, ‖iteratedFDeriv ℝ n h p‖ ≤ M) →
      ∀ (ξ : ℝ) (m : ℤ),
        ‖∫ x : ℝ, ∫ θ in Set.Ico (0 : ℝ) 1,
            Complex.exp (-(2 * Real.pi * Complex.I * ((ξ * x + m * θ : ℝ) : ℂ))) *
              ((‖(1 : ℂ) - Complex.exp ((x / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ : ℝ))‖ ^ 2 *
                  Real.log ‖(1 : ℂ) - Complex.exp ((x / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ : ℝ))‖ : ℝ) : ℂ) *
              h (x, θ)‖ ≤
          K * M * (1 + |ξ|)⁻¹ ^ 2 * ((1 + |(m : ℝ)|) ^ (3 / 2 : ℝ))⁻¹
```

### `MeasureTheory.exists_forall_norm_le_mul_prod_and_norm_integral_cexp_mul_le_of_contDiff_of_hasCompactSupport`

`Thm_MeasureTheory_exists_forall_norm_le_mul_prod_and_norm_integral_cexp_mul_le_of_contDiff_of_hasCompactSupport` — Smooth compactly supported functions have product quadratic Fourier decay

```lean
theorem MeasureTheory.exists_forall_norm_le_mul_prod_and_norm_integral_cexp_mul_le_of_contDiff_of_hasCompactSupport
    {r : ℕ} (Ψ : (Fin r → ℝ) → ℂ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨc : HasCompactSupport Ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ Continuous Ψ ∧ Integrable Ψ ∧
      (∀ x : Fin r → ℝ, ‖Ψ x‖ ≤ C * ∏ k, (1 + |x k|)⁻¹ ^ 2) ∧
      (∀ ξ : Fin r → ℝ,
        ‖∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) * Ψ x‖ ≤
          C * ∏ k, (1 + |ξ k|)⁻¹ ^ 2)
```

### `MeasureTheory.exists_forall_norm_sq_le_mul_integral_norm_sq_sum_of_definite`

`Thm_MeasureTheory_exists_forall_norm_sq_le_mul_integral_norm_sq_sum_of_definite` — Coordinate domination by an L²-norm of a definite family

```lean
theorem MeasureTheory.exists_forall_norm_sq_le_mul_integral_norm_sq_sum_of_definite
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {n : ℕ} (b : Fin n → X → ℂ)
    (hint : ∀ i j : Fin n, Integrable (fun x => b i x * conj (b j x)) μ)
    (hdef : ∀ a : Fin n → ℂ, (∫ x, ‖∑ j, a j * b j x‖ ^ 2 ∂μ) = 0 → a = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Fin n → ℂ) (i : Fin n), ‖a i‖ ^ 2 ≤ C * ∫ x, ‖∑ j, a j * b j x‖ ^ 2 ∂μ
```

### `MeasureTheory.exists_forall_summable_integral_prod_inv_one_add_abs_sq_continuousLinearEquiv_le`

`Thm_MeasureTheory_exists_forall_summable_integral_prod_inv_one_add_abs_sq_continuousLinearEquiv_le` — Uniform lattice-sum bound for a skew product Poisson kernel

```lean
theorem MeasureTheory.exists_forall_summable_integral_prod_inv_one_add_abs_sq_continuousLinearEquiv_le
    (a b r : ℕ) (S : ((Fin a → ℝ) × (Fin b → ℝ)) ≃L[ℝ] (Fin r → ℝ)) :
    ∃ K : ℝ, ∀ (ψ : Fin a → ℝ) (t : Fin r → ℝ),
      (∀ κ : Fin a → ℤ, Integrable fun η : Fin b → ℝ =>
        ∏ i, (1 + |S ((fun j => (κ j : ℝ) + ψ j), η) i - t i|)⁻¹ ^ 2) ∧
      Summable (fun κ : Fin a → ℤ =>
        ∫ η : Fin b → ℝ, ∏ i, (1 + |S ((fun j => (κ j : ℝ) + ψ j), η) i - t i|)⁻¹ ^ 2) ∧
      ∑' κ : Fin a → ℤ, ∫ η : Fin b → ℝ, ∏ i, (1 + |S ((fun j => (κ j : ℝ) + ψ j), η) i - t i|)⁻¹ ^ 2 ≤ K
```

### `MeasureTheory.exists_hasCompactSupport_integral_subgroup_translate_eq_one_of_subset_mul`

`Thm_MeasureTheory_exists_hasCompactSupport_integral_subgroup_translate_eq_one_of_subset_mul` — Bruhat section functions for a closed subgroup

```lean
theorem MeasureTheory.exists_hasCompactSupport_integral_subgroup_translate_eq_one_of_subset_mul
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (τ : Measure T) [τ.IsHaarMeasure] [τ.IsMulRightInvariant]
    {E C : Set G} (hC : IsCompact C) (hE : E ⊆ (T : Set G) * C) :
    ∃ w : G → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧
      ∀ x ∈ E, ∫ t : T, w ((t : G) * x) ∂τ = 1
```

### `MeasureTheory.exists_hasSum_mul_zpow_eval_mul_integral_prod_of_ae_forall_integral_mul_zpow_mul_eval_eq`

`Thm_MeasureTheory_exists_hasSum_mul_zpow_eval_mul_integral_prod_of_ae_forall_integral_mul_zpow_mul_eval_eq` — Fibrewise functional equation transported through an outer integral

```lean
theorem MeasureTheory.exists_hasSum_mul_zpow_eval_mul_integral_prod_of_ae_forall_integral_mul_zpow_mul_eval_eq
    {X T₁ T₂ : Type*} [MeasurableSpace X] [MeasurableSpace T₁] [MeasurableSpace T₂]
    (m : Measure X) (μ₁ : Measure T₁) (μ₂ : Measure T₂) [SFinite m] [SFinite μ₁] [SFinite μ₂]
    (E₁ : X × T₁ → ℤ) (hE₁ : Measurable E₁) (E₂ : X × T₂ → ℤ) (hE₂ : Measurable E₂)
    (G₁ : X × T₁ → ℂ) (G₂ : X × T₂ → ℂ)
    {a₁ b₁ a₂ b₂ : ℝ} (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (hG₁ : ∀ r : ℝ, a₁ < r → r < b₁ → Integrable (fun p => G₁ p * (r : ℂ) ^ E₁ p) (m.prod μ₁))
    (hG₂ : ∀ r : ℝ, a₂ < r → r < b₂ → Integrable (fun p => G₂ p * (r : ℂ) ^ E₂ p) (m.prod μ₂))
    (Q₁ Q₂ : Polynomial ℂ) (C : ℂ) (k : ℤ)
    (hfe : ∀ᵐ x ∂m, ∃ (P : Polynomial ℂ) (n : ℤ) (a₁' b₁' a₂' b₂' : ℝ),
      0 ≤ a₁' ∧ a₁' < b₁' ∧ 0 ≤ a₂' ∧ a₂' < b₂' ∧
      (∀ Y : ℂ, a₁' < ‖Y‖ → ‖Y‖ < b₁' →
        Integrable (fun t => G₁ (x, t) * Y ^ E₁ (x, t)) μ₁ ∧
        (∫ t, G₁ (x, t) * Y ^ E₁ (x, t) ∂μ₁) * Q₁.eval Y = P.eval Y * Y ^ n) ∧
      (∀ Y : ℂ, a₂' < ‖Y‖ → ‖Y‖ < b₂' →
        Integrable (fun t => G₂ (x, t) * Y ^ E₂ (x, t)) μ₂ ∧
        (∫ t, G₂ (x, t) * Y ^ E₂ (x, t) ∂μ₂) * Q₂.eval Y = C * Y ^ k * (P.eval Y * Y ^ n))) :
    ∃ e : ℤ → ℂ,
      (∀ r : ℝ, a₁ < r → r < b₁ → Summable fun j : ℤ => ‖e j‖ * r ^ j) ∧
      (∀ Y : ℂ, a₁ < ‖Y‖ → ‖Y‖ < b₁ →
        HasSum (fun j : ℤ => e j * Y ^ j) (Q₁.eval Y * ∫ p, G₁ p * Y ^ E₁ p ∂(m.prod μ₁))) ∧
      (∀ r : ℝ, a₂ < r → r < b₂ → Summable fun j : ℤ => ‖C * e (j - k)‖ * r ^ j) ∧
      (∀ Y : ℂ, a₂ < ‖Y‖ → ‖Y‖ < b₂ →
        HasSum (fun j : ℤ => C * e (j - k) * Y ^ j) (Q₂.eval Y * ∫ p, G₂ p * Y ^ E₂ p ∂(m.prod μ₂)))
```

### `MeasureTheory.exists_integral_conj_apply_smul_ne_zero_of_forall_norm_apply_eq_of_continuous`

`Thm_MeasureTheory_exists_integral_conj_apply_smul_ne_zero_of_forall_norm_apply_eq_of_continuous` — Non-vanishing matrix coefficient mean for isometric representations

```lean
theorem MeasureTheory.exists_integral_conj_apply_smul_ne_zero_of_forall_norm_apply_eq_of_continuous
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : K →* (H →L[ℂ] H))
    (hπn : ∀ (k : K) (v : H), ‖π k v‖ = ‖v‖)
    (hπc : ∀ v : H, Continuous fun k : K => π k v)
    (hsep : ∀ k : K, k ≠ 1 →
      ∃ (n : ℕ) (ρ : K →* Matrix (Fin n) (Fin n) ℂ), Continuous ρ ∧ ρ k ≠ 1)
    (v : H) (hv : v ≠ 0) :
    ∃ (n : ℕ) (ρ : K →* Matrix (Fin n) (Fin n) ℂ) (i j : Fin n), Continuous ρ ∧
      ∫ k, (conj ((ρ k) i j)) • (π k v) ∂μ ≠ 0
```

### `MeasureTheory.exists_integral_eq_inv_card_mul_sum_of_isOpen_subgroup`

`Thm_MeasureTheory_exists_integral_eq_inv_card_mul_sum_of_isOpen_subgroup` — Integral over a compact group as a finite coset average

```lean
theorem MeasureTheory.exists_integral_eq_inv_card_mul_sum_of_isOpen_subgroup
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    (H : Subgroup K) (hH : IsOpen (H : Set K)) :
    ∃ (n : ℕ) (r : Fin n → K), H.index = n ∧ 0 < n ∧
      (∀ v : K, ∃ i, (r i)⁻¹ * v ∈ H) ∧
      (∀ i j, (r i)⁻¹ * r j ∈ H → i = j) ∧
      ∀ h : K → ℂ, (∀ v : K, ∀ w ∈ H, h (v * w) = h v) →
        ∫ v, h v ∂μ = (n : ℂ)⁻¹ * ∑ i, h (r i)
```

### `MeasureTheory.exists_integral_fourierChar_bilinForm_mul_ne_zero_of_continuousOn`

`Thm_MeasureTheory_exists_integral_fourierChar_bilinForm_mul_ne_zero_of_continuousOn` — Non-vanishing Fourier coefficient of a locally continuous integrable function

```lean
theorem MeasureTheory.exists_integral_fourierChar_bilinForm_mul_ne_zero_of_continuousOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (B : LinearMap.BilinForm ℝ V) (_hB : B.Nondegenerate)
    (G : V → ℂ) (_hG : Integrable G μ)
    (U : Set V) (_hU : IsOpen U) (_hGU : ContinuousOn G U)
    (z₀ : V) (_hz₀ : z₀ ∈ U) (_h0 : G z₀ ≠ 0) :
    ∃ u : V, ∫ z, ((Real.fourierChar (B z u) : Circle) : ℂ) * G z ∂μ ≠ 0
```

### `MeasureTheory.exists_isCompact_forall_exists_eq_mul_of_map_mul_eq_of_isAddFundamentalDomain`

`Thm_MeasureTheory_exists_isCompact_forall_exists_eq_mul_of_map_mul_eq_of_isAddFundamentalDomain` — Fujisaki compactness in an abstract topological ring

```lean
theorem MeasureTheory.exists_isCompact_forall_exists_eq_mul_of_map_mul_eq_of_isAddFundamentalDomain
    {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    [MeasurableSpace R] [BorelSpace R]
    (α : Measure R) [SFinite α] [α.IsAddLeftInvariant]
    (Λ : AddSubgroup R) [Countable Λ]
    (hmul : ∀ x ∈ Λ, ∀ y ∈ Λ, x * y ∈ Λ)
    (hfin : ∀ C : Set R, IsCompact C → (C ∩ (Λ : Set R)).Finite)
    (hdiv : ∀ x ∈ Λ, x ≠ 0 → ∃ u : Rˣ, (u : R) = x ∧ ((u⁻¹ : Rˣ) : R) ∈ Λ)
    (F : Set R) (hF : IsAddFundamentalDomain Λ F α)
    (C₀ : Set R) (hC₀ : IsCompact C₀) (hlt : α F < α C₀) :
    ∃ C : Set Rˣ, IsCompact C ∧
      ∀ t : Rˣ, Measure.map (fun x : R => (t : R) * x) α = α →
        Measure.map (fun x : R => x * (t : R)) α = α →
        ∃ l : Rˣ, (l : R) ∈ Λ ∧ ((l⁻¹ : Rˣ) : R) ∈ Λ ∧ ∃ k ∈ C, t = l * k
```

### `MeasureTheory.exists_isLocallyConstant_integral_subgroup_mul_eq_one`

`Thm_MeasureTheory_exists_isLocallyConstant_integral_subgroup_mul_eq_one` — Locally constant cut-off with unit T-integral on TΩ

```lean
theorem MeasureTheory.exists_isLocallyConstant_integral_subgroup_mul_eq_one
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K₀ : Subgroup G) (hK₀ : IsCompact (K₀ : Set G)) (hK₀' : IsOpen (K₀ : Set G))
    (T : Subgroup G) (hT : IsClosed (T : Set G)) (hcomm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s)
    [MeasurableSpace T] [BorelSpace T] (τ : Measure T) [τ.IsHaarMeasure]
    (Ω : Set G) (hΩ : IsCompact Ω) :
    ∃ w : G → ℝ, (∀ x, 0 ≤ w x) ∧ IsLocallyConstant w ∧ HasCompactSupport w ∧
      ∀ x : G, (∃ t ∈ T, ∃ d ∈ Ω, x = t * d) → ∫ t : T, w (t * x) ∂τ = 1
```

### `MeasureTheory.exists_isOpen_injOn_forall_mul_lintegral_comp_le_lintegral_image_of_det_fderiv_ne_zero`

`Thm_MeasureTheory_exists_isOpen_injOn_forall_mul_lintegral_comp_le_lintegral_image_of_det_fderiv_ne_zero` — Local lower bound for change of variables at a nondegenerate point

```lean
theorem MeasureTheory.exists_isOpen_injOn_forall_mul_lintegral_comp_le_lintegral_image_of_det_fderiv_ne_zero
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E → E) (a : E) (hf : ContDiffAt ℝ 1 f a) (hf' : (fderiv ℝ f a).det ≠ 0) :
    ∃ s : Set E, IsOpen s ∧ a ∈ s ∧ Set.InjOn f s ∧ ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ t ⊆ s, MeasurableSet t → ∀ g : E → ℝ≥0∞,
        (δ : ℝ≥0∞) * ∫⁻ x in t, g (f x) ∂μ ≤ ∫⁻ y in f '' t, g y ∂μ
```

### `MeasureTheory.exists_kernel_moments_integral_eq_one_forall_exists_contDiff_hasCompactSupport_integral_mul_scaledKernel_eq_integral_mul_cexp`

`Thm_MeasureTheory_exists_kernel_moments_integral_eq_one_forall_exists_contDiff_hasCompactSupport_integral_mul_scaledKernel_eq_integral_mul_cexp` — An admissible mollifier kernel with smooth compactly supported Fourier inverse

```lean
theorem MeasureTheory.exists_kernel_moments_integral_eq_one_forall_exists_contDiff_hasCompactSupport_integral_mul_scaledKernel_eq_integral_mul_cexp :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧ (∀ n : ℕ, Integrable (fun t : ℝ => |t| ^ n * ρ t)) ∧ (∫ t : ℝ, ρ t = 1) ∧
      ∀ (u : ℝ → ℂ), Measurable u → (∃ R : ℝ, ∀ x, R < |x| → u x = 0) → (∃ B : ℝ, ∀ x, ‖u x‖ ≤ B) →
      ∀ δ : ℝ, 0 < δ →
      ∃ h : ℝ → ℂ, ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧
        ∀ t : ℝ, (∫ x : ℝ, u x * ((δ⁻¹ * ρ ((t - x) / δ) : ℝ) : ℂ)) =
          ∫ x : ℝ, h x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))
```

### `MeasureTheory.exists_measurableEquiv_measurePreserving_pi_apply_succ_eq_inv_mul_mul`

`Thm_MeasureTheory_exists_measurableEquiv_measurePreserving_pi_apply_succ_eq_inv_mul_mul` — A measure-preserving shearing change of variables on Gⁿ⁺¹

```lean
theorem MeasureTheory.exists_measurableEquiv_measurePreserving_pi_apply_succ_eq_inv_mul_mul
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] {n : ℕ} (D : Fin (n + 1) → G) :
    ∃ Θ : (Fin (n + 1) → G) ≃ᵐ (Fin (n + 1) → G),
      MeasurePreserving Θ (Measure.pi fun _ => μ) (Measure.pi fun _ => μ) ∧
      ∀ x : Fin (n + 1) → G, Θ x 0 = x 0 ∧
        ∀ k : Fin n, Θ x k.succ = (x k.castSucc)⁻¹ * D k.castSucc * x k.succ
```

### `MeasureTheory.exists_measurableSet_isFundamentalDomain_op_of_discreteTopology`

`Thm_MeasureTheory_exists_measurableSet_isFundamentalDomain_op_of_discreteTopology` — Borel transversal for a discrete subgroup

```lean
theorem MeasureTheory.exists_measurableSet_isFundamentalDomain_op_of_discreteTopology
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) (hΓ : DiscreteTopology Γ) :
    ∃ D : Set G, MeasurableSet D ∧ (∀ x : G, ∃! γ : Γ, x * (γ : G) ∈ D) ∧
      ∀ μ : Measure G, IsFundamentalDomain Γ.op D μ
```

### `MeasureTheory.exists_mem_le_of_setAverage_chain`

`Thm_MeasureTheory_exists_mem_le_of_setAverage_chain` — Harnack chain: iterated sub-mean-value and overlap bound

```lean
theorem MeasureTheory.exists_mem_le_of_setAverage_chain {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {ψ : α → ℝ} {G : ℕ → Set α} {B : ℕ → α → Set α} {L : ℕ}
    {A₀ κ θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hκ : 0 ≤ κ)
    (hBm : ∀ l < L, ∀ p ∈ G l, MeasurableSet (B l p))
    (hB0 : ∀ l < L, ∀ p ∈ G l, μ (B l p) ≠ 0)
    (hBt : ∀ l < L, ∀ p ∈ G l, μ (B l p) ≠ ⊤)
    (hψ0 : ∀ l < L, ∀ p ∈ G l, ∀ x ∈ B l p, ψ x ≤ 0)
    (hint : ∀ l < L, ∀ p ∈ G l, MeasureTheory.IntegrableOn ψ (B l p) μ)
    (hsmv : ∀ l < L, ∀ p ∈ G l, ψ p - κ ≤ ⨍ x in B l p, ψ x ∂μ)
    (hovl : ∀ l < L, ∀ p ∈ G l, θ * μ.real (B l p) ≤ μ.real (B l p ∩ G (l + 1)))
    {p₀ : α} (hp₀ : p₀ ∈ G 0) (hA₀ : -A₀ ≤ ψ p₀) :
    ∀ l ≤ L, ∃ p ∈ G l, -((A₀ + l * κ) / θ ^ l) ≤ ψ p
```

### `MeasureTheory.exists_nhds_one_forall_eLpNorm_comp_mul_sub_lt_of_memLp_two`

`Thm_MeasureTheory_exists_nhds_one_forall_eLpNorm_comp_mul_sub_lt_of_memLp_two` — Strong continuity at 1 of right translation on L²(G,μ)

```lean
theorem MeasureTheory.exists_nhds_one_forall_eLpNorm_comp_mul_sub_lt_of_memLp_two
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (F : G → ℂ) (hF : MemLp F 2 μ) (ε : ℝ) (hε : 0 < ε) :
    ∃ V ∈ 𝓝 (1 : G), ∀ x ∈ V, eLpNorm (fun g => F (g * x) - F g) 2 μ < ENNReal.ofReal ε
```

### `MeasureTheory.exists_nonneg_hasCompactSupport_forall_integral_subgroup_translate_eq_one_of_isCompact`

`Thm_MeasureTheory_exists_nonneg_hasCompactSupport_forall_integral_subgroup_translate_eq_one_of_isCompact` — A compactly supported T-section over a compact set

```lean
theorem MeasureTheory.exists_nonneg_hasCompactSupport_forall_integral_subgroup_translate_eq_one_of_isCompact
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (τ : Measure T) [τ.IsHaarMeasure] [τ.IsMulRightInvariant]
    (Ω : Set G) (hΩ : IsCompact Ω) :
    ∃ W : G → ℝ, (∀ x, 0 ≤ W x) ∧ Measurable W ∧ HasCompactSupport W ∧ (∃ B : ℝ, ∀ x, W x ≤ B) ∧
      ∀ x : G, (∃ t : T, ∃ k ∈ Ω, x = (t : G) * k) → ∫ t : T, W ((t : G) * x) ∂τ = 1
```

### `MeasureTheory.exists_pos_forall_integral_eq_of_forall_integral_subgroup_translate_eq_one_of_isCompact`

`Thm_MeasureTheory_exists_pos_forall_integral_eq_of_forall_integral_subgroup_translate_eq_one_of_isCompact` — Covolume of a cocompact closed subgroup via section functions

```lean
theorem MeasureTheory.exists_pos_forall_integral_eq_of_forall_integral_subgroup_translate_eq_one_of_isCompact
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (μ : Measure G) [μ.IsHaarMeasure] (τ : Measure T) [τ.IsHaarMeasure] [τ.IsInvInvariant]
    (C : Set G) (hC : IsCompact C) (hcov : ∀ g : G, ∃ t : T, ∃ k ∈ C, g = (t : G) * k) :
    ∃ κ : ℝ, 0 < κ ∧
      (∃ w : G → ℝ, (∀ x, 0 ≤ w x) ∧ Continuous w ∧ HasCompactSupport w ∧
        ∀ x : G, ∫ t : T, w ((t : G) * x) ∂τ = 1) ∧
      ∀ w : G → ℝ, (∀ x, 0 ≤ w x) → Measurable w → HasCompactSupport w →
        (∀ x : G, ∫ t : T, w ((t : G) * x) ∂τ = 1) → ∫ x, w x ∂μ = κ
```

### `MeasureTheory.exists_section_integral_mul_eq_sum_div_of_forall_eq_of_forall_exists`

`Thm_MeasureTheory_exists_section_integral_mul_eq_sum_div_of_forall_eq_of_forall_exists` — Existence of a section weight for finitely many T–U double cosets

```lean
theorem MeasureTheory.exists_section_integral_mul_eq_sum_div_of_forall_eq_of_forall_exists
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (U : Set G)
    (hUo : IsOpen U) (hUc : IsCompact U) (hμUtop : μ U ≠ ⊤)
    (h1U : (1 : G) ∈ U) (hUmul : ∀ a ∈ U, ∀ b ∈ U, a * b ∈ U) (hUinv : ∀ a ∈ U, a⁻¹ ∈ U)
    (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (τ : Measure T) [τ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts τ] [τ.IsOpenPosMeasure]
    (ψ : G → ℂ) (hψ : ∀ t ∈ T, ∀ x : G, ∀ u ∈ U, ψ (t * x * u) = ψ x)
    (S : Finset G)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ T, ∀ u ∈ U, s' = t * s * u → s' = s)
    (hcov : ∀ x, ψ x ≠ 0 → ∃ s ∈ S, ∃ t ∈ T, ∃ u ∈ U, x = t * s * u) :
    ∃ w : G → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧
      (∀ x, ψ x ≠ 0 → ∫ t : T, w ((t : G) * x) ∂τ = 1) ∧
      ∫ x, ψ x * (w x : ℂ) ∂μ =
        ∑ s ∈ S, ψ s * ((μ U).toReal : ℂ) / ((τ {t : T | s⁻¹ * (t : G) * s ∈ U}).toReal : ℂ)
```

### `MeasureTheory.exists_summable_forall_fourierMode_absOneSubExp_mul_productPoisson_of_contDiff_of_periodic`

`Thm_MeasureTheory_exists_summable_forall_fourierMode_absOneSubExp_mul_productPoisson_of_contDiff_of_periodic` — Summable Fourier modes of a kink-weighted periodic window

```lean
theorem MeasureTheory.exists_summable_forall_fourierMode_absOneSubExp_mul_productPoisson_of_contDiff_of_periodic
    {r c : ℕ} (W : (Fin r → ℝ) × (Fin c → ℝ) → ℂ) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (R : ℝ) (hR : 0 ≤ R) (hsupp : ∀ p : (Fin r → ℝ) × (Fin c → ℝ), (∃ k, R < |p.1 k|) → W p = 0)
    (hper : ∀ (p : (Fin r → ℝ) × (Fin c → ℝ)) (j : Fin c), W (p.1, p.2 + Pi.single j 1) = W p)
    (k : Fin r) :
    let Ψ : (Fin c → ℤ) → (Fin r → ℝ) → ℂ := fun m x =>
      ∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
        ((|1 - Real.exp (x k)| : ℝ) : ℂ) * W (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j', (m j' : ℝ) * θ j' : ℝ) : ℂ)))
    ∃ C : (Fin c → ℤ) → ℝ, (∀ m, 0 ≤ C m) ∧ Summable C ∧
      ∀ m : Fin c → ℤ, Continuous (Ψ m) ∧ Integrable (Ψ m) ∧
        (∀ x : Fin r → ℝ, ‖Ψ m x‖ ≤ C m * ∏ i, (1 + |x i|)⁻¹ ^ 2) ∧
        (∀ ξ : Fin r → ℝ,
          ‖∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, ξ i * x i : ℝ) : ℂ))) * Ψ m x‖ ≤
            C m * ∏ i, (1 + |ξ i|)⁻¹ ^ 2)
```

### `MeasureTheory.exists_summable_forall_fourierMode_kinkWindow_productPoisson`

`Thm_MeasureTheory_exists_summable_forall_fourierMode_kinkWindow_productPoisson` — Product-Poisson bounds for Fourier modes of kink windows

```lean
theorem MeasureTheory.exists_summable_forall_fourierMode_kinkWindow_productPoisson
    {r c : ℕ} (kC : Fin c → Fin r) {ιR : Type} [Fintype ιR] (kR : ιR → Fin r)
    (B : (Fin r → ℝ) × (Fin c → ℝ) → ℂ) (C : ιR → (Fin r → ℝ) × (Fin c → ℝ) → ℂ)
    (E : Fin c → (Fin r → ℝ) × (Fin c → ℝ) → ℂ)
    (hB : ContDiff ℝ (⊤ : ℕ∞) B) (hC : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (C i)) (hE : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (E j))
    (hper : ∀ (p : (Fin r → ℝ) × (Fin c → ℝ)) (j : Fin c),
      B (p.1, p.2 + Pi.single j 1) = B p ∧ (∀ i, C i (p.1, p.2 + Pi.single j 1) = C i p) ∧
        ∀ j', E j' (p.1, p.2 + Pi.single j 1) = E j' p)
    (S : Set (Fin r → ℝ)) (hS : IsCompact S)
    (hsupp : ∀ p : (Fin r → ℝ) × (Fin c → ℝ), p.1 ∉ S → B p = 0 ∧ (∀ i, C i p = 0) ∧ ∀ j, E j p = 0) :
    let G : (Fin r → ℝ) × (Fin c → ℝ) → ℂ := fun p =>
      B p + ∑ i, ((|1 - Real.exp (p.1 (kR i))| : ℝ) : ℂ) * C i p +
        ∑ j, ((‖(1 : ℂ) - Complex.exp ((p.1 (kC j) / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 j : ℝ))‖ ^ 2 *
              Real.log ‖(1 : ℂ) - Complex.exp ((p.1 (kC j) / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 j : ℝ))‖ : ℝ) : ℂ) *
            E j p
    let Gm : (Fin c → ℤ) → (Fin r → ℝ) → ℂ := fun m x =>
      ∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
        G (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))
    ∃ Cm : (Fin c → ℤ) → ℝ, (∀ m, 0 ≤ Cm m) ∧ Summable Cm ∧
      (∀ m, Continuous (Gm m) ∧ Integrable (Gm m) ∧
        (∀ x : Fin r → ℝ, ‖Gm m x‖ ≤ Cm m * ∏ k, (1 + |x k|)⁻¹ ^ 2) ∧
        (∀ ξ : Fin r → ℝ,
          ‖∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) * Gm m x‖ ≤
            Cm m * ∏ k, (1 + |ξ k|)⁻¹ ^ 2)) ∧
      ∀ p : (Fin r → ℝ) × (Fin c → ℝ),
        HasSum (fun m : Fin c → ℤ => Gm m p.1 * Complex.exp (2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * p.2 j : ℝ) : ℂ)))
          (G p)
```

### `MeasureTheory.exists_summable_forall_fourierMode_normSqLogGerm_mul_productPoisson_of_contDiff_of_periodic`

`Thm_MeasureTheory_exists_summable_forall_fourierMode_normSqLogGerm_mul_productPoisson_of_contDiff_of_periodic` — Summable Fourier modes of a logarithmic complex-place germ window

```lean
theorem MeasureTheory.exists_summable_forall_fourierMode_normSqLogGerm_mul_productPoisson_of_contDiff_of_periodic
    {r c : ℕ} (W : (Fin r → ℝ) × (Fin c → ℝ) → ℂ) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (R : ℝ) (hR : 0 ≤ R) (hsupp : ∀ p : (Fin r → ℝ) × (Fin c → ℝ), (∃ k, R < |p.1 k|) → W p = 0)
    (hper : ∀ (p : (Fin r → ℝ) × (Fin c → ℝ)) (j : Fin c), W (p.1, p.2 + Pi.single j 1) = W p)
    (k : Fin r) (j : Fin c) :
    let Ψ : (Fin c → ℤ) → (Fin r → ℝ) → ℂ := fun m x =>
      ∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
        ((‖(1 : ℂ) - Complex.exp ((x k / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ j : ℝ))‖ ^ 2 *
              Real.log ‖(1 : ℂ) - Complex.exp ((x k / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ j : ℝ))‖ : ℝ) : ℂ) *
            W (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j', (m j' : ℝ) * θ j' : ℝ) : ℂ)))
    ∃ C : (Fin c → ℤ) → ℝ, (∀ m, 0 ≤ C m) ∧ Summable C ∧
      ∀ m : Fin c → ℤ, Continuous (Ψ m) ∧ Integrable (Ψ m) ∧
        (∀ x : Fin r → ℝ, ‖Ψ m x‖ ≤ C m * ∏ i, (1 + |x i|)⁻¹ ^ 2) ∧
        (∀ ξ : Fin r → ℝ,
          ‖∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, ξ i * x i : ℝ) : ℂ))) * Ψ m x‖ ≤
            C m * ∏ i, (1 + |ξ i|)⁻¹ ^ 2)
```

### `MeasureTheory.exists_summable_forall_norm_setIntegral_mul_cexp_le_prod_of_contDiff_of_periodic`

`Thm_MeasureTheory_exists_summable_forall_norm_setIntegral_mul_cexp_le_prod_of_contDiff_of_periodic` — Summable angular Fourier modes of a smooth periodic window

```lean
theorem MeasureTheory.exists_summable_forall_norm_setIntegral_mul_cexp_le_prod_of_contDiff_of_periodic
    {r c : ℕ} (W : (Fin r → ℝ) × (Fin c → ℝ) → ℂ) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (R : ℝ) (hR : 0 ≤ R) (hsupp : ∀ p : (Fin r → ℝ) × (Fin c → ℝ), (∃ k, R < |p.1 k|) → W p = 0)
    (hper : ∀ (p : (Fin r → ℝ) × (Fin c → ℝ)) (j : Fin c), W (p.1, p.2 + Pi.single j 1) = W p) :
    (∀ m : Fin c → ℤ,
      ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin r → ℝ =>
        ∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
          W (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))) ∧
      ∀ x : Fin r → ℝ, (∃ k, R < |x k|) →
        (∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
              W (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))) = 0) ∧
    ∃ C : (Fin c → ℤ) → ℝ, Summable C ∧ (∀ m, 0 ≤ C m) ∧
      (∀ (m : Fin c → ℤ) (x : Fin r → ℝ),
        ‖(∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
              W (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ))))‖ ≤ C m * ∏ k, (1 + |x k|)⁻¹ ^ 2) ∧
      (∀ (m : Fin c → ℤ) (ξ : Fin r → ℝ),
        ‖∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) *
            (∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
              W (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ))))‖ ≤
          C m * ∏ k, (1 + |ξ k|)⁻¹ ^ 2)
```

### `MeasureTheory.finiteDimensional_and_finrank_le_of_forall_norm_le_mul_eLpNorm_restrict`

`Thm_MeasureTheory_finiteDimensional_and_finrank_le_of_forall_norm_le_mul_eLpNorm_restrict` — Godement's finite-dimensionality lemma on a finite-measure window

```lean
theorem MeasureTheory.finiteDimensional_and_finrank_le_of_forall_norm_le_mul_eLpNorm_restrict
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (s : Set X) (hsm : MeasurableSet s) (hs : μ s ≠ ⊤)
    (V : Submodule ℂ (X → ℂ))
    (hmeas : ∀ φ ∈ V, AEStronglyMeasurable φ (μ.restrict s))
    (hinj : ∀ φ ∈ V, (∀ x ∈ s, φ x = 0) → φ = 0)
    (C : ℝ)
    (hsup : ∀ φ ∈ V, ∀ x ∈ s, ‖φ x‖ ≤ C * (eLpNorm φ 2 (μ.restrict s)).toReal) :
    FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℝ) ≤ C ^ 2 * (μ s).toReal
```

### `MeasureTheory.hasDerivAt_integral_prod_mk_of_contDiff_of_hasCompactSupport`

`Thm_MeasureTheory_hasDerivAt_integral_prod_mk_of_contDiff_of_hasCompactSupport` — Differentiation under the integral sign for smooth compactly supported kernels

```lean
theorem MeasureTheory.hasDerivAt_integral_prod_mk_of_contDiff_of_hasCompactSupport
    {n : ℕ} (Φ : ℝ × (Fin n → ℝ) → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => deriv (fun t : ℝ => Φ (t, p.2)) p.1) ∧
    HasCompactSupport (fun p : ℝ × (Fin n → ℝ) => deriv (fun t : ℝ => Φ (t, p.2)) p.1) ∧
    ∀ x : ℝ, HasDerivAt (fun x : ℝ => ∫ y : Fin n → ℝ, Φ (x, y))
      (∫ y : Fin n → ℝ, deriv (fun t : ℝ => Φ (t, y)) x) x
```

### `MeasureTheory.hasSum_fourierCoeff_pi_mul_cexp_of_continuous_of_periodic_of_summable`

`Thm_MeasureTheory_hasSum_fourierCoeff_pi_mul_cexp_of_continuous_of_periodic_of_summable` — Pointwise Fourier inversion on ℝᶜ for periodic continuous functions

```lean
theorem MeasureTheory.hasSum_fourierCoeff_pi_mul_cexp_of_continuous_of_periodic_of_summable
    {c : ℕ} (F : (Fin c → ℝ) → ℂ) (hF : Continuous F)
    (hper : ∀ (θ : Fin c → ℝ) (j : Fin c), F (θ + Pi.single j 1) = F θ)
    (hsum : Summable fun m : Fin c → ℤ =>
      ‖∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
          F θ * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))‖)
    (θ : Fin c → ℝ) :
    HasSum (fun m : Fin c → ℤ =>
      (∫ θ' in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
          F θ' * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ' j : ℝ) : ℂ)))) *
        Complex.exp (2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ))) (F θ)
```

### `MeasureTheory.hasSum_setIntegral_preimage_mul_zpow_of_integrable_mul_zpow`

`Thm_MeasureTheory_hasSum_setIntegral_preimage_mul_zpow_of_integrable_mul_zpow` — Shell decomposition of an integral with integer exponent

```lean
theorem MeasureTheory.hasSum_setIntegral_preimage_mul_zpow_of_integrable_mul_zpow
    {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω) (E : Ω → ℤ) (hE : Measurable E)
    (G : Ω → ℂ) {r : ℝ} (hr : 0 < r)
    (hG : Integrable (fun ω => G ω * (r : ℂ) ^ E ω) ρ) :
    HasSum (fun n : ℤ => (∫ ω in E ⁻¹' {n}, ‖G ω‖ ∂ρ) * r ^ n) (∫ ω, ‖G ω‖ * r ^ E ω ∂ρ) ∧
    (Summable fun n : ℤ => ‖∫ ω in E ⁻¹' {n}, G ω ∂ρ‖ * r ^ n) ∧
    ∀ Y : ℂ, ‖Y‖ = r →
      Integrable (fun ω => G ω * Y ^ E ω) ρ ∧
      HasSum (fun n : ℤ => (∫ ω in E ⁻¹' {n}, G ω ∂ρ) * Y ^ n) (∫ ω, G ω * Y ^ E ω ∂ρ)
```

### `MeasureTheory.hasSum_translate_intCast_fst_eq_tsum_integral_fourierIntegral_of_summable`

`Thm_MeasureTheory_hasSum_translate_intCast_fst_eq_tsum_integral_fourierIntegral_of_summable` — Partial Poisson summation in the first a variables

```lean
theorem MeasureTheory.hasSum_translate_intCast_fst_eq_tsum_integral_fourierIntegral_of_summable
    (a b : ℕ) (f : (Fin a → ℝ) × (Fin b → ℝ) → ℂ) (hfc : Continuous f) (hfi : Integrable f)
    (hloc : ∀ y : (Fin a → ℝ) × (Fin b → ℝ), ∃ V ∈ nhds y, ∃ M : (Fin a → ℤ) → ℝ, Summable M ∧
      ∀ y' ∈ V, ∀ k : Fin a → ℤ, ‖f (y' + (fun i => (k i : ℝ), 0))‖ ≤ M k)
    (fhat : (Fin a → ℤ) → (Fin b → ℝ) → ℂ)
    (hfhat : ∀ (κ : Fin a → ℤ) (η : Fin b → ℝ), fhat κ η =
      ∫ p : (Fin a → ℝ) × (Fin b → ℝ),
        Complex.exp (-(2 * Real.pi * Complex.I *
          ((∑ i, (κ i : ℝ) * p.1 i + ∑ j, η j * p.2 j : ℝ) : ℂ))) * f p)
    (hint : ∀ κ : Fin a → ℤ, Integrable (fhat κ))
    (hsum : Summable (fun κ : Fin a → ℤ => ∫ η, ‖fhat κ η‖)) :
    (∀ κ : Fin a → ℤ, Continuous (fhat κ)) ∧
    ∀ y : (Fin a → ℝ) × (Fin b → ℝ),
      Summable (fun k : Fin a → ℤ => ‖f (y + (fun i => (k i : ℝ), 0))‖) ∧
      HasSum (fun k : Fin a → ℤ => f (y + (fun i => (k i : ℝ), 0)))
        (∑' κ : Fin a → ℤ, ∫ η : Fin b → ℝ, fhat κ η *
          Complex.exp (2 * Real.pi * Complex.I *
            ((∑ i, (κ i : ℝ) * y.1 i + ∑ j, η j * y.2 j : ℝ) : ℂ)))
```

### `MeasureTheory.integrable_and_integral_mul_mul_eq_of_integral_subgroup_translate_eq_one_of_continuous`

`Thm_MeasureTheory_integrable_and_integral_mul_mul_eq_of_integral_subgroup_translate_eq_one_of_continuous` — Weighted T-invariant integrals are independent of the section function

```lean
theorem MeasureTheory.integrable_and_integral_mul_mul_eq_of_integral_subgroup_translate_eq_one_of_continuous
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (μ : Measure G) [μ.IsHaarMeasure] (τ : Measure T) [τ.IsHaarMeasure] [τ.IsInvInvariant]
    (F : G → ℂ) (hFm : Measurable F) (hFb : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C)
    (hFT : ∀ (t : T) (x : G), F ((t : G) * x) = F x)
    (W : G → ℝ) (hWc : Continuous W) (hWT : ∀ (t : T) (x : G), W ((t : G) * x) = W x)
    (w₁ w₂ : G → ℝ)
    (hw₁ : (∀ x, 0 ≤ w₁ x) ∧ Measurable w₁ ∧ HasCompactSupport w₁ ∧
      ∀ x, F x ≠ 0 → ∫ t : T, w₁ ((t : G) * x) ∂τ = 1)
    (hw₂ : (∀ x, 0 ≤ w₂ x) ∧ Measurable w₂ ∧ HasCompactSupport w₂ ∧
      ∀ x, F x ≠ 0 → ∫ t : T, w₂ ((t : G) * x) ∂τ = 1) :
    Integrable (fun x => F x * (W x : ℂ) * (w₁ x : ℂ)) μ ∧
      ∫ x, F x * (W x : ℂ) * (w₁ x : ℂ) ∂μ = ∫ x, F x * (W x : ℂ) * (w₂ x : ℂ) ∂μ
```

### `MeasureTheory.integrable_and_integral_withDensity_eq_of_forall_lintegral_subgroup_mul_eq_one`

`Thm_MeasureTheory_integrable_and_integral_withDensity_eq_of_forall_lintegral_subgroup_mul_eq_one` — Independence of int f d(ρμ) from the normalised density ρ

```lean
theorem MeasureTheory.integrable_and_integral_withDensity_eq_of_forall_lintegral_subgroup_mul_eq_one
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (H : Subgroup G) (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ] (μH : Measure H) [SFinite μH]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hinv : ∀ f : H → ℝ≥0∞, ∫⁻ n, f n⁻¹ ∂μH = ∫⁻ n, f n ∂μH)
    {ρ ρ' : G → ℝ≥0∞} (hρ : Measurable ρ) (hρ' : Measurable ρ')
    (hρ1 : ∀ g, ∫⁻ n : H, ρ ((n : G) * g) ∂μH = 1) (hρ'1 : ∀ g, ∫⁻ n : H, ρ' ((n : G) * g) ∂μH = 1)
    (hρt : ∀ g, ρ g ≠ ∞) (hρ't : ∀ g, ρ' g ≠ ∞)
    {f : G → E} (hfinv : ∀ (n : H) (g : G), f ((n : G) * g) = f g)
    (hfi : Integrable f (μ.withDensity ρ)) :
    Integrable f (μ.withDensity ρ') ∧
      ∫ g, f g ∂μ.withDensity ρ' = ∫ g, f g ∂μ.withDensity ρ
```

### `MeasureTheory.integrable_mul_comp_neg_div_div_of_integrable_prod_Iio_prod_Ioi`

`Thm_MeasureTheory_integrable_mul_comp_neg_div_div_of_integrable_prod_Iio_prod_Ioi` — Integrability transfers under the substitution (u,v)↦(-u/t, u/v)

```lean
theorem MeasureTheory.integrable_mul_comp_neg_div_div_of_integrable_prod_Iio_prod_Ioi
    (F : ℝ × ℝ × ℝ → ℂ) (hFm : Measurable F)
    (hF : Integrable F ((volume.restrict (Ioi (0 : ℝ))).prod
      ((volume.restrict (Iio (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))))) :
    Integrable (fun p : ℝ × ℝ × ℝ =>
        ((p.2.1 / (p.1 * p.2.2 ^ 2) : ℝ) : ℂ) * F (p.1, -(p.2.1 / p.1), p.2.1 / p.2.2))
      ((volume.restrict (Ioi (0 : ℝ))).prod
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))))
```

### `MeasureTheory.integrable_mul_of_integral_subgroup_translate_eq_one`

`Thm_MeasureTheory_integrable_mul_of_integral_subgroup_translate_eq_one` — Integrability of a bounded T-invariant function times a cut-off

```lean
theorem MeasureTheory.integrable_mul_of_integral_subgroup_translate_eq_one
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (μ : Measure G) [μ.IsHaarMeasure] (τ : Measure T) [τ.IsHaarMeasure] [τ.IsInvInvariant]
    (F : G → ℂ) (hFm : Measurable F) (hFb : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C)
    (hFT : ∀ (t : T) (x : G), F ((t : G) * x) = F x)
    (w : G → ℝ)
    (hw : (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧
      ∀ x, F x ≠ 0 → ∫ t : T, w ((t : G) * x) ∂τ = 1) :
    Integrable (fun x => F x * (w x : ℂ)) μ
```

### `MeasureTheory.integrable_norm_sq_sum_conj_smul_and_integral_eq_sum_mul_norm_sq_of_forall_integral_mul_conj_eq`

`Thm_MeasureTheory_integrable_norm_sq_sum_conj_smul_and_integral_eq_sum_mul_norm_sq_of_forall_integral_mul_conj_eq` — Finite Parseval identity for vector-valued L² expansions

```lean
theorem MeasureTheory.integrable_norm_sq_sum_conj_smul_and_integral_eq_sum_mul_norm_sq_of_forall_integral_mul_conj_eq
    {X : Type*} [MeasurableSpace X] (ρ : Measure X)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {J : Type*} [Fintype J] [DecidableEq J]
    (φ : J → X → ℂ) (hφ : ∀ j, MemLp (φ j) 2 ρ) (v : J → E) (s : J → ℝ)
    (horth : ∀ j j', ∫ x, φ j x * conj (φ j' x) ∂ρ = if j = j' then ((s j : ℝ) : ℂ) else 0) :
    Integrable (fun x => ‖∑ j, conj (φ j x) • v j‖ ^ 2) ρ ∧
      ∫ x, ‖∑ j, conj (φ j x) • v j‖ ^ 2 ∂ρ = ∑ j, s j * ‖v j‖ ^ 2
```

### `MeasureTheory.integral_abs_det_div_sq_mul_comp_moebius_real`

`Thm_MeasureTheory_integral_abs_det_div_sq_mul_comp_moebius_real` — Möbius change of variables on ℝ

```lean
theorem MeasureTheory.integral_abs_det_div_sq_mul_comp_moebius_real
    (a b c d : ℝ) (_hdet : a * d - b * c ≠ 0) (G : ℝ → ℂ) :
    ∫ x : ℝ, ((|a * d - b * c| / (a + x * c) ^ 2 : ℝ) : ℂ) * G ((b + x * d) / (a + x * c))
      = ∫ u : ℝ, G u
```

### `MeasureTheory.integral_integral_integral_comm_of_integrable_prod_prod`

`Thm_MeasureTheory_integral_integral_integral_comm_of_integrable_prod_prod` — Reversal of a triple iterated Bochner integral

```lean
theorem MeasureTheory.integral_integral_integral_comm_of_integrable_prod_prod
    {X Y Z E : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (ν : Measure Y) (ρ : Measure Z) [SFinite μ] [SFinite ν] [SFinite ρ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : X × Y × Z → E) (hf : Integrable f (μ.prod (ν.prod ρ))) :
    ∫ x, ∫ y, ∫ z, f (x, y, z) ∂ρ ∂ν ∂μ = ∫ z, ∫ y, ∫ x, f (x, y, z) ∂μ ∂ν ∂ρ
```

### `MeasureTheory.integral_mul_eq_integral_integral_subgroup_mul_mul_of_forall_integral_translate_eq_one`

`Thm_MeasureTheory_integral_mul_eq_integral_integral_subgroup_mul_mul_of_forall_integral_translate_eq_one` — Unfolding Sbackslash G through Tbackslash G with section functions

```lean
theorem MeasureTheory.integral_mul_eq_integral_integral_subgroup_mul_mul_of_forall_integral_translate_eq_one
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (S : Subgroup G) (hS : IsClosed (S : Set G)) (hST : S ≤ T) [MeasurableSpace S] [BorelSpace S]
    (μ : Measure G) [μ.IsHaarMeasure]
    (τ : Measure T) [τ.IsHaarMeasure] [τ.IsInvInvariant]
    (τS : Measure S) [τS.IsHaarMeasure] [τS.IsInvInvariant]
    (F : G → ℂ) (hFm : Measurable F) (hFb : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C)
    (hFS : ∀ (s : S) (x : G), F ((s : G) * x) = F x)
    (wS : G → ℝ) (hwS0 : ∀ x, 0 ≤ wS x) (hwSm : Measurable wS) (hwSc : HasCompactSupport wS)
    (hwS1 : ∀ x : G, F x ≠ 0 → ∫ s : S, wS ((s : G) * x) ∂τS = 1)
    (β : T → ℝ) (hβ0 : ∀ t, 0 ≤ β t) (hβm : Measurable β) (hβc : HasCompactSupport β)
    (hβ1 : ∀ t : T, ∫ s : S, β (⟨(s : G), hST s.2⟩ * t) ∂τS = 1)
    (W : G → ℝ) (hW0 : ∀ x, 0 ≤ W x) (hWm : Measurable W) (hWc : HasCompactSupport W)
    (hW1 : ∀ x : G, F x ≠ 0 → ∫ t : T, W ((t : G) * x) ∂τ = 1) :
    ∫ x, F x * (wS x : ℂ) ∂μ = ∫ x, (∫ t : T, F ((t : G) * x) * (β t : ℂ) ∂τ) * (W x : ℂ) ∂μ
```

### `MeasureTheory.integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one`

`Thm_MeasureTheory_integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one` — Independence of weighted integrals from the choice of cut-off function

```lean
theorem MeasureTheory.integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (μ : Measure G) [μ.IsHaarMeasure] (τ : Measure T) [τ.IsHaarMeasure] [τ.IsInvInvariant]
    (F : G → ℂ) (hFm : Measurable F) (hFb : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C)
    (hFT : ∀ (t : T) (x : G), F ((t : G) * x) = F x)
    (w₁ w₂ : G → ℝ)
    (hw₁ : (∀ x, 0 ≤ w₁ x) ∧ Measurable w₁ ∧ HasCompactSupport w₁ ∧
      ∀ x, F x ≠ 0 → ∫ t : T, w₁ ((t : G) * x) ∂τ = 1)
    (hw₂ : (∀ x, 0 ≤ w₂ x) ∧ Measurable w₂ ∧ HasCompactSupport w₂ ∧
      ∀ x, F x ≠ 0 → ∫ t : T, w₂ ((t : G) * x) ∂τ = 1) :
    ∫ x, F x * (w₁ x : ℂ) ∂μ = ∫ x, F x * (w₂ x : ℂ) ∂μ
```

### `MeasureTheory.integral_normSq_det_div_mul_comp_moebius_complex`

`Thm_MeasureTheory_integral_normSq_det_div_mul_comp_moebius_complex` — Möbius change of variables on ℂ

```lean
theorem MeasureTheory.integral_normSq_det_div_mul_comp_moebius_complex
    (a b c d : ℂ) (_hdet : a * d - b * c ≠ 0) (G : ℂ → ℂ) :
    ∫ z : ℂ, ((‖a * d - b * c‖ ^ 2 / ‖a + z * c‖ ^ 4 : ℝ) : ℂ) * G ((b + z * d) / (a + z * c))
      = ∫ u : ℂ, G u
```

### `MeasureTheory.integral_norm_sq_axis_sub_le_of_analyticOnNhd_of_forall_integral_norm_sq_deriv_le`

`Thm_MeasureTheory_integral_norm_sq_axis_sub_le_of_analyticOnNhd_of_forall_integral_norm_sq_deriv_le` — L² mean value inequality along the imaginary axis

```lean
theorem MeasureTheory.integral_norm_sq_axis_sub_le_of_analyticOnNhd_of_forall_integral_norm_sq_deriv_le
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (O : Set ℂ) (hO : IsOpen O) (hO₀ : {s : ℂ | s.re = 0} ⊆ O)
    (N : ℂ → X → ℂ) (hNa : ∀ x : X, AnalyticOnNhd ℂ (fun s => N s x) O)
    (hNc : ContinuousOn (fun p : ℂ × X => N p.1 p.2) (O ×ˢ Set.univ))
    (t t' B : ℝ)
    (hB : ∀ τ ∈ Set.uIcc t t',
      ∫ x, ‖deriv (fun s : ℂ => N s x) ((τ : ℂ) * Complex.I)‖ ^ 2 ∂μ ≤ B ^ 2) :
    ∫ x, ‖N ((t : ℂ) * Complex.I) x - N ((t' : ℂ) * Complex.I) x‖ ^ 2 ∂μ ≤ (B * |t - t'|) ^ 2
```

### `MeasureTheory.integral_tsum_integral_eq_tsum_integral_integral_of_summable_integral_norm`

`Thm_MeasureTheory_integral_tsum_integral_eq_tsum_integral_integral_of_summable_integral_norm` — Countable sums through iterated integrals, L¹-summable case

```lean
theorem MeasureTheory.integral_tsum_integral_eq_tsum_integral_integral_of_summable_integral_norm
    {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] [Countable ι]
    (H : ι → X × Y → ℂ) (hH : ∀ i, Integrable (H i) (μ.prod ν))
    (hS : Summable fun i => ∫ p, ‖H i p‖ ∂(μ.prod ν)) :
    (∀ i, Integrable (fun x => ∫ y, H i (x, y) ∂ν) μ) ∧
    (∀ i, Integrable (fun y => ∫ x, H i (x, y) ∂μ) ν) ∧
    (Summable fun i => ∫ x, ‖∫ y, H i (x, y) ∂ν‖ ∂μ) ∧
    (Summable fun i => ∫ y, ‖∫ x, H i (x, y) ∂μ‖ ∂ν) ∧
    Integrable (fun y => ∑' i, ∫ x, H i (x, y) ∂μ) ν ∧
    ∫ y, ∑' i, ∫ x, H i (x, y) ∂μ ∂ν = ∑' i, ∫ x, ∫ y, H i (x, y) ∂ν ∂μ
```

### `MeasureTheory.lintegral_enorm_mul_eq_and_integral_mul_eq_of_forall_lintegral_comp_smul_eq_one`

`Thm_MeasureTheory_lintegral_enorm_mul_eq_and_integral_mul_eq_of_forall_lintegral_comp_smul_eq_one` — Independence of orbit integrals from the section function

```lean
theorem MeasureTheory.lintegral_enorm_mul_eq_and_integral_mul_eq_of_forall_lintegral_comp_smul_eq_one
    {A X : Type*} [Group A] [MulAction A X] [MeasurableSpace A] [MeasurableInv A] [MeasurableSpace X]
    (hact : Measurable fun z : A × X => z.1 • z.2)
    (τ : Measure A) [SFinite τ] [τ.IsInvInvariant]
    (ρ : Measure X) [SFinite ρ] (hρ : ∀ a : A, MeasurePreserving (fun x : X => a • x) ρ ρ)
    (h : X → ℂ) (hh : Measurable h) (hhA : ∀ (a : A) (x : X), h (a • x) = h x)
    (w₁ w₂ : X → ℝ) (hw₁ : Measurable w₁) (hw₂ : Measurable w₂) (hw₁0 : ∀ x, 0 ≤ w₁ x) (hw₂0 : ∀ x, 0 ≤ w₂ x)
    (hs₁ : ∀ x, h x ≠ 0 → ∫⁻ a, ENNReal.ofReal (w₁ (a • x)) ∂τ = 1)
    (hs₂ : ∀ x, h x ≠ 0 → ∫⁻ a, ENNReal.ofReal (w₂ (a • x)) ∂τ = 1) :
    ∫⁻ x, ‖h x‖ₑ * ENNReal.ofReal (w₁ x) ∂ρ = ∫⁻ x, ‖h x‖ₑ * ENNReal.ofReal (w₂ x) ∂ρ ∧
      (Integrable (fun x => h x * (w₁ x : ℂ)) ρ →
        Integrable (fun x => h x * (w₂ x : ℂ)) ρ ∧
          ∫ x, h x * (w₁ x : ℂ) ∂ρ = ∫ x, h x * (w₂ x : ℂ) ∂ρ)
```

### `MeasureTheory.lintegral_enorm_sub_integral_mul_sq_le_lintegral_mul_lintegral_enorm_sub_sq`

`Thm_MeasureTheory_lintegral_enorm_sub_integral_mul_sq_le_lintegral_mul_lintegral_enorm_sub_sq` — Jensen-type L² bound for averages against a probability density

```lean
theorem MeasureTheory.lintegral_enorm_sub_integral_mul_sq_le_lintegral_mul_lintegral_enorm_sub_sq
    {X A : Type*} [MeasurableSpace X] [MeasurableSpace A] (ν : Measure X) (ρ : Measure A) [SFinite ν] [SFinite ρ]
    (p : A → ℝ) (hp : Measurable p) (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∫ a, p a ∂ρ = 1)
    (u : X → ℂ) (hu : Measurable u) (U : X → A → ℂ) (hU : Measurable (Function.uncurry U))
    (hint : ∀ x, Integrable (fun a => U x a * (p a : ℂ)) ρ) :
    ∫⁻ x, ‖u x - ∫ a, U x a * (p a : ℂ) ∂ρ‖ₑ ^ 2 ∂ν
      ≤ ∫⁻ a, ENNReal.ofReal (p a) * ∫⁻ x, ‖u x - U x a‖ₑ ^ 2 ∂ν ∂ρ
```

### `MeasureTheory.lintegral_inv_sq_quadForm_shell_eq`

`Thm_MeasureTheory_lintegral_inv_sq_quadForm_shell_eq` — Mass of an indefinite quadratic shell in ℝ⁴

```lean
theorem MeasureTheory.lintegral_inv_sq_quadForm_shell_eq
    (c : ℝ) (hc : c < 0) :
    ∫⁻ a in {a : Fin 4 → ℝ | a 0 ^ 2 + a 1 ^ 2 - c * (a 2 ^ 2 + a 3 ^ 2) ∈ Set.Icc (1 : ℝ) (Real.exp 2)},
        (ENNReal.ofReal ((a 0 ^ 2 + a 1 ^ 2 - c * (a 2 ^ 2 + a 3 ^ 2)) ^ 2))⁻¹ =
      ENNReal.ofReal (2 * Real.pi ^ 2 / |c|)
```

### `MeasureTheory.lintegral_mul_comp_eq_tsum_zpow_mul_setLIntegral_of_measure_image_eq_mul`

`Thm_MeasureTheory_lintegral_mul_comp_eq_tsum_zpow_mul_setLIntegral_of_measure_image_eq_mul` — Peeling a geometric shell index off a lower Lebesgue integral

```lean
theorem MeasureTheory.lintegral_mul_comp_eq_tsum_zpow_mul_setLIntegral_of_measure_image_eq_mul
    {Q : Type*} [MeasurableSpace Q] (ν : Measure Q) (T : Q ≃ᵐ Q)
    (κ : ℝ≥0∞) (hκ₀ : κ ≠ 0) (hκ : κ ≠ ∞)
    (hT : ∀ s : Set Q, MeasurableSet s → ν (T '' s) = κ * ν s)
    (m : Q → ℤ) (hm : Measurable m) (hmT : ∀ q, m (T q) = m q + 1)
    (h : Q → ℝ≥0∞) (hh : Measurable h) (hhT : ∀ q, h (T q) = h q)
    (Φ : ℤ → ℝ≥0∞) :
    ∫⁻ q, h q * Φ (m q) ∂ν = (∑' n : ℤ, κ ^ n * Φ n) * ∫⁻ q in {q | m q = 0}, h q ∂ν
```

### `MeasureTheory.lintegral_mul_eq_lintegral_mul_of_forall_lintegral_subgroup_mul_eq_one`

`Thm_MeasureTheory_lintegral_mul_eq_lintegral_mul_of_forall_lintegral_subgroup_mul_eq_one` — Independence of the normalising density for H-invariant integrands

```lean
theorem MeasureTheory.lintegral_mul_eq_lintegral_mul_of_forall_lintegral_subgroup_mul_eq_one
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (H : Subgroup G) (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ] (μH : Measure H) [SFinite μH]
    (hinv : ∀ f : H → ℝ≥0∞, ∫⁻ n, f n⁻¹ ∂μH = ∫⁻ n, f n ∂μH)
    {ρ ρ' : G → ℝ≥0∞} (hρ : Measurable ρ) (hρ' : Measurable ρ')
    (hρ1 : ∀ g, ∫⁻ n : H, ρ ((n : G) * g) ∂μH = 1) (hρ'1 : ∀ g, ∫⁻ n : H, ρ' ((n : G) * g) ∂μH = 1)
    {φ : G → ℝ≥0∞} (hφ : AEMeasurable φ μ) (hφinv : ∀ (n : H) (g : G), φ ((n : G) * g) = φ g) :
    ∫⁻ g, φ g * ρ g ∂μ = ∫⁻ g, φ g * ρ' g ∂μ
```

### `MeasureTheory.lintegral_mul_eq_lintegral_mul_of_forall_mul_eq_of_ae_lintegral_comp_mul_eq_one`

`Thm_MeasureTheory_lintegral_mul_eq_lintegral_mul_of_forall_mul_eq_of_ae_lintegral_comp_mul_eq_one` — Independence of the weight function in Weil's integration formula

```lean
theorem MeasureTheory.lintegral_mul_eq_lintegral_mul_of_forall_mul_eq_of_ae_lintegral_comp_mul_eq_one
    {G X : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    [AddGroup X] [MeasurableSpace X] [MeasurableNeg X]
    (τ : Measure G) [SFinite τ] [τ.IsMulRightInvariant]
    (μ : Measure X) [SFinite μ] [μ.IsNegInvariant]
    (n : X → G) (hn : Measurable n) (hn_add : ∀ x y, n (x + y) = n x * n y)
    (Φ : G → ℝ≥0∞) (hΦ : Measurable Φ) (hΦn : ∀ g x, Φ (g * n x) = Φ g)
    (w w₀ : G → ℝ≥0∞) (hw : Measurable w) (hw₀ : Measurable w₀)
    (h1 : ∀ᵐ g ∂τ, ∫⁻ x, w (g * n x) ∂μ = 1) (h1₀ : ∀ᵐ g ∂τ, ∫⁻ x, w₀ (g * n x) ∂μ = 1) :
    ∫⁻ g, w g * Φ g ∂τ = ∫⁻ g, w₀ g * Φ g ∂τ
```

### `MeasureTheory.measure_biUnion_finset_image_mul_right_lt_top`

`Thm_MeasureTheory_measure_biUnion_finset_image_mul_right_lt_top` — Finite unions of right translates have finite measure

```lean
theorem MeasureTheory.measure_biUnion_finset_image_mul_right_lt_top
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulRightInvariant]
    (s : Set G) (hs : μ s < ⊤) (T : Finset G) :
    μ (⋃ x ∈ T, (· * x) '' s) < ⊤
```

### `MeasureTheory.measure_setOf_exists_mem_le_mul_of_forall_closedBall`

`Thm_MeasureTheory_measure_setOf_exists_mem_le_mul_of_forall_closedBall` — Besicovitch propagation of a hitting bound from small balls

```lean
theorem MeasureTheory.measure_setOf_exists_mem_le_mul_of_forall_closedBall
    {α β : Type*} [MetricSpace α] [SecondCountableTopology α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [HasBesicovitchCovering α] {_ : MeasurableSpace β} (μ : Measure β) (ν : Measure α) [SFinite ν]
    [ν.OuterRegular] (P : β → α → Prop) (S : Set α) (K : ℝ≥0∞) (hK : K ≠ ⊤)
    (h : ∀ x ∈ S, ∃ δ > 0, ∀ ρ ∈ Set.Ioo 0 δ,
      μ {b | ∃ y ∈ Metric.closedBall x ρ, P b y} ≤ K * ν (Metric.closedBall x ρ)) :
    μ {b | ∃ x ∈ S, P b x} ≤ K * ν S
```

### `MeasureTheory.memLp_two_and_integral_sum_norm_sq_sub_le_mul_add_of_eq_mul_add_sum_conj_mul_of_bessel`

`Thm_MeasureTheory_memLp_two_and_integral_sum_norm_sq_sub_le_mul_add_of_eq_mul_add_sum_conj_mul_of_bessel` — L² error bound under a shifted Bessel-bounded mixing matrix

```lean
theorem MeasureTheory.memLp_two_and_integral_sum_norm_sq_sub_le_mul_add_of_eq_mul_add_sum_conj_mul_of_bessel
    {n m : ℕ} (κ τ₁ τ₂ : ℝ)
    (T F d : Fin n → ℝ → ℂ) (d' : Fin m → ℝ → ℂ) (B : Fin n → Fin m → ℝ → ℂ)
    (_hd : ∀ j, MemLp (d j) 2) (_hd' : ∀ j', MemLp (d' j') 2)
    (_hTF : ∀ j, AEStronglyMeasurable (fun t => T j t - F j t))
    (_hB : ∀ (t : ℝ) (x : Fin m → ℂ),
      ∑ j : Fin n, ‖∑ j' : Fin m, conj (B j j' t) * x j'‖ ^ 2 ≤ ∑ j' : Fin m, ‖x j'‖ ^ 2)
    (_heq : ∀ (j : Fin n) (t : ℝ),
      T j (t + τ₁) - F j (t + τ₁) = (κ : ℂ) * (d j (t + τ₁) + ∑ j' : Fin m, conj (B j j' t) * d' j' (-t + τ₂))) :
    (∀ j : Fin n, MemLp (fun t => F j t - T j t) 2) ∧
    ∫ t : ℝ, ∑ j : Fin n, ‖F j t - T j t‖ ^ 2 ≤
      2 * κ ^ 2 * ((∑ j : Fin n, ∫ t : ℝ, ‖d j t‖ ^ 2) + ∑ j' : Fin m, ∫ t : ℝ, ‖d' j' t‖ ^ 2)
```

### `MeasureTheory.memLp_two_and_sum_integral_norm_sq_le_of_forall_norm_sum_integral_conj_scaledKernelAverage_mul_le`

`Thm_MeasureTheory_memLp_two_and_sum_integral_norm_sq_le_of_forall_norm_sum_integral_conj_scaledKernelAverage_mul_le` — L² bound for a polynomially bounded family from kernel-averaged pairings

```lean
theorem MeasureTheory.memLp_two_and_sum_integral_norm_sq_le_of_forall_norm_sum_integral_conj_scaledKernelAverage_mul_le
    {ι : Type} [Fintype ι] (Θ : ι → ℝ → ℂ) (hΘ : ∀ i, Continuous (Θ i))
    (hΘg : ∀ i, ∃ (A : ℝ) (k : ℕ), ∀ t, ‖Θ i t‖ ≤ A * (1 + |t|) ^ k)
    (ρ : ℝ → ℝ) (hρ : Measurable ρ) (hρm : ∀ n : ℕ, Integrable (fun t : ℝ => |t| ^ n * ρ t))
    (hρ1 : ∫ t : ℝ, ρ t = 1)
    (M : ℝ)
    (h : ∀ (u : ι → ℝ → ℂ), (∀ i, Measurable (u i)) →
      (∃ R : ℝ, ∀ i x, R < |x| → u i x = 0) → (∃ B : ℝ, ∀ i x, ‖u i x‖ ≤ B) →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ‖∑ i, ∫ t : ℝ, conj (∫ x : ℝ, u i x * ((δ⁻¹ * ρ ((t - x) / δ) : ℝ) : ℂ)) * Θ i t‖ ≤
        M * Real.sqrt (∑ i, ∫ t : ℝ, ‖∫ x : ℝ, u i x * ((δ⁻¹ * ρ ((t - x) / δ) : ℝ) : ℂ)‖ ^ 2)) :
    (∀ i, MemLp (Θ i) 2) ∧ ∑ i, ∫ t : ℝ, ‖Θ i t‖ ^ 2 ≤ M ^ 2
```

### `MeasureTheory.memLp_two_integral_and_integral_norm_sq_integral_le_of_integral_norm_sq_le_of_integrable_one_add_sq_mul`

`Thm_MeasureTheory_memLp_two_integral_and_integral_norm_sq_integral_le_of_integral_norm_sq_le_of_integrable_one_add_sq_mul` — Weighted L² bound for a parametric integral

```lean
theorem MeasureTheory.memLp_two_integral_and_integral_norm_sq_integral_le_of_integral_norm_sq_le_of_integrable_one_add_sq_mul
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    (G : ℝ × X → ℂ) (_hG : AEStronglyMeasurable G ((volume : Measure ℝ).prod μ))
    (M : ℝ → ℝ) (_hM0 : ∀ t, 0 ≤ M t)
    (_hGt : ∀ t : ℝ, MemLp (fun x => G (t, x)) 2 μ ∧ (∫ x, ‖G (t, x)‖ ^ 2 ∂μ) ≤ M t)
    (_hM : Integrable (fun t : ℝ => (1 + t ^ 2) * M t)) :
    MemLp (fun x => ∫ t : ℝ, G (t, x)) 2 μ ∧
    (∫ x, ‖∫ t : ℝ, G (t, x)‖ ^ 2 ∂μ) ≤ Real.pi * ∫ t : ℝ, (1 + t ^ 2) * M t
```

### `MeasureTheory.norm_integral_mul_cexp_le_two_pow_mul_rpow_neg_of_contDiff_of_hasCompactSupport`

`Thm_MeasureTheory_norm_integral_mul_cexp_le_two_pow_mul_rpow_neg_of_contDiff_of_hasCompactSupport` — Non-stationary phase bound for oscillatory integrals on ℝ

```lean
theorem MeasureTheory.norm_integral_mul_cexp_le_two_pow_mul_rpow_neg_of_contDiff_of_hasCompactSupport
    (N : ℕ) (H : ℝ → ℂ) (hH : ContDiff ℝ N H) (hHc : HasCompactSupport H) (l : ℝ) :
    ‖∫ u : ℝ, H u * Complex.exp (Complex.I * (l : ℂ) * (u : ℂ))‖
      ≤ 2 ^ N * ((∫ u : ℝ, ‖H u‖) + ∫ u : ℝ, ‖iteratedDeriv N H u‖) * (1 + |l|) ^ (-(N : ℝ))
```

### `MeasureTheory.norm_le_two_pow_mul_of_forall_norm_integral_cexp_mul_le_prod`

`Thm_MeasureTheory_norm_le_two_pow_mul_of_forall_norm_integral_cexp_mul_le_prod` — Sup bound from product decay of the Fourier transform

```lean
theorem MeasureTheory.norm_le_two_pow_mul_of_forall_norm_integral_cexp_mul_le_prod
    {r : ℕ} (f : (Fin r → ℝ) → ℂ) (hf : Continuous f) (hfi : Integrable f) (C : ℝ)
    (hC : ∀ ξ : Fin r → ℝ,
      ‖∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) * f x‖ ≤ C * ∏ k, (1 + |ξ k|)⁻¹ ^ 2)
    (x : Fin r → ℝ) :
    ‖f x‖ ≤ 2 ^ r * C
```

### `MeasureTheory.setIntegral_Iio_setIntegral_Ioi_eq_setIntegral_setIntegral_mul_comp_neg_div_div`

`Thm_MeasureTheory_setIntegral_Iio_setIntegral_Ioi_eq_setIntegral_setIntegral_mul_comp_neg_div_div` — Fibre substitution (y₁,y₂)=(-u/t, u/v) for iterated integrals

```lean
theorem MeasureTheory.setIntegral_Iio_setIntegral_Ioi_eq_setIntegral_setIntegral_mul_comp_neg_div_div
    (h : ℝ → ℝ → ℂ) (t : ℝ) (ht : 0 < t) :
    ∫ y₁ in Iio (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ), h y₁ y₂ =
      ∫ u in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ), ((u / (t * v ^ 2) : ℝ) : ℂ) * h (-(u / t)) (u / v)
```

### `MeasureTheory.setIntegral_Ioi_setIntegral_Ioi_eq_setIntegral_setIntegral_Ioi_div_wedgeSubst`

`Thm_MeasureTheory_setIntegral_Ioi_setIntegral_Ioi_eq_setIntegral_setIntegral_Ioi_div_wedgeSubst` — Wedge substitution t=u(σ-u), u=v/w for iterated integrals

```lean
theorem MeasureTheory.setIntegral_Ioi_setIntegral_Ioi_eq_setIntegral_setIntegral_Ioi_div_wedgeSubst
    (H : ℝ → ℝ → ℂ) (hHm : Measurable (Function.uncurry H))
    (hHi : Integrable (Function.uncurry H)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))))
    (v : ℝ) (hv : 0 < v) :
    ∫ u in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), H t u =
      ∫ σ in Ioi (0 : ℝ), ∫ w in Ioi (v / σ),
        ((v ^ 2 / w ^ 3 : ℝ) : ℂ) * H (v * (σ * w - v) / w ^ 2) (v / w)
```

### `MeasureTheory.setIntegral_exp_mul_le_exp_neg_mul_setIntegral_of_gap`

`Thm_MeasureTheory_setIntegral_exp_mul_le_exp_neg_mul_setIntegral_of_gap` — Laplace concentration: off-window tail bound from a gap

```lean
theorem MeasureTheory.setIntegral_exp_mul_le_exp_neg_mul_setIntegral_of_gap
    (φ : ℝ → ℝ) (hφm : Measurable φ) (hφmax : ∀ v, φ v ≤ φ 0)
    (γ δ ρ : ℝ) (hγ : 0 < γ) (hρ : 0 < ρ) (hρδ : ρ ≤ δ)
    (hout : ∀ v, δ < |v| → φ v ≤ φ 0 - γ) (hin : ∀ v, |v| ≤ ρ → φ 0 - γ / 2 ≤ φ v)
    (H : ℝ → ℝ) (Λ₀ : ℝ) (hΛ₀ : 0 ≤ Λ₀)
    (hHint : Integrable (fun v => Real.exp (Λ₀ * (φ v - φ 0 + γ)) * H v))
    (hHloc : IntegrableOn H {v | |v| ≤ δ})
    (h : ℝ → ℝ) (hhm : Measurable h) (hh0 : ∀ v, 0 ≤ h v) (hhH : ∀ v, h v ≤ H v)
    (cm : ℝ) (hhin : ∀ v, |v| ≤ ρ → Real.exp cm ≤ h v)
    (Λ : ℝ) (hΛ : Λ₀ ≤ Λ) :
    IntegrableOn (fun v => Real.exp (Λ * φ v) * h v) {v | δ < |v|} ∧
    IntegrableOn (fun v => Real.exp (Λ * φ v) * h v) {v | |v| ≤ δ} ∧
    ∫ v in {v | δ < |v|}, Real.exp (Λ * φ v) * h v ≤
      ((∫ v, Real.exp (Λ₀ * (φ v - φ 0 + γ)) * H v) * Real.exp (-cm) / (2 * ρ)) * Real.exp (-(Λ * γ / 2)) *
        ∫ v in {v | |v| ≤ δ}, Real.exp (Λ * φ v) * h v
```

### `MeasureTheory.setIntegral_iwasawaRegion_eq_two_pi_mul_of_theta_free`

`Thm_MeasureTheory_setIntegral_iwasawaRegion_eq_two_pi_mul_of_theta_free` — Integrating out θ over the Iwasawa region

```lean
theorem MeasureTheory.setIntegral_iwasawaRegion_eq_two_pi_mul_of_theta_free
    (F : ℝ × ℝ × ℝ × ℝ → ℂ) (G : ℝ → ℝ → ℝ → ℂ)
    (hFG : ∀ x y₁ y₂ θ : ℝ, y₁ ≠ 0 → 0 < y₂ → F (x, y₁, y₂, θ) = G x y₁ y₂)
    (hG : Integrable (fun q : ℝ × ℝ × ℝ => G q.1 q.2.1 q.2.2)
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))))) :
    ∫ p : ℝ × ℝ × ℝ × ℝ in Set.univ ×ˢ (Set.univ ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioc (0 : ℝ) (2 * Real.pi))), F p =
      ((2 * Real.pi : ℝ) : ℂ) * ∫ y₁ : ℝ, ∫ y₂ in Set.Ioi (0 : ℝ), ∫ x : ℝ, G x y₁ y₂
```

### `MeasureTheory.sq_norm_apply_mul_measureReal_le_finrank_mul_integral_sq_norm_of_forall_mul_right_mem`

`Thm_MeasureTheory_sq_norm_apply_mul_measureReal_le_finrank_mul_integral_sq_norm_of_forall_mul_right_mem` — Sup-L² bound for finite-dimensional translation-invariant spaces

```lean
theorem MeasureTheory.sq_norm_apply_mul_measureReal_le_finrank_mul_integral_sq_norm_of_forall_mul_right_mem
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (V : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ V]
    (hcont : ∀ f ∈ V, Continuous f)
    (hinv : ∀ f ∈ V, ∀ g : G, (fun x => f (x * g)) ∈ V) :
    ∀ f ∈ V, ∀ x : G,
      ‖f x‖ ^ 2 * μ.real Set.univ ≤ (Module.finrank ℂ V : ℝ) * ∫ y, ‖f y‖ ^ 2 ∂μ
```

### `MeasureTheory.sum_coeff_mul_setIntegral_preimage_eq_of_forall_integral_mul_zpow_mul_eval_eq`

`Thm_MeasureTheory_sum_coeff_mul_setIntegral_preimage_eq_of_forall_integral_mul_zpow_mul_eval_eq` — Laurent coefficients of a functional equation on an annulus

```lean
theorem MeasureTheory.sum_coeff_mul_setIntegral_preimage_eq_of_forall_integral_mul_zpow_mul_eval_eq
    {T : Type*} [MeasurableSpace T] (μ : Measure T) (d : T → ℤ) (hd : Measurable d)
    (g : T → ℂ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hg : ∀ Y : ℂ, a < ‖Y‖ → ‖Y‖ < b → Integrable (fun t => g t * Y ^ d t) μ)
    (Q P : Polynomial ℂ) (n : ℤ)
    (hfe : ∀ Y : ℂ, a < ‖Y‖ → ‖Y‖ < b →
      (∫ t, g t * Y ^ d t ∂μ) * Q.eval Y = P.eval Y * Y ^ n)
    (j : ℤ) :
    ∑ i ∈ Q.support, Q.coeff i * ∫ t in d ⁻¹' {j - (i : ℤ)}, g t ∂μ =
      if n ≤ j then P.coeff (j - n).toNat else 0
```

### `MeasureTheory.sum_norm_sq_integral_mul_conj_le_integral_norm_sq_of_orthonormal`

`Thm_MeasureTheory_sum_norm_sq_integral_mul_conj_le_integral_norm_sq_of_orthonormal` — Bessel's inequality for a finite orthonormal family

```lean
theorem MeasureTheory.sum_norm_sq_integral_mul_conj_le_integral_norm_sq_of_orthonormal
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {n : ℕ} (e : Fin n → X → ℂ)
    (hint : ∀ i j, Integrable (fun x => e i x * conj (e j x)) μ)
    (hon : ∀ i j, ∫ x, e i x * conj (e j x) ∂μ = if i = j then 1 else 0)
    (w : X → ℂ) (hw : Integrable (fun x => ‖w x‖ ^ 2) μ)
    (hwe : ∀ j, Integrable (fun x => w x * conj (e j x)) μ) :
    ∑ j, ‖∫ x, w x * conj (e j x) ∂μ‖ ^ 2 ≤ ∫ x, ‖w x‖ ^ 2 ∂μ
```

### `MeasureTheory.sum_norm_sq_sum_conj_integral_mul_conj_mul_le_sum_norm_sq_of_orthonormal`

`Thm_MeasureTheory_sum_norm_sq_sum_conj_integral_mul_conj_mul_le_sum_norm_sq_of_orthonormal` — Bessel's inequality between two finite orthonormal systems

```lean
theorem MeasureTheory.sum_norm_sq_sum_conj_integral_mul_conj_mul_le_sum_norm_sq_of_orthonormal
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {n m : ℕ}
    (e : Fin n → X → ℂ) (f : Fin m → X → ℂ)
    (_he : ∀ i, MemLp (e i) 2 μ) (_hf : ∀ j, MemLp (f j) 2 μ)
    (_heon : ∀ i i' : Fin n, ∫ x, e i x * conj (e i' x) ∂μ = if i = i' then 1 else 0)
    (_hfon : ∀ j j' : Fin m, ∫ x, f j x * conj (f j' x) ∂μ = if j = j' then 1 else 0)
    (x : Fin m → ℂ) :
    ∑ i : Fin n, ‖∑ j' : Fin m, conj (∫ y, e i y * conj (f j' y) ∂μ) * x j'‖ ^ 2 ≤ ∑ j' : Fin m, ‖x j'‖ ^ 2
```

### `MeasureTheory.tendsto_integral_mul_nhdsGT_of_tendstoUniformlyOn_tsupport`

`Thm_MeasureTheory_tendsto_integral_mul_nhdsGT_of_tendstoUniformlyOn_tsupport` — Dominated convergence for integrals against a compactly supported weight

```lean
theorem MeasureTheory.tendsto_integral_mul_nhdsGT_of_tendstoUniformlyOn_tsupport
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (w : X → ℝ) (hwm : Measurable w) (hwc : HasCompactSupport w) (hwb : ∃ B : ℝ, ∀ x, |w x| ≤ B)
    (Φ : ℝ → X → ℂ) (Φ₀ : X → ℂ)
    (hΦm : ∀ θ : ℝ, AEStronglyMeasurable (Φ θ) μ) (hΦ₀m : AEStronglyMeasurable Φ₀ μ)
    (hΦ₀b : ∃ B₀ : ℝ, ∀ x ∈ tsupport w, ‖Φ₀ x‖ ≤ B₀)
    (hunif : TendstoUniformlyOn Φ Φ₀ (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (tsupport w)) :
    Tendsto (fun θ : ℝ => ∫ x, Φ θ x * (w x : ℂ) ∂μ) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∫ x, Φ₀ x * (w x : ℂ) ∂μ))
```

### `MeasureTheory.tendsto_integral_sin_mul_div_mul_of_integrable_fourierIntegral`

`Thm_MeasureTheory_tendsto_integral_sin_mul_div_mul_of_integrable_fourierIntegral` — Dirichlet localisation: int h(t)sin(Rt)/t → π h(0)

```lean
theorem MeasureTheory.tendsto_integral_sin_mul_div_mul_of_integrable_fourierIntegral
    (h : ℝ → ℂ) (hh : MeasureTheory.Integrable h)
    (hFh : MeasureTheory.Integrable (𝓕 h)) (h0 : ContinuousAt h 0) :
    Filter.Tendsto (fun R : ℝ => ∫ t : ℝ, ((Real.sin (R * t) / t : ℝ) : ℂ) * h t)
      Filter.atTop (nhds ((Real.pi : ℂ) * h 0))
```

### `MeasureTheory.tendsto_lintegral_nhds_zero_of_le_of_limsup_lintegral_le`

`Thm_MeasureTheory_tendsto_lintegral_nhds_zero_of_le_of_limsup_lintegral_le` — Pratt's lemma for lower integrals with moving dominators

```lean
theorem MeasureTheory.tendsto_lintegral_nhds_zero_of_le_of_limsup_lintegral_le
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter ι} [l.IsCountablyGenerated]
    (F G : ι → α → ℝ≥0∞) (g : α → ℝ≥0∞)
    (hF : ∀ i, AEMeasurable (F i) μ) (hG : ∀ i, AEMeasurable (G i) μ)
    (hFG : ∀ i, ∀ᵐ x ∂μ, F i x ≤ G i x)
    (hF0 : ∀ᵐ x ∂μ, Tendsto (fun i => F i x) l (𝓝 0))
    (hGg : ∀ᵐ x ∂μ, Tendsto (fun i => G i x) l (𝓝 (g x)))
    (hg : ∫⁻ x, g x ∂μ ≠ ∞)
    (hlim : limsup (fun i => ∫⁻ x, G i x ∂μ) l ≤ ∫⁻ x, g x ∂μ) :
    Tendsto (fun i => ∫⁻ x, F i x ∂μ) l (𝓝 0)
```

### `MeasureTheory.volume_setOf_mvPolynomial_eval_eq_zero`

`Thm_MeasureTheory_volume_setOf_mvPolynomial_eval_eq_zero` — Zero sets of non-zero real polynomials are Lebesgue-null

```lean
theorem MeasureTheory.volume_setOf_mvPolynomial_eval_eq_zero
    {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (hp : p ≠ 0) :
    volume {x : Fin n → ℝ | MvPolynomial.eval x p = 0} = 0
```

## Matrix (96)

### `Matrix.GeneralLinearGroup.card_subgroup_dvd_sixteen_of_forall_det_of_card_le_fin_two_zmod_three`

`Thm_Matrix_GeneralLinearGroup_card_subgroup_dvd_sixteen_of_forall_det_of_card_le_fin_two_zmod_three` — Subgroups of GL₂(𝔽₃) of order ≤ 24 with full determinant

```lean
theorem Matrix.GeneralLinearGroup.card_subgroup_dvd_sixteen_of_forall_det_of_card_le_fin_two_zmod_three
    (H : Subgroup (GL (Fin 2) (ZMod 3)))
    (hirr : ¬ ∃ v : Fin 2 → ZMod 3, v ≠ 0 ∧ ∀ h ∈ H, ∃ c : ZMod 3,
      Matrix.mulVec (h : Matrix (Fin 2) (Fin 2) (ZMod 3)) v = c • v)
    (hdet : ∀ d : (ZMod 3)ˣ, ∃ h ∈ H, Matrix.GeneralLinearGroup.det h = d)
    (hle : Nat.card H ≤ 24) :
    Nat.card H ∣ 16
```

### `Matrix.GeneralLinearGroup.eq_one_of_isOfFinOrder_of_forall_sub_one_mem_of_ne`

`Thm_Matrix_GeneralLinearGroup_eq_one_of_isOfFinOrder_of_forall_sub_one_mem_of_ne` — Selberg's torsion-killing lemma: two primes force g=1

```lean
theorem Matrix.GeneralLinearGroup.eq_one_of_isOfFinOrder_of_forall_sub_one_mem_of_ne
    (A : Type) [CommRing A] [IsDomain A] [CharZero A]
    (𝔪₁ 𝔪₂ : Ideal A) (h𝔪₁ : 𝔪₁.IsMaximal) (h𝔪₂ : 𝔪₂.IsMaximal)
    (p₁ p₂ : ℕ) (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hne : p₁ ≠ p₂) (hp₁𝔪 : (p₁ : A) ∈ 𝔪₁) (hp₂𝔪 : (p₂ : A) ∈ 𝔪₂)
    (n : Type) [Fintype n] [DecidableEq n]
    (g : Matrix.GeneralLinearGroup n A) (hg : IsOfFinOrder g)
    (hg₁ : ∀ i j : n, (g : Matrix n n A) i j - (1 : Matrix n n A) i j ∈ 𝔪₁)
    (hg₂ : ∀ i j : n, (g : Matrix n n A) i j - (1 : Matrix n n A) i j ∈ 𝔪₂) :
    g = 1
```

### `Matrix.GeneralLinearGroup.exists_forall_inv_mul_apply_mem_and_mul_inv_apply_mem_of_forall_conj_apply_mem`

`Thm_Matrix_GeneralLinearGroup_exists_forall_inv_mul_apply_mem_and_mul_inv_apply_mem_of_forall_conj_apply_mem` — Conjugation-stable integral matrices force g ∈ K^× GLₙ(𝒪)

```lean
theorem Matrix.GeneralLinearGroup.exists_forall_inv_mul_apply_mem_and_mul_inv_apply_mem_of_forall_conj_apply_mem
    {K : Type*} [Field K] (𝒪 : ValuationSubring K) {n : Type*} [Fintype n] [DecidableEq n]
    (g : GL n K)
    (hg : ∀ M : Matrix n n K, (∀ i j, M i j ∈ 𝒪) →
      ∀ i j, ((g : Matrix n n K) * M * ((g⁻¹ : GL n K) : Matrix n n K)) i j ∈ 𝒪) :
    ∃ c : Kˣ, (∀ i j, ((c⁻¹ : Kˣ) : K) * (g : Matrix n n K) i j ∈ 𝒪) ∧
      (∀ i j, (c : K) * ((g⁻¹ : GL n K) : Matrix n n K) i j ∈ 𝒪)
```

### `Matrix.GeneralLinearGroup.exists_inv_mul_mem_iwahori_or_atkinLehner_inv_mul_mem_of_forall_conj_mem`

`Thm_Matrix_GeneralLinearGroup_exists_inv_mul_mem_iwahori_or_atkinLehner_inv_mul_mem_of_forall_conj_mem` — Semi-normaliser of the Iwahori order in GL₂(K)

```lean
theorem Matrix.GeneralLinearGroup.exists_inv_mul_mem_iwahori_or_atkinLehner_inv_mul_mem_of_forall_conj_mem
    {K : Type*} [Field K] (O : ValuationSubring K) (ϖ : K) (hϖO : ϖ ∈ O) (hϖ : ϖ ≠ 0)
    (g : GL (Fin 2) K)
    (hg : ∀ M : Matrix (Fin 2) (Fin 2) K, (∀ i j, M i j ∈ O) → ϖ⁻¹ * M 1 0 ∈ O →
      (∀ i j, ((g : Matrix (Fin 2) (Fin 2) K) * M * ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) i j ∈ O) ∧
        ϖ⁻¹ * ((g : Matrix (Fin 2) (Fin 2) K) * M * ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 1 0 ∈ O) :
    ∃ c : Kˣ,
      ((∀ i j, ((c⁻¹ : Kˣ) : K) * (g : Matrix (Fin 2) (Fin 2) K) i j ∈ O) ∧
        ϖ⁻¹ * (((c⁻¹ : Kˣ) : K) * (g : Matrix (Fin 2) (Fin 2) K) 1 0) ∈ O ∧
        (∀ i j, (c : K) * ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j ∈ O) ∧
        ϖ⁻¹ * ((c : K) * ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0) ∈ O) ∨
      ((∀ i j, ((!![0, ϖ⁻¹; 1, 0] : Matrix (Fin 2) (Fin 2) K) *
          (((c⁻¹ : Kˣ) : K) • (g : Matrix (Fin 2) (Fin 2) K))) i j ∈ O) ∧
        ϖ⁻¹ * ((!![0, ϖ⁻¹; 1, 0] : Matrix (Fin 2) (Fin 2) K) *
          (((c⁻¹ : Kˣ) : K) • (g : Matrix (Fin 2) (Fin 2) K))) 1 0 ∈ O ∧
        (∀ i j, (((c : K) • ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
          (!![0, 1; ϖ, 0] : Matrix (Fin 2) (Fin 2) K)) i j ∈ O) ∧
        ϖ⁻¹ * ((((c : K) • ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
          (!![0, 1; ϖ, 0] : Matrix (Fin 2) (Fin 2) K)) 1 0) ∈ O)
```

### `Matrix.GeneralLinearGroup.exists_isCompact_forall_conj_mem_of_conj_mul_self_mem_of_trace_ne_zero`

`Thm_Matrix_GeneralLinearGroup_exists_isCompact_forall_conj_mem_of_conj_mul_self_mem_of_trace_ne_zero` — Compact bound on conjugates of t from conjugates of t²

```lean
theorem Matrix.GeneralLinearGroup.exists_isCompact_forall_conj_mem_of_conj_mul_self_mem_of_trace_ne_zero
    {𝕜 : Type*} [RCLike 𝕜]
    (T : Set (GL (Fin 2) 𝕜)) (hT : IsCompact T)
    (hTtr : ∀ t ∈ T, Matrix.trace ((t : GL (Fin 2) 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜) ≠ 0)
    (B : Set (GL (Fin 2) 𝕜)) (hB : IsCompact B) :
    ∃ B' : Set (GL (Fin 2) 𝕜), IsCompact B' ∧
      ∀ t ∈ T, ∀ x : GL (Fin 2) 𝕜, x⁻¹ * (t * t) * x ∈ B → x⁻¹ * t * x ∈ B'
```

### `Matrix.GeneralLinearGroup.exists_isCompact_forall_exists_map_star_eq_and_eq_mul_of_inv_mul_map_star_mem`

`Thm_Matrix_GeneralLinearGroup_exists_isCompact_forall_exists_map_star_eq_and_eq_mul_of_inv_mul_map_star_mem` — Uniform Hilbert 90 for GL₂(ℂ)/GL₂(ℝ)

```lean
theorem Matrix.GeneralLinearGroup.exists_isCompact_forall_exists_map_star_eq_and_eq_mul_of_inv_mul_map_star_mem
    (B : Set (Matrix (Fin 2) (Fin 2) ℂ)) (hB : IsCompact B) :
    ∃ K : Set (GL (Fin 2) ℂ), IsCompact K ∧
      ∀ x : GL (Fin 2) ℂ,
        ((x⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * ((x : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ) ∈ B →
        ∃ m k : GL (Fin 2) ℂ,
          ((m : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ) = m ∧ k ∈ K ∧ x = m * k
```

### `Matrix.GeneralLinearGroup.exists_natCard_le_of_isSemisimpleRepresentation_of_card_image_charpoly_le`

`Thm_Matrix_GeneralLinearGroup_exists_natCard_le_of_isSemisimpleRepresentation_of_card_image_charpoly_le` — Deligne–Serre: uniform bound for few characteristic polynomials

```lean
theorem Matrix.GeneralLinearGroup.exists_natCard_le_of_isSemisimpleRepresentation_of_card_image_charpoly_le
    (η : ℝ) (hη : η < 1 / 2) (M : ℕ) :
    ∃ A : ℕ, ∀ (ℓ : ℕ) [Fact ℓ.Prime] (G : Subgroup (GL (Fin 2) (ZMod ℓ))),
      (Deformation.matrixRepresentation G.subtype).IsSemisimpleRepresentation →
      ∀ H : Finset (GL (Fin 2) (ZMod ℓ)), (↑H : Set (GL (Fin 2) (ZMod ℓ))) ⊆ G →
        (1 - η) * (Nat.card G : ℝ) ≤ H.card →
        (H.image fun h : GL (Fin 2) (ZMod ℓ) =>
            (h : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).charpoly).card ≤ M →
          Nat.card G ≤ A
```

### `Matrix.GeneralLinearGroup.exists_normal_relIndex_ne_zero_forall_isOfFinOrder_imp_eq_one_of_fg`

`Thm_Matrix_GeneralLinearGroup_exists_normal_relIndex_ne_zero_forall_isOfFinOrder_imp_eq_one_of_fg` — Selberg's lemma for finitely generated subgroups of GLₙ(K)

```lean
theorem Matrix.GeneralLinearGroup.exists_normal_relIndex_ne_zero_forall_isOfFinOrder_imp_eq_one_of_fg
    (K : Type) [Field K] [CharZero K] (n : Type) [Fintype n] [DecidableEq n]
    (Γ : Subgroup (Matrix.GeneralLinearGroup n K)) (hΓ : Γ.FG) :
    ∃ N : Subgroup (Matrix.GeneralLinearGroup n K), N ≤ Γ ∧ (N.subgroupOf Γ).Normal ∧ N.relIndex Γ ≠ 0 ∧
      ∀ g ∈ N, IsOfFinOrder g → g = 1
```

### `Matrix.GeneralLinearGroup.exists_subfield_specialLinearGroup_conj_le_of_dvd_card`

`Thm_Matrix_GeneralLinearGroup_exists_subfield_specialLinearGroup_conj_le_of_dvd_card` — Dickson's theorem for finite irreducible subgroups of GL₂

```lean
theorem Matrix.GeneralLinearGroup.exists_subfield_specialLinearGroup_conj_le_of_dvd_card
    {K : Type} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (H : Subgroup (GL (Fin 2) K)) [Finite H] (hdvd : p ∣ Nat.card H)
    (hirr : ∀ v : Fin 2 → K, v ≠ 0 →
      ∃ h ∈ H, ((h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v ∉ K ∙ v) :
    (p = 3 ∧ ¬ 9 ∣ Nat.card H) ∨
    ∃ (F : Subfield K) (_ : Finite F) (g : GL (Fin 2) K),
      (∀ s : SL(2, F),
        g * (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map F.subtype s)) * g⁻¹ ∈ H) ∧
      (∀ h ∈ H, ∃ (a : K) (m : GL (Fin 2) F),
        ((g⁻¹ * h * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
          a • ((Matrix.GeneralLinearGroup.map F.subtype m : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
```

### `Matrix.GeneralLinearGroup.isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two`

`Thm_Matrix_GeneralLinearGroup_isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two` — Unimodularity and inversion invariance of Haar measure on GL₂(F)

```lean
theorem Matrix.GeneralLinearGroup.isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two
    {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [LocallyCompactSpace (GL (Fin 2) F)] [SecondCountableTopology (GL (Fin 2) F)]
    [MeasurableSpace (GL (Fin 2) F)] [BorelSpace (GL (Fin 2) F)]
    (μ : Measure (GL (Fin 2) F)) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant ∧ μ.IsInvInvariant
```

### `Matrix.GeneralLinearGroup.isMulRightInvariant_of_isHaarMeasure_fin_two`

`Thm_Matrix_GeneralLinearGroup_isMulRightInvariant_of_isHaarMeasure_fin_two` — Haar measure on GL₂(F) is right invariant

```lean
theorem Matrix.GeneralLinearGroup.isMulRightInvariant_of_isHaarMeasure_fin_two
    {F : Type*} [Field F] [CharZero F] [TopologicalSpace F] [IsTopologicalRing F]
    [LocallyCompactSpace (GL (Fin 2) F)] [SecondCountableTopology (GL (Fin 2) F)]
    [MeasurableSpace (GL (Fin 2) F)] [BorelSpace (GL (Fin 2) F)]
    (μ : Measure (GL (Fin 2) F)) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant
```

### `Matrix.GeneralLinearGroup.modularCharacter_fin_two_eq_one`

`Thm_Matrix_GeneralLinearGroup_modularCharacter_fin_two_eq_one` — Unimodularity of GL₂(F): the modular character is trivial

```lean
theorem Matrix.GeneralLinearGroup.modularCharacter_fin_two_eq_one
    {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [LocallyCompactSpace (GL (Fin 2) F)] (g : GL (Fin 2) F) :
    MeasureTheory.Measure.modularCharacter g = 1
```

### `Matrix.GeneralLinearGroup.surjective_of_isUnipotent_of_forall_exists_mulVec_ne_smul_of_det_surjective`

`Thm_Matrix_GeneralLinearGroup_surjective_of_isUnipotent_of_forall_exists_mulVec_ne_smul_of_det_surjective` — Surjectivity of a GL₂(𝔽₃)-representation from unipotents and irreducibility

```lean
theorem Matrix.GeneralLinearGroup.surjective_of_isUnipotent_of_forall_exists_mulVec_ne_smul_of_det_surjective
    {G : Type*} [Group G] (ρ : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (hunip : ∃ σ : G,
      (((ρ σ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) - 1) ^ 2 = 0 ∧
        ((ρ σ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) ≠ 1)
    (hirr : ∀ v : Fin 2 → ZMod 3, v ≠ 0 → ∃ σ : G, ∀ c : ZMod 3,
      Matrix.mulVec ((ρ σ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) v
        ≠ c • v)
    (hdet : ∀ u : (ZMod 3)ˣ, ∃ σ : G, Matrix.GeneralLinearGroup.det (ρ σ) = u) :
    Function.Surjective ρ
```

### `Matrix.OrthogonalGroup.exists_polynomial_eq_of_continuous_of_rightFinite`

`Thm_Matrix_OrthogonalGroup_exists_polynomial_eq_of_continuous_of_rightFinite` — Right-finite continuous functions on O(2) are polynomials in the entries

```lean
theorem Matrix.OrthogonalGroup.exists_polynomial_eq_of_continuous_of_rightFinite
    (Φ : ↥(Matrix.orthogonalGroup (Fin 2) ℝ) → ℂ) (hc : Continuous Φ)
    (hfin : ∃ s : Finset (↥(Matrix.orthogonalGroup (Fin 2) ℝ) → ℂ),
      ∀ k : ↥(Matrix.orthogonalGroup (Fin 2) ℝ),
        (fun x => Φ (x * k)) ∈ Submodule.span ℂ (s : Set (↥(Matrix.orthogonalGroup (Fin 2) ℝ) → ℂ))) :
    ∃ F ∈ Submodule.span ℂ
        {F : Matrix (Fin 2) (Fin 2) ℝ → ℂ |
          ∃ l : List (Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] ℂ), F = fun m => (l.map (fun φ => φ m)).prod},
      ∀ k : ↥(Matrix.orthogonalGroup (Fin 2) ℝ), Φ k = F (k : Matrix (Fin 2) (Fin 2) ℝ)
```

### `Matrix.ProjGenLinGroup.exists_torsionFree_normal_subgroup_finiteIndex_of_fg_charZero`

`Thm_Matrix_ProjGenLinGroup_exists_torsionFree_normal_subgroup_finiteIndex_of_fg_charZero` — Selberg's lemma for PGLₙ in characteristic zero

```lean
theorem Matrix.ProjGenLinGroup.exists_torsionFree_normal_subgroup_finiteIndex_of_fg_charZero
    (K : Type) [Field K] [CharZero K] (n : Type) [Fintype n] [DecidableEq n]
    (Γ : Subgroup (Matrix.ProjGenLinGroup n K)) (hΓ : Γ.FG) :
    ∃ N : Subgroup (Matrix.ProjGenLinGroup n K), N ≤ Γ ∧ (N.subgroupOf Γ).Normal ∧ N.relIndex Γ ≠ 0 ∧
      ∀ g ∈ N, IsOfFinOrder g → g = 1
```

### `Matrix.SpecialLinearGroup.borel_orbit_structure_of_sylow_eq_upper`

`Thm_Matrix_SpecialLinearGroup_borel_orbit_structure_of_sylow_eq_upper` — Borel orbit structure for a finite subgroup of SL₂

```lean
theorem Matrix.SpecialLinearGroup.borel_orbit_structure_of_sylow_eq_upper
    {K : Type} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    {H : Type} [Group H] [Finite H] (ρ : H →* SL(2, K)) (hρ : Function.Injective ρ)
    (P : Sylow p H) (hP : ∀ x : H, x ∈ P ↔ ∃ t : K, ρ x = ModularCurve.upperElem t)
    (hne : ∃ a : K, a ≠ 0 ∧ ∃ u : H,
      ((ρ u : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![1, a; 0, 1]) :
    Nat.card (Subgroup.normalizer (P : Set H)) =
      Nat.card P * Nat.card (Set.range fun x : Subgroup.normalizer (P : Set H) =>
        ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0) ∧
    Nat.card (Set.range fun x : Subgroup.normalizer (P : Set H) =>
        ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0) =
      Nat.card {x : H // ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 ∨
          ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1} *
        Nat.card (Set.range fun x : Subgroup.normalizer (P : Set H) =>
          (((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0) ^ 2) ∧
    (Nat.card (Set.range fun x : Subgroup.normalizer (P : Set H) =>
        (((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0) ^ 2) ≠ 1 →
      ∃ b : H, b ∈ Subgroup.normalizer (P : Set H) ∧
        (((ρ b : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 +
          ((ρ b : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 1) ^ 2 ≠ 4 ∧
        Nat.card (Subgroup.centralizer ({b} : Set H)) =
          Nat.card (Set.range fun x : Subgroup.normalizer (P : Set H) =>
            ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0) ∧
        ((∃ n₀ : H, n₀ ∈ Subgroup.normalizer (Subgroup.centralizer ({b} : Set H) : Set H) ∧
            n₀ ∉ Subgroup.centralizer ({b} : Set H)) →
          ∃ k : ℕ, Nat.card (Sylow p H) = 1 + Nat.card P + k * (Nat.card P *
            Nat.card (Set.range fun x : Subgroup.normalizer (P : Set H) =>
              (((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0) ^ 2))) ∧
        (∀ h : H, (((ρ h : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 +
            ((ρ h : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 1) ^ 2 ≠ 4 →
          (¬ ∃ s : H, ∀ g : H, g ∈ Subgroup.centralizer ({h} : Set H) ↔
              s⁻¹ * g * s ∈ Subgroup.centralizer ({b} : Set H)) →
          Nat.card (Subgroup.centralizer ({h} : Set H)) ∣
            Nat.card {x : H // ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 ∨
              ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1} * Nat.card (Sylow p H)))
```

### `Matrix.SpecialLinearGroup.card_sylow_eq_card_add_one_of_finite`

`Thm_Matrix_SpecialLinearGroup_card_sylow_eq_card_add_one_of_finite` — Number of Sylow p-subgroups of a finite subgroup of SL₂(K)

```lean
theorem Matrix.SpecialLinearGroup.card_sylow_eq_card_add_one_of_finite
    {K : Type} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (G : Subgroup SL(2, K)) [Finite G] (P : Sylow p G)
    (hq : 3 < Nat.card P) (hP : Nat.card (Sylow p G) ≠ 1) :
    Nat.card (Sylow p G) = Nat.card P + 1
```

### `Matrix.SpecialLinearGroup.centralizer_semisimple_structure_of_finite`

`Thm_Matrix_SpecialLinearGroup_centralizer_semisimple_structure_of_finite` — Tori of a finite subgroup of SL₂(K)

```lean
theorem Matrix.SpecialLinearGroup.centralizer_semisimple_structure_of_finite
    {K : Type} [Field K] (h2 : (2 : K) ≠ 0)
    {H : Type} [Group H] [Finite H] (ρ : H →* SL(2, K)) (hρ : Function.Injective ρ)
    (h : H) (hh : (((ρ h : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 +
      ((ρ h : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 1) ^ 2 ≠ 4) :
    (∀ g : H, g ∈ Subgroup.centralizer ({h} : Set H) ↔
      ∃ x y : K, ((ρ g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
        x • (1 : Matrix (Fin 2) (Fin 2) K) + y • ((ρ h : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) ∧
    (∀ g ∈ Subgroup.centralizer ({h} : Set H),
      ¬ (((ρ g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 ∨
         ((ρ g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1) →
      Subgroup.centralizer ({g} : Set H) = Subgroup.centralizer ({h} : Set H) ∧
      ((((ρ g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 +
        ((ρ g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 1) ^ 2 ≠ 4)) ∧
    Nat.card (Subgroup.normalizer (Subgroup.centralizer ({h} : Set H) : Set H)) ≤
      2 * Nat.card (Subgroup.centralizer ({h} : Set H)) ∧
    Nat.card {x : H // ¬ (((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 ∨
        ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1) ∧
      ∃ s : H, ∀ g : H, g ∈ Subgroup.centralizer ({x} : Set H) ↔
        s⁻¹ * g * s ∈ Subgroup.centralizer ({h} : Set H)} *
      Nat.card (Subgroup.normalizer (Subgroup.centralizer ({h} : Set H) : Set H)) =
    Nat.card H * (Nat.card (Subgroup.centralizer ({h} : Set H)) -
      Nat.card {x : H // ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 ∨
        ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1})
```

### `Matrix.SpecialLinearGroup.closure_diagonal_unipotent_weyl_eq_top`

`Thm_Matrix_SpecialLinearGroup_closure_diagonal_unipotent_weyl_eq_top` — SL₂(K) is generated by torus, shears and Weyl element

```lean
theorem Matrix.SpecialLinearGroup.closure_diagonal_unipotent_weyl_eq_top
    {K : Type*} [Field K] :
    Subgroup.closure
      ({g : SL(2, K) | ∃ a : K, (g : Matrix (Fin 2) (Fin 2) K) = !![a, 0; 0, a⁻¹]} ∪
        {g : SL(2, K) | ∃ z : K, (g : Matrix (Fin 2) (Fin 2) K) = !![1, z; 0, 1]} ∪
        {g : SL(2, K) | (g : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0]}) = ⊤
```

### `Matrix.SpecialLinearGroup.eq_top_of_normal_of_exists_ne_one_ne_neg_one`

`Thm_Matrix_SpecialLinearGroup_eq_top_of_normal_of_exists_ne_one_ne_neg_one` — Normal subgroups of SL₂(K) for |K|≥ 4

```lean
theorem Matrix.SpecialLinearGroup.eq_top_of_normal_of_exists_ne_one_ne_neg_one
    {K : Type*} [Field K] (hK : 4 ≤ Cardinal.mk K)
    (N : Subgroup SL(2, K)) [N.Normal]
    (hN : ∃ g ∈ N, g ≠ 1 ∧ g ≠ -1) :
    N = ⊤
```

### `Matrix.SpecialLinearGroup.exists_addMonoidHom_conj_T_pow_minimalPeriod_eq_of_finsum_eq_zero`

`Thm_Matrix_SpecialLinearGroup_exists_addMonoidHom_conj_T_pow_minimalPeriod_eq_of_finsum_eq_zero` — Sum-zero functions on cusps realised by homomorphisms of Γ

```lean
theorem Matrix.SpecialLinearGroup.exists_addMonoidHom_conj_T_pow_minimalPeriod_eq_of_finsum_eq_zero
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Γ) (R : Type) [AddCommGroup R]
    (a : MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.T)
          (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Γ) → R)
    (ha : ∑ᶠ c, a c = 0) :
    ∃ φ : Additive Γ →+ R,
      ∀ (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)
        (hg : g⁻¹ * ModularGroup.T ^ Function.minimalPeriod (fun x => ModularGroup.T • x)
                (g : Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Γ) * g ∈ Γ),
        φ (Additive.ofMul ⟨_, hg⟩)
          = a (Quotient.mk (MulAction.orbitRel (Subgroup.zpowers ModularGroup.T) _)
              (g : Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Γ))
```

### `Matrix.SpecialLinearGroup.exists_eq_mul_diagonal_mul_of_gcd_eq_one`

`Thm_Matrix_SpecialLinearGroup_exists_eq_mul_diagonal_mul_of_gcd_eq_one` — Primitive upper-triangular matrices of determinant N in one double coset

```lean
theorem Matrix.SpecialLinearGroup.exists_eq_mul_diagonal_mul_of_gcd_eq_one
    {N a b d : ℕ} (hN : N ≠ 0) (had : a * d = N) (hgcd : Nat.gcd a (Nat.gcd b d) = 1) :
    ∃ γ₁ γ₂ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      !![(a : ℤ), b; 0, d] = (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * !![(N : ℤ), 0; 0, 1] * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ)
```

### `Matrix.SpecialLinearGroup.exists_generators_free_mod_neg_one_of_forall_trace_ne`

`Thm_Matrix_SpecialLinearGroup_exists_generators_free_mod_neg_one_of_forall_trace_ne` — Free basis modulo ± 1 for torsion-free ΓleSL₂(ℤ)

```lean
theorem Matrix.SpecialLinearGroup.exists_generators_free_mod_neg_one_of_forall_trace_ne
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Γ)
    (hΓ : ∀ γ ∈ Γ, (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 1 ∧ (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ -1) :
    ∃ gens : Fin (1 + Γ.index / 6) → Γ,
      Subgroup.closure (Set.range gens ∪ {⟨-1, hneg⟩}) = ⊤ ∧
      ∀ (L : Type) [Group L] (v : Fin (1 + Γ.index / 6) → L),
        ∃ f : Γ →* L, ∀ i, f (gens i) = v i
```

### `Matrix.SpecialLinearGroup.exists_map_eq_and_map_eq_of_coprime`

`Thm_Matrix_SpecialLinearGroup_exists_map_eq_and_map_eq_of_coprime` — Simultaneous lift to SL₂(ℤ) for coprime moduli

```lean
theorem Matrix.SpecialLinearGroup.exists_map_eq_and_map_eq_of_coprime
    (m M : ℕ) [NeZero m] [NeZero M] (hmM : Nat.Coprime m M)
    (A : SL(2, ZMod m)) (B : SL(2, ZMod M)) :
    ∃ γ : SL(2, ℤ), Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod m)) γ = A ∧
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ = B
```

### `Matrix.SpecialLinearGroup.exists_subfield_forall_upperElem_mem_iff_of_finite`

`Thm_Matrix_SpecialLinearGroup_exists_subfield_forall_upperElem_mem_iff_of_finite` — Dickson's theorem, root-group form, in odd characteristic

```lean
theorem Matrix.SpecialLinearGroup.exists_subfield_forall_upperElem_mem_iff_of_finite
    {K : Type} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (G : Subgroup SL(2, K)) [Finite G]
    (hU : ModularCurve.upperElem (1 : K) ∈ G)
    (hL : ∃ μ : K, μ ≠ 0 ∧ ModularCurve.lowerElem μ ∈ G) :
    (p = 3 ∧ ∀ t : K, ModularCurve.upperElem t ∈ G → t ^ 3 = t) ∨
    ∃ F : Subfield K, Finite F ∧
      (∀ t : K, ModularCurve.upperElem t ∈ G ↔ t ∈ F) ∧
      (∀ t : K, ModularCurve.lowerElem t ∈ G ↔ t ∈ F)
```

### `Matrix.SpecialLinearGroup.finrank_addMonoidHom_add_card_orbitRelQuotient_S_ST_le_index_add_one`

`Thm_Matrix_SpecialLinearGroup_finrank_addMonoidHom_add_card_orbitRelQuotient_S_ST_le_index_add_one` — Elliptic-orbit bound for finite-index subgroups of SL₂(ℤ)

```lean
theorem Matrix.SpecialLinearGroup.finrank_addMonoidHom_add_card_orbitRelQuotient_S_ST_le_index_add_one
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Γ) (K : Type) [Field K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    Module.finrank K (Additive Γ →+ K)
      + Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.S)
          (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Γ))
      + Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers (ModularGroup.S * ModularGroup.T))
          (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Γ))
      ≤ Γ.index + 1
```

### `Matrix.SpecialLinearGroup.finrank_addMonoidHom_eq_of_forall_trace_ne`

`Thm_Matrix_SpecialLinearGroup_finrank_addMonoidHom_eq_of_forall_trace_ne` — Dimension of Hom(Γ,K) for elliptic-free ΓleSL₂(ℤ)

```lean
theorem Matrix.SpecialLinearGroup.finrank_addMonoidHom_eq_of_forall_trace_ne
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Γ)
    (hΓ : ∀ γ ∈ Γ, (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 1 ∧ (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ -1)
    (K : Type) [Field K] [CharZero K] :
    Module.finrank K (Additive Γ →+ K) = 1 + Γ.index / 6
```

### `Matrix.SpecialLinearGroup.mem_sup_zpowers_neg_one_iff`

`Thm_Matrix_SpecialLinearGroup_mem_sup_zpowers_neg_one_iff` — Membership in ⟨ Γ, -1⟩ inside SL₂(ℤ)

```lean
theorem Matrix.SpecialLinearGroup.mem_sup_zpowers_neg_one_iff
    (Γ : Subgroup SL(2, ℤ)) (g : SL(2, ℤ)) :
    g ∈ Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) ↔ g ∈ Γ ∨ -g ∈ Γ
```

### `Matrix.SpecialLinearGroup.natCard_fin_two_zmod_eq_of_prime`

`Thm_Matrix_SpecialLinearGroup_natCard_fin_two_zmod_eq_of_prime` — Order of SL₂(ℤ/p) is p(p²-1)

```lean
theorem Matrix.SpecialLinearGroup.natCard_fin_two_zmod_eq_of_prime (p : ℕ) [Fact p.Prime] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) = p * (p ^ 2 - 1)
```

### `Matrix.SpecialLinearGroup.nonempty_freeGroupBasis_map_quotient_center_of_forall_trace_ne`

`Thm_Matrix_SpecialLinearGroup_nonempty_freeGroupBasis_map_quotient_center_of_forall_trace_ne` — Free image in PSL₂(ℤ) of a torsion-free congruence-type subgroup

```lean
theorem Matrix.SpecialLinearGroup.nonempty_freeGroupBasis_map_quotient_center_of_forall_trace_ne
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Γ)
    (hΓ : ∀ γ ∈ Γ, (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 1 ∧ (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ -1) :
    Nonempty (FreeGroupBasis (Fin (1 + Γ.index / 6))
      (Γ.map (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) ℤ)))))
```

### `Matrix.SpecialLinearGroup.three_mul_natCard_doubleCoset_eq_index_and_two_mul_of_forall_smul_eq`

`Thm_Matrix_SpecialLinearGroup_three_mul_natCard_doubleCoset_eq_index_and_two_mul_of_forall_smul_eq` — Double-coset counts for torsion-free subgroups of SL₂(ℤ)

```lean
theorem Matrix.SpecialLinearGroup.three_mul_natCard_doubleCoset_eq_index_and_two_mul_of_forall_smul_eq
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (hfree : ∀ γ : SL(2, ℤ), (γ ∈ Γ ∨ -γ ∈ Γ) → ∀ τ : UpperHalfPlane, γ • τ = τ → γ = 1 ∨ γ = -1) :
    3 * Nat.card (DoubleCoset.Quotient (Γ : Set SL(2, ℤ))
          (Subgroup.zpowers (ModularGroup.S * ModularGroup.T) : Set SL(2, ℤ))) =
        (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index ∧
      2 * Nat.card (DoubleCoset.Quotient (Γ : Set SL(2, ℤ))
          (Subgroup.zpowers ModularGroup.S : Set SL(2, ℤ))) =
        (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index
```

### `Matrix.SpecialLinearGroup.trace_sq_le_four_of_isOfFinOrder`

`Thm_Matrix_SpecialLinearGroup_trace_sq_le_four_of_isOfFinOrder` — Finite-order elements of SL₂(ℤ) have trace squared at most 4

```lean
theorem Matrix.SpecialLinearGroup.trace_sq_le_four_of_isOfFinOrder (γ : SL(2, ℤ)) (h : IsOfFinOrder γ) :
    (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 ≤ 4
```

### `Matrix.UnitaryGroup.exists_polynomial_eq_of_continuous_of_rightFinite`

`Thm_Matrix_UnitaryGroup_exists_polynomial_eq_of_continuous_of_rightFinite` — Right-finite continuous functions on U(2) are polynomial

```lean
theorem Matrix.UnitaryGroup.exists_polynomial_eq_of_continuous_of_rightFinite
    (Φ : ↥(Matrix.unitaryGroup (Fin 2) ℂ) → ℂ) (hc : Continuous Φ)
    (hfin : ∃ s : Finset (↥(Matrix.unitaryGroup (Fin 2) ℂ) → ℂ),
      ∀ k : ↥(Matrix.unitaryGroup (Fin 2) ℂ),
        (fun x => Φ (x * k)) ∈ Submodule.span ℂ (s : Set (↥(Matrix.unitaryGroup (Fin 2) ℂ) → ℂ))) :
    ∃ F ∈ Submodule.span ℂ
        {F : Matrix (Fin 2) (Fin 2) ℂ → ℂ |
          ∃ l : List (Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ), F = fun m => (l.map (fun φ => φ m)).prod},
      ∀ k : ↥(Matrix.unitaryGroup (Fin 2) ℂ), Φ k = F (k : Matrix (Fin 2) (Fin 2) ℂ)
```

### `Matrix.aeval_const_term_eq_zero_of_forall_pos`

`Thm_Matrix_aeval_const_term_eq_zero_of_forall_pos` — Annihilation of the constant term of a matrix pencil

```lean
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Complex.Basic
import P2M.Util
import P2M.Sol.S_Matrix_aeval_const_term_eq_zero_of_forall_pos

theorem
Matrix.aeval_const_term_eq_zero_of_forall_pos
    {R d : ℕ} (M : Fin (d + 1) → Matrix (Fin R) (Fin R) ℂ) (q : Polynomial ℂ)
    (h : ∀ y : ℝ, 0 < y → Polynomial.aeval (∑ a : Fin (d + 1), ((y : ℂ) ^ (a : ℕ)) • M a) q = 0) :
    Polynomial.aeval (M 0) q = 0 := by p2m_exact_reverting @_root_.P2MW.S_Matrix_aeval_const_term_eq_zero_of_forall_pos.solution

```

### `Matrix.apply_eq_zero_of_diagonal_mul_eq_pow_mul_diagonal_of_sub_one_mem`

`Thm_Matrix_apply_eq_zero_of_diagonal_mul_eq_pow_mul_diagonal_of_sub_one_mem` — Off-diagonal entries vanish under a tame matrix relation

```lean
theorem Matrix.apply_eq_zero_of_diagonal_mul_eq_pow_mul_diagonal_of_sub_one_mem {A : Type u} [CommRing A] [IsLocalRing A]
    (hH : ∀ x : A, (∀ n : ℕ, x ∈ IsLocalRing.maximalIdeal A ^ n) → x = 0)
    {a d : A} {q : ℕ} (had : IsUnit (a - (q : A) * d)) (hda : IsUnit (d - (q : A) * a))
    {N : Matrix (Fin 2) (Fin 2) A} (hN : ∀ i j, N i j - (1 : Matrix (Fin 2) (Fin 2) A) i j ∈ IsLocalRing.maximalIdeal A)
    (hrel : Matrix.diagonal ![a, d] * N = N ^ q * Matrix.diagonal ![a, d]) :
    N 0 1 = 0 ∧ N 1 0 = 0
```

### `Matrix.bijective_mulVec_and_forall_exists_mulVec_eq_of_forall_isUnit_of_finrank_eq_card`

`Thm_Matrix_bijective_mulVec_and_forall_exists_mulVec_eq_of_forall_isUnit_of_finrank_eq_card` — Cyclic vectors for a division algebra in M_N(K)

```lean
theorem Matrix.bijective_mulVec_and_forall_exists_mulVec_eq_of_forall_isUnit_of_finrank_eq_card
    {K : Type} [Field K] {D : Type} [Ring D] [Algebra K D]
    (hdiv : ∀ d : D, d ≠ 0 → IsUnit d)
    {N : Type} [Fintype N] [DecidableEq N] [Nonempty N]
    (hdim : Module.finrank K D = Fintype.card N)
    (ι : D →ₐ[K] Matrix N N K) (e₀ : N → K) (he₀ : e₀ ≠ 0) :
    Function.Bijective (fun d : D => (ι d).mulVec e₀) ∧
      ∀ T : Matrix N N K, (∀ d : D, T * ι d = ι d * T) →
        ∃ ξ : D, ∀ d : D, T.mulVec ((ι d).mulVec e₀) = (ι (d * ξ)).mulVec e₀
```

### `Matrix.charpoly_of_uString`

`Thm_Matrix_charpoly_of_uString` — Characteristic polynomial of a U-string matrix

```lean
theorem Matrix.charpoly_of_uString (F : Type) [Field F] (e : ℕ) (a b : F) :
    (Matrix.of fun i j : Fin (e + 1) =>
        if (j : ℕ) = 0 then (if (i : ℕ) = 0 then a else if (i : ℕ) = 1 then -b else 0)
        else (if (i : ℕ) + 1 = (j : ℕ) then (1 : F) else 0)).charpoly =
      if e = 0 then X - C a else X ^ (e - 1) * (X ^ 2 - C a * X + C b)
```

### `Matrix.det_eq_zero_of_isIdempotentElem_of_trace_eq_one`

`Thm_Matrix_det_eq_zero_of_isIdempotentElem_of_trace_eq_one` — Trace-one 2×2 idempotents have zero determinant

```lean
theorem Matrix.det_eq_zero_of_isIdempotentElem_of_trace_eq_one {A : Type*} [CommRing A]
    {e : Matrix (Fin 2) (Fin 2) A} (he : IsIdempotentElem e) (htr : e.trace = 1) :
    e.det = 0
```

### `Matrix.existsUnique_add_mulVec_pow_eq_of_forall_mem_of_isNilpotent`

`Thm_Matrix_existsUnique_add_mulVec_pow_eq_of_forall_mem_of_isNilpotent` — Unique solution of y + D y⁽ᵖ⁾ = b for nilpotent-triangular D

```lean
theorem Matrix.existsUnique_add_mulVec_pow_eq_of_forall_mem_of_isNilpotent
    {S : Type u} [CommRing S] (p : ℕ) [Fact p.Prime] [CharP S p]
    {d : ℕ} (𝔫 : Ideal S) (h𝔫 : IsNilpotent 𝔫)
    (D : Matrix (Fin d) (Fin d) S) (hD : ∀ i j : Fin d, j ≤ i → D i j ∈ 𝔫)
    (b : Fin d → S) :
    ∃! y : Fin d → S, y + D.mulVec (fun j => y j ^ p) = b
```

### `Matrix.existsUnique_eq_one_kroneckerMap_of_forall_commute_kroneckerMap_one`

`Thm_Matrix_existsUnique_eq_one_kroneckerMap_of_forall_commute_kroneckerMap_one` — The commutant of M_m(K)⊗ 1 consists of 1⊗ B

```lean
theorem Matrix.existsUnique_eq_one_kroneckerMap_of_forall_commute_kroneckerMap_one
    {K : Type} [CommRing K] {m n : Type} [Fintype m] [DecidableEq m] [Nonempty m] [Fintype n] [DecidableEq n]
    (X : Matrix (m × n) (m × n) K)
    (hX : ∀ A : Matrix m m K,
      X * Matrix.kroneckerMap (· * ·) A (1 : Matrix n n K) = Matrix.kroneckerMap (· * ·) A (1 : Matrix n n K) * X) :
    ∃! B : Matrix n n K, X = Matrix.kroneckerMap (· * ·) (1 : Matrix m m K) B
```

### `Matrix.exists_adapted_basis_of_unipotent_family`

`Thm_Matrix_exists_adapted_basis_of_unipotent_family` — Adapted basis for a unipotent family of 2× 2 matrices

```lean
theorem Matrix.exists_adapted_basis_of_unipotent_family
    {R : Type} [CommRing R] [IsDomain R]
    [ValuationRing R] (T : Set (Matrix (Fin 2) (Fin 2) R))
    (hmul : ∀ A ∈ T, ∀ B ∈ T, A * B ∈ T)
    (hsq : ∀ A ∈ T, (A - 1) * (A - 1) = 0)
    (A₀ : Matrix (Fin 2) (Fin 2) R) (hA₀ : A₀ ∈ T) (hA₀ne : A₀ ≠ 1) :
    ∃ P : Matrix (Fin 2) (Fin 2) R, IsUnit P.det ∧
      (∃ t : R, t ≠ 0 ∧ A₀ * P = P * Matrix.of ![![1, t], ![0, 1]]) ∧
      ∀ A ∈ T, ∃ s : R, A * P = P * Matrix.of ![![1, s], ![0, 1]]
```

### `Matrix.exists_adapted_frob_shape`

`Thm_Matrix_exists_adapted_frob_shape` — Shape of Frobenius in a basis adapted to a nilpotent line

```lean
theorem Matrix.exists_adapted_frob_shape
    {R : Type} [CommRing R] [IsDomain R]
    (N₀ P F : Matrix (Fin 2) (Fin 2) R) (hP : IsUnit P.det)
    (t : R) (ht : t ≠ 0) (hN₀P : N₀ * P = P * Matrix.of ![![0, t], ![0, 0]])
    (q : R) (hFN : F * N₀ = q • (N₀ * F)) :
    ∃ F' : Matrix (Fin 2) (Fin 2) R,
      F * P = P * F' ∧ F' 1 0 = 0 ∧ F' 0 0 = q * F' 1 1
```

### `Matrix.exists_algEquiv_centralizer_forall_map_le_iff_apply_one_zero_eq_zero_of_squarefree`

`Thm_Matrix_exists_algEquiv_centralizer_forall_map_le_iff_apply_one_zero_eq_zero_of_squarefree` — Borel condition for stabilising a submodule of order N²

```lean
theorem Matrix.exists_algEquiv_centralizer_forall_map_le_iff_apply_one_zero_eq_zero_of_squarefree
    (N : ℕ) [NeZero N] (hN : Squarefree N)
    (α : Matrix (Fin 2) (Fin 2) (ZMod N) →+* Module.End (ZMod N) (Fin 2 → Fin 2 → ZMod N))
    (hfree : ∃ v₀ : Fin 2 → Fin 2 → ZMod N, ∀ w : Fin 2 → Fin 2 → ZMod N,
      ∃! a : Matrix (Fin 2) (Fin 2) (ZMod N), w = α a v₀)
    (W : Submodule (ZMod N) (Fin 2 → Fin 2 → ZMod N))
    (hWstab : ∀ (a : Matrix (Fin 2) (Fin 2) (ZMod N)) (w : Fin 2 → Fin 2 → ZMod N), w ∈ W → α a w ∈ W)
    (hWcard : Nat.card ↥W = N ^ 2) :
    ∃ θ : ↥(Subalgebra.centralizer (ZMod N) (Set.range α)) ≃ₐ[ZMod N] Matrix (Fin 2) (Fin 2) (ZMod N),
      ∀ (β : Module.End (ZMod N) (Fin 2 → Fin 2 → ZMod N))
        (hβ : β ∈ Subalgebra.centralizer (ZMod N) (Set.range α)),
        Submodule.map β W ≤ W ↔ θ ⟨β, hβ⟩ 1 0 = 0
```

### `Matrix.exists_bifiltered_unimodular_of_forall_block_avoidance`

`Thm_Matrix_exists_bifiltered_unimodular_of_forall_block_avoidance` — Existence of bifiltered p-unimodular matrices avoiding affine conditions

```lean
theorem Matrix.exists_bifiltered_unimodular_of_forall_block_avoidance
    (p : ℕ) [Fact p.Prime] {r : ℕ} (n : Fin r → ℕ) (hn0 : ∀ i : Fin r, (i : ℕ) = 0 → n i = 0)
    {ι : Fin r → Type*} [∀ i, Fintype (ι i)]
    {V : ∀ i, ι i → Type*} [∀ i j, AddCommGroup (V i j)] [∀ i j, Module (ZMod p) (V i j)]
    (φ : ∀ i j, (Fin r → ZMod p) →ᵃ[ZMod p] V i j)
    (hφ : ∀ i : Fin r, (i : ℕ) ≠ 0 → ∀ j, ∃ x, φ i j x ≠ 0)
    (hm : ∀ i, Fintype.card (ι i) + 1 < p) :
    ∃ (U : Matrix (Fin r) (Fin r) ℚ) (d : Fin r → Fin r → ZMod p),
      IsUnit U ∧
      (∀ i j, max 0 ((n i : ℤ) - (n j : ℤ)) ≤ padicValRat p (U i j) ∨ U i j = 0) ∧
      (∀ i j, max 0 ((n i : ℤ) - (n j : ℤ)) ≤ padicValRat p (U⁻¹ i j) ∨ U⁻¹ i j = 0) ∧
      (∀ i j : Fin r, (i : ℕ) = 0 → U i j = if (j : ℕ) = 0 then 1 else 0) ∧
      (∀ i j, U i j = (p : ℚ) ^ (max 0 ((n i : ℤ) - (n j : ℤ))).toNat * ((d i j).val : ℚ)) ∧
      (∀ c : ℕ, IsUnit (Matrix.det (Matrix.of fun (i j : {a : Fin r // n a = c}) => d i.1 j.1))) ∧
      (∀ i : Fin r, (i : ℕ) ≠ 0 → ∀ j, φ i j (d i) ≠ 0)
```

### `Matrix.exists_bijective_transpose_mulVec_of_adjoin_intCast`

`Thm_Matrix_exists_bijective_transpose_mulVec_of_adjoin_intCast` — Freeness over the transposed integer subalgebra in characteristic zero

```lean
theorem Matrix.exists_bijective_transpose_mulVec_of_adjoin_intCast
    {ι : Type*} (n d : ℕ) (M : ι → Matrix (Fin n) (Fin n) ℤ)
    (hcomm : ∀ i j, M i * M j = M j * M i)
    (hfree : ∃ v : Fin d → (Fin n → ℂ), Function.Bijective
      (fun c : Fin d → ↥(Algebra.adjoin ℂ (Set.range fun i => (M i).map (Int.cast : ℤ → ℂ))) =>
        ∑ k, ((c k : Matrix (Fin n) (Fin n) ℂ).mulVec (v k))))
    (hmult : ∀ χ : ↥(Algebra.adjoin ℂ (Set.range fun i => (M i).map (Int.cast : ℤ → ℂ))) →ₐ[ℂ] ℂ,
      Module.finrank ℂ ↥(⨅ a : ↥(Algebra.adjoin ℂ (Set.range fun i => (M i).map (Int.cast : ℤ → ℂ))),
        Module.End.eigenspace (Matrix.toLin' (a : Matrix (Fin n) (Fin n) ℂ)) (χ a)) = d)
    (K : Type*) [Field K] [CharZero K] :
    ∃ w : Fin d → (Fin n → K), Function.Bijective
      (fun c : Fin d → ↥(Algebra.adjoin K (Set.range fun i => ((M i).transpose).map (Int.cast : ℤ → K))) =>
        ∑ k, ((c k : Matrix (Fin n) (Fin n) K).mulVec (w k)))
```

### `Matrix.exists_const_forall_norm_le_mul_of_norm_sum_pow_smul_le`

`Thm_Matrix_exists_const_forall_norm_le_mul_of_norm_sum_pow_smul_le` — Uniform Vandermonde inversion bound for vector-valued coefficients

```lean
theorem Matrix.exists_const_forall_norm_le_mul_of_norm_sum_pow_smul_le
    (L : ℕ) (x : Fin L → ℂ) (hx : Function.Injective x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] (v : Fin L → E) (B : ℝ),
      (∀ t : Fin L, ‖∑ m : Fin L, (x t) ^ (m : ℕ) • v m‖ ≤ B) → ∀ m : Fin L, ‖v m‖ ≤ C * B
```

### `Matrix.exists_contDiffOn_upperTriangular_pos_diag_mul_orthogonal_eq`

`Thm_Matrix_exists_contDiffOn_upperTriangular_pos_diag_mul_orthogonal_eq` — Smooth QR factorisation on GLₙ(ℝ)

```lean
theorem Matrix.exists_contDiffOn_upperTriangular_pos_diag_mul_orthogonal_eq
    (n : ℕ) :
    ∃ (b o : (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ)),
      ContDiffOn ℝ (⊤ : ℕ∞) b {A : Fin n → Fin n → ℝ | (Matrix.of A).det ≠ 0} ∧
      ContDiffOn ℝ (⊤ : ℕ∞) o {A : Fin n → Fin n → ℝ | (Matrix.of A).det ≠ 0} ∧
      ∀ A : Fin n → Fin n → ℝ, (Matrix.of A).det ≠ 0 →
        (∀ i j : Fin n, j < i → b A i j = 0) ∧ (∀ i : Fin n, 0 < b A i i) ∧
        (∀ i j : Fin n, ∑ a : Fin n, o A a i * o A a j = if i = j then 1 else 0) ∧
        ∀ i j : Fin n, A i j = ∑ k : Fin n, b A i k * o A k j
```

### `Matrix.exists_det_eq_one_unipotent_forall_mul_mem_of_ne_bot_of_ne_top`

`Thm_Matrix_exists_det_eq_one_unipotent_forall_mul_mem_of_ne_bot_of_ne_top` — A non-trivial unipotent in SL₂(F) carrying I into I'

```lean
theorem Matrix.exists_det_eq_one_unipotent_forall_mul_mem_of_ne_bot_of_ne_top
    {F : Type*} [Field F] (I I' : Submodule (Matrix (Fin 2) (Fin 2) F) (Matrix (Fin 2) (Fin 2) F))
    (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) (hI'0 : I' ≠ ⊥) (hI'1 : I' ≠ ⊤) :
    ∃ g : Matrix (Fin 2) (Fin 2) F, g.det = 1 ∧ (g - 1) * (g - 1) = 0 ∧ g ≠ 1 ∧ ∀ A ∈ I, A * g ∈ I'
```

### `Matrix.exists_det_eq_one_unipotent_forall_mul_mem_of_not_le_of_not_le`

`Thm_Matrix_exists_det_eq_one_unipotent_forall_mul_mem_of_not_le_of_not_le` — Unipotent in SL₂(F) stabilising I₀ and mapping I into I'

```lean
theorem Matrix.exists_det_eq_one_unipotent_forall_mul_mem_of_not_le_of_not_le
    {F : Type*} [Field F] (I₀ I I' : Submodule (Matrix (Fin 2) (Fin 2) F) (Matrix (Fin 2) (Fin 2) F))
    (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) (hI'0 : I' ≠ ⊥) (hI'1 : I' ≠ ⊤)
    (h₀ : ¬ I₀ ≤ I) (h₀' : ¬ I₀ ≤ I') :
    ∃ g : Matrix (Fin 2) (Fin 2) F, g.det = 1 ∧ (g - 1) * (g - 1) = 0 ∧
      (∀ A ∈ I₀, A * g ∈ I₀) ∧ ∀ A ∈ I, A * g ∈ I'
```

### `Matrix.exists_det_map_eq_of_isUnit_of_ne`

`Thm_Matrix_exists_det_map_eq_of_isUnit_of_ne` — Prescribing determinants mod two distinct primes

```lean
theorem Matrix.exists_det_map_eq_of_isUnit_of_ne
    (ℓ q : ℕ) [Fact ℓ.Prime] [Fact q.Prime] (hℓq : ℓ ≠ q) (u : (ZMod ℓ)ˣ) (v : (ZMod q)ˣ) :
    ∃ g : Matrix (Fin 2) (Fin 2) ℤ,
      IsUnit (g.map (Int.castRingHom (ZMod (q * ℓ)))).det ∧
      ((g.det : ℤ) : ZMod ℓ) = (u : ZMod ℓ) ∧ ((g.det : ℤ) : ZMod q) = (v : ZMod q)
```

### `Matrix.exists_differentiableOn_det_ne_zero_forall_intertwiner_eq_smul`

`Thm_Matrix_exists_differentiableOn_det_ne_zero_forall_intertwiner_eq_smul` — Holomorphic intertwiner line for a holomorphic family

```lean
theorem Matrix.exists_differentiableOn_det_ne_zero_forall_intertwiner_eq_smul
    {X : Type} {n : ℕ} (ι' : X → Matrix (Fin n) (Fin n) ℂ)
    (hspan : Submodule.span ℂ (Set.range ι') = ⊤)
    (z₀ : ℂ) {ε : ℝ} (hε : 0 < ε) (ρ : ℂ → X → Matrix (Fin n) (Fin n) ℂ)
    (hρ : ∀ (x : X) (i j : Fin n), DifferentiableOn ℂ (fun z : ℂ => ρ z x i j) (Metric.ball z₀ ε))
    (hM : ∀ z ∈ Metric.ball z₀ ε, ∃ M : Matrix (Fin n) (Fin n) ℂ, M.det ≠ 0 ∧ ∀ x : X, M * ι' x = ρ z x * M) :
    ∃ (ε' : ℝ) (N : ℂ → Matrix (Fin n) (Fin n) ℂ), 0 < ε' ∧ ε' ≤ ε ∧
      (∀ i j : Fin n, DifferentiableOn ℂ (fun z : ℂ => N z i j) (Metric.ball z₀ ε')) ∧
      ∀ z ∈ Metric.ball z₀ ε',
        (N z).det ≠ 0 ∧ (∀ x : X, N z * ι' x = ρ z x * N z) ∧
        ∀ M : Matrix (Fin n) (Fin n) ℂ, (∀ x : X, M * ι' x = ρ z x * M) → ∃ c : ℂ, M = c • N z
```

### `Matrix.exists_eigenvalues_of_henselianLocalRing`

`Thm_Matrix_exists_eigenvalues_of_henselianLocalRing` — Lifting distinct residual eigenvalues of a 2×2 matrix

```lean
theorem Matrix.exists_eigenvalues_of_henselianLocalRing {A : Type*} [CommRing A] [IsLocalRing A]
    [HenselianLocalRing A] (M : Matrix (Fin 2) (Fin 2) A) {α β : IsLocalRing.ResidueField A}
    (hne : α ≠ β) (htr : IsLocalRing.residue A M.trace = α + β)
    (hdet : IsLocalRing.residue A M.det = α * β) :
    ∃ a b : A, M.trace = a + b ∧ M.det = a * b ∧ IsUnit (a - b) ∧
      IsLocalRing.residue A a = α ∧ IsLocalRing.residue A b = β
```

### `Matrix.exists_eq_iwahori_mul_diagonal_mul_iwahori_or_eq_atkinLehner_mul_of_mem_iwahori`

`Thm_Matrix_exists_eq_iwahori_mul_diagonal_mul_iwahori_or_eq_atkinLehner_mul_of_mem_iwahori` — Iwahori double cosets at determinant valuation one

```lean
theorem Matrix.exists_eq_iwahori_mul_diagonal_mul_iwahori_or_eq_atkinLehner_mul_of_mem_iwahori
    (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hpv : (p : 𝓞 ℚ) ∈ v.asIdeal)
    (Y Yi : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) (h1 : Y * Yi = 1) (h2 : Yi * Y = 1)
    (hY : ∀ i j, Y i j ∈ v.adicCompletionIntegers ℚ) (hY10 : (p : v.adicCompletion ℚ)⁻¹ * Y 1 0 ∈ v.adicCompletionIntegers ℚ)
    (hpYi : ∀ i j, ((p : v.adicCompletion ℚ) • Yi) i j ∈ v.adicCompletionIntegers ℚ) (hpYi10 : (p : v.adicCompletion ℚ)⁻¹ * ((p : v.adicCompletion ℚ) • Yi) 1 0 ∈ v.adicCompletionIntegers ℚ)
    (hYi : ¬ ((∀ i j, Yi i j ∈ v.adicCompletionIntegers ℚ) ∧ (p : v.adicCompletion ℚ)⁻¹ * Yi 1 0 ∈ v.adicCompletionIntegers ℚ))
    (hpY : ¬ ((∀ i j, ((p : v.adicCompletion ℚ)⁻¹ • Y) i j ∈ v.adicCompletionIntegers ℚ) ∧ (p : v.adicCompletion ℚ)⁻¹ * ((p : v.adicCompletion ℚ)⁻¹ • Y) 1 0 ∈ v.adicCompletionIntegers ℚ)) :
    Valued.v Y.det = Valued.v (p : v.adicCompletion ℚ) ∧
    ((∃ ι ιi ι' ι'i : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      (∀ i j, ι i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, ιi i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, ι' i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, ι'i i j ∈ v.adicCompletionIntegers ℚ) ∧
      ι * ιi = 1 ∧ ιi * ι = 1 ∧ ι' * ι'i = 1 ∧ ι'i * ι' = 1 ∧
      (p : v.adicCompletion ℚ)⁻¹ * ι 1 0 ∈ v.adicCompletionIntegers ℚ ∧ (p : v.adicCompletion ℚ)⁻¹ * ι' 1 0 ∈ v.adicCompletionIntegers ℚ ∧
      Y = ι * !![(p : v.adicCompletion ℚ), 0; 0, 1] * ι') ∨
     (∃ ι ιi ι' ι'i : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      (∀ i j, ι i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, ιi i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, ι' i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, ι'i i j ∈ v.adicCompletionIntegers ℚ) ∧
      ι * ιi = 1 ∧ ιi * ι = 1 ∧ ι' * ι'i = 1 ∧ ι'i * ι' = 1 ∧
      (p : v.adicCompletion ℚ)⁻¹ * ι 1 0 ∈ v.adicCompletionIntegers ℚ ∧ (p : v.adicCompletion ℚ)⁻¹ * ι' 1 0 ∈ v.adicCompletionIntegers ℚ ∧
      Y = ι * !![1, 0; 0, (p : v.adicCompletion ℚ)] * ι') ∨
     (∃ κ κi : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      (∀ i j, κ i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, κi i j ∈ v.adicCompletionIntegers ℚ) ∧ κ * κi = 1 ∧ κi * κ = 1 ∧
      (p : v.adicCompletion ℚ)⁻¹ * κ 1 0 ∈ v.adicCompletionIntegers ℚ ∧ Y = !![0, 1; (p : v.adicCompletion ℚ), 0] * κ))
```

### `Matrix.exists_eq_smul_one_of_commute_of_map_span_eq_top`

`Thm_Matrix_exists_eq_smul_one_of_commute_of_map_span_eq_top` — Commutant of a residually spanning set of matrices is scalar

```lean
theorem Matrix.exists_eq_smul_one_of_commute_of_map_span_eq_top
    {n : Type*} [Fintype n] [DecidableEq n] {A : Type*} [CommRing A] [IsLocalRing A]
    {k : Type*} [Field k] (π : A →+* k) (hπ : Function.Surjective π)
    {S : Set (Matrix n n A)}
    (hS : Submodule.span k ((fun X : Matrix n n A => X.map π) '' S) = ⊤)
    (M : Matrix n n A) (hM : ∀ X ∈ S, X * M = M * X) : ∃ a : A, M = a • 1
```

### `Matrix.exists_eq_smul_one_of_commute_of_span_eq_top`

`Thm_Matrix_exists_eq_smul_one_of_commute_of_span_eq_top` — Matrices commuting with a spanning set are scalar

```lean
theorem Matrix.exists_eq_smul_one_of_commute_of_span_eq_top
    {n : Type*} [Fintype n] [DecidableEq n] {A : Type*} [CommRing A]
    {S : Set (Matrix n n A)} (hS : Submodule.span A S = ⊤)
    (M : Matrix n n A) (hM : ∀ X ∈ S, X * M = M * X) :
    ∃ a : A, M = a • 1
```

### `Matrix.exists_eq_smul_one_of_forall_specialLinearGroup_mul_eq_smul_mul`

`Thm_Matrix_exists_eq_smul_one_of_forall_specialLinearGroup_mul_eq_smul_mul` — Matrices projectively commuting with SL₂(ℤ/q) are scalar

```lean
theorem Matrix.exists_eq_smul_one_of_forall_specialLinearGroup_mul_eq_smul_mul
    (q : ℕ) (k : Type) [Field k] (φ : ZMod q →+* k)
    (B : Matrix (Fin 2) (Fin 2) k) (hB : B.det ≠ 0)
    (h : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) (ZMod q), ∃ c : k,
      B * (γ : Matrix (Fin 2) (Fin 2) (ZMod q)).map φ = c • ((γ : Matrix (Fin 2) (Fin 2) (ZMod q)).map φ * B)) :
    ∃ a : k, B = a • (1 : Matrix (Fin 2) (Fin 2) k)
```

### `Matrix.exists_forall_existsUnique_eq_apply_of_squarefree_of_card_eq`

`Thm_Matrix_exists_forall_existsUnique_eq_apply_of_squarefree_of_card_eq` — Rank-one freeness of M₂(ℤ/N)-modules of order N⁴

```lean
theorem Matrix.exists_forall_existsUnique_eq_apply_of_squarefree_of_card_eq
    (N : ℕ) [NeZero N] (hN : Squarefree N) (V : Type) [AddCommGroup V] [Module (ZMod N) V] [Finite V]
    (hV : Nat.card V = N ^ 4) (α : Matrix (Fin 2) (Fin 2) (ZMod N) →+* Module.End (ZMod N) V) :
    ∃ v₀ : V, ∀ w : V, ∃! a : Matrix (Fin 2) (Fin 2) (ZMod N), w = α a v₀
```

### `Matrix.exists_forall_exists_eq_pow_smul_map_coe_of_injective_of_forall_exists_eq_map_coe`

`Thm_Matrix_exists_forall_exists_eq_pow_smul_map_coe_of_injective_of_forall_exists_eq_map_coe` — Transferring lattice-saturation between two embeddings into Mₙ(ℚₚ)

```lean
theorem Matrix.exists_forall_exists_eq_pow_smul_map_coe_of_injective_of_forall_exists_eq_map_coe
    (p : ℕ) [Fact p.Prime] {A : Type u} [Ring A] {n : Type} [Fintype n] [DecidableEq n]
    (θ E : A →+* Matrix n n ℚ_[p]) (hθ : Function.Injective θ) (hE : Function.Injective E) (m : ℕ)
    (hθm : ∀ M : Matrix n n ℤ_[p], ∃ a : A, θ a = (p : ℚ_[p]) ^ m • M.map ((↑) : ℤ_[p] → ℚ_[p]))
    (hEint : ∀ a : A, ∃ M : Matrix n n ℤ_[p], E a = M.map ((↑) : ℤ_[p] → ℚ_[p])) :
    ∃ m' : ℕ, ∀ M : Matrix n n ℤ_[p], ∃ a : A, E a = (p : ℚ_[p]) ^ m' • M.map ((↑) : ℤ_[p] → ℚ_[p])
```

### `Matrix.exists_generalLinearGroup_forall_algHom_apply_eq_conj`

`Thm_Matrix_exists_generalLinearGroup_forall_algHom_apply_eq_conj` — Every K-algebra endomorphism of Mₙ(K) is inner

```lean
theorem Matrix.exists_generalLinearGroup_forall_algHom_apply_eq_conj
    (K : Type) [Field K] (n : Type) [Fintype n] [DecidableEq n] [Nonempty n]
    (f : Matrix n n K →ₐ[K] Matrix n n K) :
    ∃ u : GL n K, ∀ x : Matrix n n K,
      f x = (u : Matrix n n K) * x * ((u⁻¹ : GL n K) : Matrix n n K)
```

### `Matrix.exists_generalLinearGroup_forall_mem_addSubgroup_iff_of_isPrincipalIdealRing`

`Thm_Matrix_exists_generalLinearGroup_forall_mem_addSubgroup_iff_of_isPrincipalIdealRing` — Bounded full lattices of matrices over a PID are principal

```lean
theorem Matrix.exists_generalLinearGroup_forall_mem_addSubgroup_iff_of_isPrincipalIdealRing
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {n : Type*} [Fintype n] [DecidableEq n]
    (L : AddSubgroup (Matrix n n K))
    (hmul : ∀ x ∈ L, ∀ m : Matrix n n R, x * m.map (algebraMap R K) ∈ L)
    (hbdd : ∃ d : R, d ≠ 0 ∧ ∀ x ∈ L, ∀ i j, algebraMap R K d * x i j ∈ (algebraMap R K).range)
    (hfull : ∃ N : R, N ≠ 0 ∧ ∀ m : Matrix n n R, algebraMap R K N • m.map (algebraMap R K) ∈ L) :
    ∃ g : GL n K, ∀ x : Matrix n n K,
      x ∈ L ↔ ∀ i j, (((g⁻¹ : GL n K) : Matrix n n K) * x) i j ∈ (algebraMap R K).range
```

### `Matrix.exists_isUnit_det_and_mul_map_castRingHom_zmod_eq_one`

`Thm_Matrix_exists_isUnit_det_and_mul_map_castRingHom_zmod_eq_one` — Integer two-sided inverse modulo n for a matrix with unit determinant

```lean
theorem Matrix.exists_isUnit_det_and_mul_map_castRingHom_zmod_eq_one
    {m : Type} [Fintype m] [DecidableEq m] (n : ℕ)
    (g : Matrix m m ℤ) (hg : IsUnit ((g.det : ℤ) : ZMod n)) :
    ∃ g' : Matrix m m ℤ, IsUnit ((g'.det : ℤ) : ZMod n) ∧
      (g * g').map (Int.castRingHom (ZMod n)) = 1 ∧ (g' * g).map (Int.castRingHom (ZMod n)) = 1
```

### `Matrix.exists_iwahori_conj_diagonal_not_mem_of_exists_iwahori_conj_not_mem`

`Thm_Matrix_exists_iwahori_conj_diagonal_not_mem_of_exists_iwahori_conj_not_mem` — Iwahori conjugation failure transfers to the twin maximal order

```lean
theorem Matrix.exists_iwahori_conj_diagonal_not_mem_of_exists_iwahori_conj_not_mem
    (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hpv : (p : 𝓞 ℚ) ∈ v.asIdeal)
    (Y Yi : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) (h1 : Y * Yi = 1) (h2 : Yi * Y = 1)
    (hY : ∀ i j, Y i j ∈ v.adicCompletionIntegers ℚ) (hY10 : (p : v.adicCompletion ℚ)⁻¹ * Y 1 0 ∈ v.adicCompletionIntegers ℚ)
    (hpYi : ∀ i j, ((p : v.adicCompletion ℚ) • Yi) i j ∈ v.adicCompletionIntegers ℚ)
    (hpYi10 : (p : v.adicCompletion ℚ)⁻¹ * ((p : v.adicCompletion ℚ) • Yi) 1 0 ∈ v.adicCompletionIntegers ℚ)
    (hYi : ¬ ((∀ i j, Yi i j ∈ v.adicCompletionIntegers ℚ) ∧ (p : v.adicCompletion ℚ)⁻¹ * Yi 1 0 ∈ v.adicCompletionIntegers ℚ))
    (hpY : ¬ ((∀ i j, ((p : v.adicCompletion ℚ)⁻¹ • Y) i j ∈ v.adicCompletionIntegers ℚ) ∧
      (p : v.adicCompletion ℚ)⁻¹ * ((p : v.adicCompletion ℚ)⁻¹ • Y) 1 0 ∈ v.adicCompletionIntegers ℚ))
    (hZ : ∃ Z : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ), (∀ i j, Z i j ∈ v.adicCompletionIntegers ℚ) ∧ (p : v.adicCompletion ℚ)⁻¹ * Z 1 0 ∈ v.adicCompletionIntegers ℚ ∧
      ¬ ∀ i j, (Y * Z * Yi) i j ∈ v.adicCompletionIntegers ℚ) :
    ∃ X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ), (∀ i j, X i j ∈ v.adicCompletionIntegers ℚ) ∧ (p : v.adicCompletion ℚ)⁻¹ * X 1 0 ∈ v.adicCompletionIntegers ℚ ∧
      ¬ ∀ i j, (Matrix.diagonal ![(1 : v.adicCompletion ℚ), ((p : v.adicCompletion ℚ))⁻¹] * (Yi * X * Y) *
        Matrix.diagonal ![(1 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)]) i j ∈ v.adicCompletionIntegers ℚ
```

### `Matrix.exists_list_prod_elementary_eq_diagonal_of_det_map_mul_eq_one`

`Thm_Matrix_exists_list_prod_elementary_eq_diagonal_of_det_map_mul_eq_one` — Whitehead's lemma for diag(g₁,g₂) over M₂(F)

```lean
theorem Matrix.exists_list_prod_elementary_eq_diagonal_of_det_map_mul_eq_one
    {A : Type*} [Ring A] {F : Type*} [Field F]
    (φ : A ≃+* Matrix (Fin 2) (Fin 2) F) (g₁ g₂ : Aˣ) (h : (φ ((g₁ : A) * g₂)).det = 1) :
    ∃ l : List (Bool × A),
      (l.map fun p : Bool × A =>
        if p.1 then !![(1 : A), p.2; 0, 1] else !![(1 : A), 0; p.2, 1]).prod = !![(g₁ : A), 0; 0, (g₂ : A)]
```

### `Matrix.exists_mulVec_eq_and_isUnit_det_of_isIdempotentElem_of_trace_eq_one`

`Thm_Matrix_exists_mulVec_eq_and_isUnit_det_of_isIdempotentElem_of_trace_eq_one` — Adapted basis for a trace-one 2×2 idempotent over a local ring

```lean
theorem Matrix.exists_mulVec_eq_and_isUnit_det_of_isIdempotentElem_of_trace_eq_one {A : Type u} [CommRing A] [IsLocalRing A]
    {e : Matrix (Fin 2) (Fin 2) A} (he : e * e = e) (htr : e.trace = 1) :
    ∃ u w : Fin 2 → A, IsUnit (Matrix.of (fun i j => ![u, w] j i)).det ∧
      e.mulVec u = u ∧ e.mulVec w = 0
```

### `Matrix.exists_mvPolynomial_eval_eq_of_continuousOn_orthogonal_of_finite_span_translates`

`Thm_Matrix_exists_mvPolynomial_eval_eq_of_continuousOn_orthogonal_of_finite_span_translates` — O(n)-finite continuous functions are polynomials in the entries

```lean
theorem Matrix.exists_mvPolynomial_eval_eq_of_continuousOn_orthogonal_of_finite_span_translates
    (n : ℕ) (f : (Fin n → Fin n → ℝ) → ℂ)
    (hf : ContinuousOn f {o : Fin n → Fin n → ℝ | ∀ i j : Fin n, ∑ a : Fin n, o a i * o a j = if i = j then 1 else 0})
    (hfin : ∃ (m : ℕ) (g : Fin m → (Fin n → Fin n → ℝ) → ℂ),
      ∀ r : Fin n → Fin n → ℝ, (∀ i j : Fin n, ∑ a : Fin n, r a i * r a j = if i = j then 1 else 0) →
        ∃ a : Fin m → ℂ, ∀ o : Fin n → Fin n → ℝ,
          (∀ i j : Fin n, ∑ a : Fin n, o a i * o a j = if i = j then 1 else 0) →
          f (fun i j => ∑ k : Fin n, o i k * r k j) = ∑ l, a l * g l o) :
    ∃ P : MvPolynomial (Fin n × Fin n) ℂ, ∀ o : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, ∑ a : Fin n, o a i * o a j = if i = j then 1 else 0) →
      f o = MvPolynomial.eval (fun ij : Fin n × Fin n => ((o ij.1 ij.2 : ℝ) : ℂ)) P
```

### `Matrix.exists_natCard_eq_pow_two_mul_of_module_zmod`

`Thm_Matrix_exists_natCard_eq_pow_two_mul_of_module_zmod` — Finite M₂(𝔽_ℓ)-modules have order ℓ^{2k}

```lean
theorem Matrix.exists_natCard_eq_pow_two_mul_of_module_zmod
    (ℓ : ℕ) [Fact ℓ.Prime] (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] [Finite V] :
    ∃ k : ℕ, Nat.card V = ℓ ^ (2 * k)
```

### `Matrix.exists_ne_zero_forall_mulVec_eq_zero_of_forall_map_mulVec_eq_zero`

`Thm_Matrix_exists_ne_zero_forall_mulVec_eq_zero_of_forall_map_mulVec_eq_zero` — Common kernel vectors descend to the base field

```lean
theorem Matrix.exists_ne_zero_forall_mulVec_eq_zero_of_forall_map_mulVec_eq_zero
    {k K : Type*} [Field k] [Field K] [Algebra k K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {J : Type*} (A : J → Matrix ι ι k) (v : ι → K) (hv : v ≠ 0)
    (hAv : ∀ j, ((A j).map (algebraMap k K)).mulVec v = 0) :
    ∃ w : ι → k, w ≠ 0 ∧ ∀ j, (A j).mulVec w = 0
```

### `Matrix.exists_rat_mul_eq_map_padicInt_of_isUnit_det`

`Thm_Matrix_exists_rat_mul_eq_map_padicInt_of_isUnit_det` — Factorisation GLₙ(ℚₚ)=GLₙ(ℤₚ)cdotGLₙ(ℚ)

```lean
theorem Matrix.exists_rat_mul_eq_map_padicInt_of_isUnit_det
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℚ_[p]) (hM : IsUnit M.det) :
    ∃ (Q : Matrix (Fin n) (Fin n) ℚ) (P : Matrix (Fin n) (Fin n) ℤ_[p]),
      IsUnit Q.det ∧ IsUnit P.det ∧
      M * Q.map (algebraMap ℚ ℚ_[p]) = P.map (algebraMap ℤ_[p] ℚ_[p])
```

### `Matrix.exists_specialLinearGroup_mul_upperTriangular`

`Thm_Matrix_exists_specialLinearGroup_mul_upperTriangular` — Hermite normal form for nonsingular integer 2×2 matrices

```lean
theorem Matrix.exists_specialLinearGroup_mul_upperTriangular (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) : ∃ (B : Matrix.SpecialLinearGroup (Fin 2) ℤ) (a b d : ℤ), 0 < a ∧ 0 ≤ b ∧ b < |d| ∧ a * d = M.det ∧ M = (B : Matrix (Fin 2) (Fin 2) ℤ) * !![a, b; 0, d]
```

### `Matrix.exists_submodule_addEquiv_zmod_pow_succ_of_addEquiv_zmod_pow`

`Thm_Matrix_exists_submodule_addEquiv_zmod_pow_succ_of_addEquiv_zmod_pow` — Lifting a left ideal of M₂(ℤ/ℓ^{e+1}) one step

```lean
theorem Matrix.exists_submodule_addEquiv_zmod_pow_succ_of_addEquiv_zmod_pow
    (ℓ : ℕ) [Fact ℓ.Prime] (e : ℕ)
    (I : Submodule (Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ (e + 1)))) (Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ (e + 1)))))
    (hI : Nonempty (↥I ≃+ (ZMod (ℓ ^ e) × ZMod (ℓ ^ e)))) :
    ∃ J : Submodule (Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ (e + 1)))) (Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ (e + 1)))),
      I ≤ J ∧ Nonempty (↥J ≃+ (ZMod (ℓ ^ (e + 1)) × ZMod (ℓ ^ (e + 1)))) ∧
      ∀ x ∈ J, (ℓ : Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ (e + 1)))) • x ∈ I
```

### `Matrix.exists_transpose_mul_mul_eq_J`

`Thm_Matrix_exists_transpose_mul_mul_eq_J` — Symplectic normal form for a unimodular alternating integer matrix

```lean
theorem Matrix.exists_transpose_mul_mul_eq_J {n : ℕ} (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ)
    (hQ : Q.transpose = -Q) (hdet : IsUnit Q.det) :
    ∃ P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ, IsUnit P.det ∧
      P.transpose * Q * P = Matrix.J (Fin n) ℤ
```

### `Matrix.exists_upperTriangular_pos_diag_mul_orthogonal_eq_of_det_ne_zero`

`Thm_Matrix_exists_upperTriangular_pos_diag_mul_orthogonal_eq_of_det_ne_zero` — Iwasawa decomposition of GLₙ(ℝ): A = b o

```lean
theorem Matrix.exists_upperTriangular_pos_diag_mul_orthogonal_eq_of_det_ne_zero
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) :
    ∃ b o : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j : Fin n, j < i → b i j = 0) ∧ (∀ i : Fin n, 0 < b i i) ∧
      (∀ i j : Fin n, ∑ a : Fin n, o a i * o a j = if i = j then 1 else 0) ∧ A = b * o
```

### `Matrix.finrank_ker_eq_one_and_iff_det_eq_zero_and_of_mul_eq_zero`

`Thm_Matrix_finrank_ker_eq_one_and_iff_det_eq_zero_and_of_mul_eq_zero` — Two eigenspaces of a 2× 2 matrix are lines iff both determinants vanish

```lean
theorem Matrix.finrank_ker_eq_one_and_iff_det_eq_zero_and_of_mul_eq_zero
    {K : Type} [Field K] (T : Matrix (Fin 2) (Fin 2) K) (a b : K)
    (hT : (T - a • (1 : Matrix (Fin 2) (Fin 2) K)) * (T - b • (1 : Matrix (Fin 2) (Fin 2) K)) = 0) (hab : a ≠ b) :
    (Module.finrank K (LinearMap.ker (Matrix.mulVecLin (T - a • (1 : Matrix (Fin 2) (Fin 2) K)))) = 1 ∧
      Module.finrank K (LinearMap.ker (Matrix.mulVecLin (T - b • (1 : Matrix (Fin 2) (Fin 2) K)))) = 1) ↔
    ((T - a • (1 : Matrix (Fin 2) (Fin 2) K)).det = 0 ∧ (T - b • (1 : Matrix (Fin 2) (Fin 2) K)).det = 0)
```

### `Matrix.finrank_linearMap_mul_card_sq_eq_finrank_mul_finrank`

`Thm_Matrix_finrank_linearMap_mul_card_sq_eq_finrank_mul_finrank` — Dimension form of Morita equivalence for Mₙ(k)

```lean
theorem Matrix.finrank_linearMap_mul_card_sq_eq_finrank_mul_finrank
    (k : Type u) [Field k] (ι : Type v) [Fintype ι] [DecidableEq ι]
    (V : Type w) (W : Type w') [AddCommGroup V] [Module k V] [Module (Matrix ι ι k) V]
    [IsScalarTower k (Matrix ι ι k) V]
    [AddCommGroup W] [Module k W] [Module (Matrix ι ι k) W] [IsScalarTower k (Matrix ι ι k) W]
    [FiniteDimensional k V] [FiniteDimensional k W] :
    Module.finrank k (V →ₗ[Matrix ι ι k] W) * Fintype.card ι ^ 2 =
      Module.finrank k V * Module.finrank k W
```

### `Matrix.finrank_range_and_eigenspace_of_adjoin_intCast`

`Thm_Matrix_finrank_range_and_eigenspace_of_adjoin_intCast` — Descent of idempotent-image and eigenspace ranks to a PID

```lean
theorem Matrix.finrank_range_and_eigenspace_of_adjoin_intCast
    {ι : Type*} (n d : ℕ) (M : ι → Matrix (Fin n) (Fin n) ℤ)
    (hfree : ∃ v : Fin d → (Fin n → ℂ), Function.Bijective
      (fun c : Fin d → ↥(Algebra.adjoin ℂ (Set.range fun i => (M i).map (Int.cast : ℤ → ℂ))) =>
        ∑ k, ((c k : Matrix (Fin n) (Fin n) ℂ).mulVec (v k))))
    (hmult : ∀ χ : ↥(Algebra.adjoin ℂ (Set.range fun i => (M i).map (Int.cast : ℤ → ℂ))) →ₐ[ℂ] ℂ,
      Module.finrank ℂ ↥(⨅ a : ↥(Algebra.adjoin ℂ (Set.range fun i => (M i).map (Int.cast : ℤ → ℂ))),
        Module.End.eigenspace (Matrix.toLin' (a : Matrix (Fin n) (Fin n) ℂ)) (χ a)) = d)
    (𝒪 : Type*) [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪] [CharZero 𝒪] :
    (∀ ε ∈ Algebra.adjoin 𝒪 (Set.range fun i => (M i).map (Int.cast : ℤ → 𝒪)),
      IsIdempotentElem ε →
        Module.finrank 𝒪 ↥(LinearMap.range (Matrix.toLin' ε)) =
          d * Module.finrank 𝒪 ↥(LinearMap.range (LinearMap.mulLeft 𝒪 ε ∘ₗ
            (Algebra.adjoin 𝒪 (Set.range fun i => (M i).map (Int.cast : ℤ → 𝒪))).val.toLinearMap))) ∧
    ∀ lam : ↥(Algebra.adjoin 𝒪 (Set.range fun i => (M i).map (Int.cast : ℤ → 𝒪))) →ₐ[𝒪] 𝒪,
      Module.finrank 𝒪 ↥(⨅ a : ↥(Algebra.adjoin 𝒪 (Set.range fun i => (M i).map (Int.cast : ℤ → 𝒪))),
        Module.End.eigenspace (Matrix.toLin' (a : Matrix (Fin n) (Fin n) 𝒪)) (lam a)) = d
```

### `Matrix.forall_iwahori_conj_mem_of_exists_iwahori_conj_not_mem`

`Thm_Matrix_forall_iwahori_conj_mem_of_exists_iwahori_conj_not_mem` — Iwahori conjugation by Y⁻¹ lands in M₂(ℤₚ)

```lean
theorem Matrix.forall_iwahori_conj_mem_of_exists_iwahori_conj_not_mem
    (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hpv : (p : 𝓞 ℚ) ∈ v.asIdeal)
    (Y Yi : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) (h1 : Y * Yi = 1) (h2 : Yi * Y = 1)
    (hY : ∀ i j, Y i j ∈ v.adicCompletionIntegers ℚ) (hY10 : (p : v.adicCompletion ℚ)⁻¹ * Y 1 0 ∈ v.adicCompletionIntegers ℚ)
    (hpYi : ∀ i j, ((p : v.adicCompletion ℚ) • Yi) i j ∈ v.adicCompletionIntegers ℚ)
    (hpYi10 : (p : v.adicCompletion ℚ)⁻¹ * ((p : v.adicCompletion ℚ) • Yi) 1 0 ∈ v.adicCompletionIntegers ℚ)
    (hYi : ¬ ((∀ i j, Yi i j ∈ v.adicCompletionIntegers ℚ) ∧ (p : v.adicCompletion ℚ)⁻¹ * Yi 1 0 ∈ v.adicCompletionIntegers ℚ))
    (hpY : ¬ ((∀ i j, ((p : v.adicCompletion ℚ)⁻¹ • Y) i j ∈ v.adicCompletionIntegers ℚ) ∧
      (p : v.adicCompletion ℚ)⁻¹ * ((p : v.adicCompletion ℚ)⁻¹ • Y) 1 0 ∈ v.adicCompletionIntegers ℚ))
    (hZ : ∃ Z : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ), (∀ i j, Z i j ∈ v.adicCompletionIntegers ℚ) ∧ (p : v.adicCompletion ℚ)⁻¹ * Z 1 0 ∈ v.adicCompletionIntegers ℚ ∧
      ¬ ∀ i j, (Y * Z * Yi) i j ∈ v.adicCompletionIntegers ℚ) :
    ∀ X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ), (∀ i j, X i j ∈ v.adicCompletionIntegers ℚ) →
      (p : v.adicCompletion ℚ)⁻¹ * X 1 0 ∈ v.adicCompletionIntegers ℚ →
      ∀ i j, (Yi * X * Y) i j ∈ v.adicCompletionIntegers ℚ
```

### `Matrix.hasDistinctRationalEigenvalues_of_isConj`

`Thm_Matrix_hasDistinctRationalEigenvalues_of_isConj` — Conjugation invariance of split distinct eigenvalues

```lean
theorem Matrix.hasDistinctRationalEigenvalues_of_isConj {R : Type*} [CommRing R]
    {M N : Matrix (Fin 2) (Fin 2) R} (h : IsConj M N)
    (hM : M.HasDistinctRationalEigenvalues) : N.HasDistinctRationalEigenvalues
```

### `Matrix.hasDistinctRationalEigenvalues_pow`

`Thm_Matrix_hasDistinctRationalEigenvalues_pow` — Coprime powers preserve distinct rational eigenvalues

```lean
theorem Matrix.hasDistinctRationalEigenvalues_pow {𝕜 : Type*} [Field 𝕜]
    {M : Matrix (Fin 2) (Fin 2) 𝕜} {d : ℕ} (hd : 0 < d) (hM : M ^ d = 1)
    (h : M.HasDistinctRationalEigenvalues) {k : ℕ} (hk : k.Coprime d) :
    (M ^ k).HasDistinctRationalEigenvalues
```

### `Matrix.isCompl_range_mulVecLin_and_invertible_of_trace_eq_one_of_det_eq_zero`

`Thm_Matrix_isCompl_range_mulVecLin_and_invertible_of_trace_eq_one_of_det_eq_zero` — Trace-one, determinant-zero 2×2 matrices are rank-one projectors

```lean
theorem Matrix.isCompl_range_mulVecLin_and_invertible_of_trace_eq_one_of_det_eq_zero
    {R : Type*} [CommRing R] (e : Matrix (Fin 2) (Fin 2) R) (htr : e.trace = 1) (hdet : e.det = 0) :
    e * e = e ∧
      IsCompl (LinearMap.range (Matrix.mulVecLin e)) (LinearMap.range (Matrix.mulVecLin (1 - e))) ∧
      Module.Invertible R ↥(LinearMap.range (Matrix.mulVecLin e)) ∧
      Module.Invertible R ↥(LinearMap.range (Matrix.mulVecLin (1 - e)))
```

### `Matrix.isUnit_and_padicValRat_inv_nonneg_of_not_dvd_det`

`Thm_Matrix_isUnit_and_padicValRat_inv_nonneg_of_not_dvd_det` — Integer matrix with determinant prime to p has p-integral inverse

```lean
theorem Matrix.isUnit_and_padicValRat_inv_nonneg_of_not_dvd_det {m : Type*} [Fintype m] [DecidableEq m]
    (p : ℕ) [Fact p.Prime] (M : Matrix m m ℤ) (hM : ¬ (p : ℤ) ∣ M.det) :
    IsUnit (M.map (Int.cast : ℤ → ℚ)) ∧
      ∀ i j, 0 ≤ padicValRat p ((M.map (Int.cast : ℤ → ℚ))⁻¹ i j)
```

### `Matrix.isUnit_det_padicInt_of_norm_sub_one_lt_one`

`Thm_Matrix_isUnit_det_padicInt_of_norm_sub_one_lt_one` — Matrices congruent to the identity over ℤₚ have unit determinant

```lean
theorem Matrix.isUnit_det_padicInt_of_norm_sub_one_lt_one
    (p : ℕ) [Fact p.Prime] (n : ℕ) (P : Matrix (Fin n) (Fin n) ℤ_[p])
    (h : ∀ i j, ‖P i j - (1 : Matrix (Fin n) (Fin n) ℤ_[p]) i j‖ < 1) :
    IsUnit P.det
```

### `Matrix.isUnit_of_isUnit_map_of_le_jacobson_bot`

`Thm_Matrix_isUnit_of_isUnit_map_of_le_jacobson_bot` — Matrices invertible modulo an ideal in the Jacobson radical

```lean
theorem Matrix.isUnit_of_isUnit_map_of_le_jacobson_bot
    {S : Type u} [CommRing S] {n : Type v} [Fintype n] [DecidableEq n]
    (𝔫 : Ideal S) (h𝔫 : 𝔫 ≤ (⊥ : Ideal S).jacobson)
    (A : Matrix n n S) (hA : IsUnit (A.map (Ideal.Quotient.mk 𝔫))) :
    IsUnit A
```

### `Matrix.mul_comm_of_forall_map_mulVec_mem_span_of_forall_exists_mulVec_not_mem_span`

`Thm_Matrix_mul_comm_of_forall_map_mulVec_mem_span_of_forall_exists_mulVec_not_mem_span` — Commutativity from a stable line only after base change

```lean
theorem Matrix.mul_comm_of_forall_map_mulVec_mem_span_of_forall_exists_mulVec_not_mem_span
    {F F' : Type*} [Field F] [Field F'] (e : F →+* F') {ι : Type*}
    (M : ι → Matrix (Fin 2) (Fin 2) F)
    (hirr : ∀ v : Fin 2 → F, v ≠ 0 → ∃ i, (M i).mulVec v ∉ F ∙ v)
    (u : Fin 2 → F') (hu : u ≠ 0) (hstab : ∀ i, ((M i).map e).mulVec u ∈ F' ∙ u) :
    ∀ i j, M i * M j = M j * M i
```

### `Matrix.natCard_GL_fin_two_zmod_eq`

`Thm_Matrix_natCard_GL_fin_two_zmod_eq` — Order of GL₂(ℤ/p)

```lean
theorem Matrix.natCard_GL_fin_two_zmod_eq (p : ℕ) [Fact p.Prime] :
    Nat.card (GL (Fin 2) (ZMod p)) = (p ^ 2 - 1) * (p ^ 2 - p)
```

### `Matrix.natCard_leftIdeal_ne_bot_ne_top_eq_and_inf_eq_bot`

`Thm_Matrix_natCard_leftIdeal_ne_bot_ne_top_eq_and_inf_eq_bot` — The ℓ+1 proper left ideals of M₂(𝔽_ℓ)

```lean
theorem Matrix.natCard_leftIdeal_ne_bot_ne_top_eq_and_inf_eq_bot
    (ℓ : ℕ) [Fact ℓ.Prime] :
    Nat.card {I : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) // I ≠ ⊥ ∧ I ≠ ⊤} = ℓ + 1 ∧
    ∀ I I' : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ)),
      I ≠ ⊥ → I ≠ ⊤ → I' ≠ ⊥ → I' ≠ ⊤ → I ≠ I' → I ⊓ I' = ⊥
```

### `Matrix.nonempty_linearEquiv_self_of_natCard_eq_pow_four`

`Thm_Matrix_nonempty_linearEquiv_self_of_natCard_eq_pow_four` — A module of order ℓ⁴ over M₂(mathbb F_ℓ) is free of rank one

```lean
theorem Matrix.nonempty_linearEquiv_self_of_natCard_eq_pow_four
    (ℓ : ℕ) [Fact ℓ.Prime] (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] [Finite V]
    (hV : Nat.card V = ℓ ^ 4) :
    Nonempty (V ≃ₗ[Matrix (Fin 2) (Fin 2) (ZMod ℓ)] Matrix (Fin 2) (Fin 2) (ZMod ℓ))
```

### `Matrix.nonempty_linearEquiv_self_of_natCard_eq_pow_of_natCard_torsionBy`

`Thm_Matrix_nonempty_linearEquiv_self_of_natCard_eq_pow_of_natCard_torsionBy` — Finite M₂(ℤ/ℓ^m)-modules with free torsion counts are free of rank one

```lean
theorem Matrix.nonempty_linearEquiv_self_of_natCard_eq_pow_of_natCard_torsionBy
    (ℓ : ℕ) [Fact ℓ.Prime] (m : ℕ) [NeZero m]
    (V : Type u) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ m))) V] [Finite V]
    (hV : ∀ j ≤ m, Nat.card {v : V // ℓ ^ j • v = 0} = ℓ ^ (4 * j)) :
    Nonempty (V ≃ₗ[Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ m))] Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ m)))
```

### `Matrix.pow_five_eq_one_of_trace_sq_add_trace_sub_one`

`Thm_Matrix_pow_five_eq_one_of_trace_sq_add_trace_sub_one` — Trace criterion for g⁵=1 in SL₂(R)

```lean
theorem Matrix.pow_five_eq_one_of_trace_sq_add_trace_sub_one {R : Type*} [CommRing R] (g : Matrix (Fin 2) (Fin 2) R) (hdet : g.det = 1) (ht : g.trace ^ 2 + g.trace - 1 = 0) : g ^ 5 = 1
```

### `Matrix.span_eq_top_of_map_span_eq_top`

`Thm_Matrix_span_eq_top_of_map_span_eq_top` — Spanning sets of Mₙ(A) lift from the residue field

```lean
theorem Matrix.span_eq_top_of_map_span_eq_top
    {n : Type*} [Fintype n] [DecidableEq n] {A : Type*} [CommRing A] [IsLocalRing A]
    {k : Type*} [Field k] (π : A →+* k) (hπ : Function.Surjective π) {S : Set (Matrix n n A)}
    (hS : Submodule.span k ((fun X : Matrix n n A => X.map π) '' S) = ⊤) :
    Submodule.span A S = ⊤
```

### `Matrix.span_image_map_eq_top_of_span_eq_top`

`Thm_Matrix_span_image_map_eq_top_of_span_eq_top` — Spanning sets of Mₙ(k) span Mₙ(K) after base change

```lean
theorem Matrix.span_image_map_eq_top_of_span_eq_top
    {n : Type*} [Fintype n] [DecidableEq n]
    {k : Type*} [Field k] {K : Type*} [Field K] (f : k →+* K)
    {S : Set (Matrix n n k)} (hS : Submodule.span k S = ⊤) :
    Submodule.span K ((fun X : Matrix n n k => X.map f) '' S) = ⊤
```

### `Matrix.span_range_map_eq_top_of_exists_odd_of_forall_exists_mulVec_ne_smul`

`Thm_Matrix_span_range_map_eq_top_of_exists_odd_of_forall_exists_mulVec_ne_smul` — Odd irreducible two-dimensional representations span M₂ after base change

```lean
theorem Matrix.span_range_map_eq_top_of_exists_odd_of_forall_exists_mulVec_ne_smul
    {G : Type*} [Group G] {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    (ρ : G →* Matrix (Fin 2) (Fin 2) F)
    (hodd : ∃ c : G, ρ c * ρ c = 1 ∧ (ρ c).det = -1)
    (hirr : ∀ v : Fin 2 → F, v ≠ 0 → ∃ σ : G, ∀ c : F, (ρ σ).mulVec v ≠ c • v)
    {k : Type*} [Field k] (ι : F →+* k) :
    Submodule.span k (Set.range fun g : G => (ρ g).map ι) = ⊤
```

### `Matrix.specialUnitaryGroup_fin_two_eq_diag_mul_rotation_mul_diag`

`Thm_Matrix_specialUnitaryGroup_fin_two_eq_diag_mul_rotation_mul_diag` — Euler angle decomposition for SU(2)

```lean
theorem Matrix.specialUnitaryGroup_fin_two_eq_diag_mul_rotation_mul_diag
    (k : Matrix (Fin 2) (Fin 2) ℂ) (hk : k ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ∃ a b c : ℝ,
      k = !![Complex.exp (a * Complex.I), 0; 0, Complex.exp (-(a * Complex.I))] *
            !![(Real.cos b : ℂ), -(Real.sin b : ℂ); (Real.sin b : ℂ), (Real.cos b : ℂ)] *
            !![Complex.exp (c * Complex.I), 0; 0, Complex.exp (-(c * Complex.I))]
```

### `Matrix.sub_smul_one_mul_sub_smul_one_eq_zero`

`Thm_Matrix_sub_smul_one_mul_sub_smul_one_eq_zero` — Factored Cayley–Hamilton identity for 2×2 matrices

```lean
theorem Matrix.sub_smul_one_mul_sub_smul_one_eq_zero {A : Type*} [CommRing A]
    {M : Matrix (Fin 2) (Fin 2) A} {a b : A}
    (htr : M.trace = a + b) (hdet : M.det = a * b) :
    (M - a • (1 : Matrix (Fin 2) (Fin 2) A)) * (M - b • (1 : Matrix (Fin 2) (Fin 2) A)) = 0
```

### `Matrix.sum_apply_conj_single_eq_sum_apply_single`

`Thm_Matrix_sum_apply_conj_single_eq_sum_apply_single` — Conjugation invariance of the quadratic and cubic trace tensors of mathfrakgl₃

```lean
theorem Matrix.sum_apply_conj_single_eq_sum_apply_single
    {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    (C : Matrix (Fin 3) (Fin 3) K) (hC : C.det ≠ 0)
    (β : Matrix (Fin 3) (Fin 3) K →ₗ[K] Matrix (Fin 3) (Fin 3) K →ₗ[K] V)
    (τ : Matrix (Fin 3) (Fin 3) K →ₗ[K] Matrix (Fin 3) (Fin 3) K →ₗ[K] Matrix (Fin 3) (Fin 3) K →ₗ[K] V) :
    (∑ i : Fin 3, ∑ j : Fin 3, β (C * Matrix.single i j 1 * C⁻¹) (C * Matrix.single j i 1 * C⁻¹)
      = ∑ i : Fin 3, ∑ j : Fin 3, β (Matrix.single i j 1) (Matrix.single j i 1)) ∧
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        τ (C * Matrix.single i j 1 * C⁻¹) (C * Matrix.single j k 1 * C⁻¹) (C * Matrix.single k i 1 * C⁻¹)
      = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        τ (Matrix.single i j 1) (Matrix.single j k 1) (Matrix.single k i 1))
```

### `Matrix.trace_pow_eq_of_trace_eq_of_det_eq`

`Thm_Matrix_trace_pow_eq_of_trace_eq_of_det_eq` — Equal trace and determinant give equal traces of all powers

```lean
theorem Matrix.trace_pow_eq_of_trace_eq_of_det_eq {R : Type*} [CommRing R]
    {M N : Matrix (Fin 2) (Fin 2) R} (htr : M.trace = N.trace) (hdet : M.det = N.det)
    (k : ℕ) : (M ^ k).trace = (N ^ k).trace
```

### `Matrix.trace_pow_eq_sum_pow`

`Thm_Matrix_trace_pow_eq_sum_pow` — Trace of powers of a 2×2 matrix as a power sum

```lean
theorem Matrix.trace_pow_eq_sum_pow {R : Type*} [CommRing R]
    {M : Matrix (Fin 2) (Fin 2) R} {α β : R}
    (htr : M.trace = α + β) (hdet : M.det = α * β) (k : ℕ) :
    (M ^ k).trace = α ^ k + β ^ k
```

## Polynomial (67)

### `Polynomial.Chebyshev.eq_zero_on_Ioo_of_forall_intervalIntegral_mul_U_eq_zero`

`Thm_Polynomial_Chebyshev_eq_zero_on_Ioo_of_forall_intervalIntegral_mul_U_eq_zero` — Completeness of the Chebyshev polynomials Uⱼ on (0,π)

```lean
theorem Polynomial.Chebyshev.eq_zero_on_Ioo_of_forall_intervalIntegral_mul_U_eq_zero
    (g : ℝ → ℂ) (hg : ContinuousOn g (Set.Ioo 0 Real.pi))
    (hgi : IntervalIntegrable g MeasureTheory.volume 0 Real.pi)
    (hmodes : ∀ j : ℕ,
      ∫ θ in (0 : ℝ)..Real.pi, g θ * (((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) : ℂ) = 0) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, g θ = 0
```

### `Polynomial.Monic.map_roots_eq_of_map_eq_kroneckerFibre`

`Thm_Polynomial_Monic_map_roots_eq_of_map_eq_kroneckerFibre` — Reduced roots of a monic lift of (a^q-X)(a-X^q)

```lean
theorem Polynomial.Monic.map_roots_eq_of_map_eq_kroneckerFibre
    {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {k : Type*} [Field k] (q : ℕ) [Fact q.Prime] [CharP k q]
    (red : A →+* k) (r : L → k) (hr : ∀ a : A, r a = red a)
    {P : Polynomial A} (hP : P.Monic) (a b : k) (hb : b ^ q = a)
    (hred : P.map red = (Polynomial.C (a ^ q) - Polynomial.X) * (Polynomial.C a - Polynomial.X ^ q)) :
    ((P.map (algebraMap A L)).roots).map r = {a ^ q} + q • ({b} : Multiset k)
```

### `Polynomial.X_pow_sub_C_irreducible_of_isCoprime_apply`

`Thm_Polynomial_X_pow_sub_C_irreducible_of_isCoprime_apply` — Irreducibility of Xⁿ - a via a coprime valuation

```lean
theorem Polynomial.X_pow_sub_C_irreducible_of_isCoprime_apply
    {F : Type*} [Field F] (v : F → ℤ) (hv : ∀ x y : F, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y)
    {n : ℕ} (hn : 0 < n) {a : F} (ha : a ≠ 0) (hcop : IsCoprime (v a) n) :
    Irreducible (X ^ n - C a)
```

### `Polynomial.abv_coeff_mul_pow_le_of_evalEval_C_add_X_eq_zero`

`Thm_Polynomial_abv_coeff_mul_pow_le_of_evalEval_C_add_X_eq_zero` — Coefficient bounds for a formal branch through a simple point

```lean
theorem Polynomial.abv_coeff_mul_pow_le_of_evalEval_C_add_X_eq_zero
    {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ)
    (G : Polynomial (Polynomial K)) (hG : ∀ i j, μ ((G.coeff i).coeff j) ≤ 1)
    (z₀ y₀ : K) (hz : μ z₀ ≤ 1) (hy : μ y₀ ≤ 1)
    (hsep : (Polynomial.derivative G).evalEval z₀ y₀ ≠ 0)
    (Y : PowerSeries K) (hY0 : PowerSeries.constantCoeff Y = y₀)
    (hY : (G.map (Polynomial.mapRingHom (algebraMap K (PowerSeries K)))).evalEval
        (PowerSeries.C z₀ + PowerSeries.X) Y = 0)
    (n : ℕ) (hn : 1 ≤ n) :
    μ (PowerSeries.coeff n Y) * μ ((Polynomial.derivative G).evalEval z₀ y₀) ^ (2 * n)
      ≤ μ ((Polynomial.derivative G).evalEval z₀ y₀)
```

### `Polynomial.abv_eval_le_gaussNorm`

`Thm_Polynomial_abv_eval_le_gaussNorm` — Polynomials are bounded by their Gauss norm on a disc

```lean
theorem Polynomial.abv_eval_le_gaussNorm {R : Type*} [CommRing R] (v : AbsoluteValue R ℝ)
    (hv : IsNonarchimedean v) {c : ℝ} (hc : 0 ≤ c) (p : R[X]) {z : R} (hz : v z ≤ c) :
    v (p.eval z) ≤ p.gaussNorm v c
```

### `Polynomial.aeval_eq_zero_of_forall_pos_aeval_sum_pow_smul_eq_zero`

`Thm_Polynomial_aeval_eq_zero_of_forall_pos_aeval_sum_pow_smul_eq_zero` — Annihilating polynomial passes to the constant term

```lean
theorem Polynomial.aeval_eq_zero_of_forall_pos_aeval_sum_pow_smul_eq_zero
    (R D : ℕ) (N : Fin (D + 1) → Matrix (Fin R) (Fin R) ℂ) (q : Polynomial ℂ)
    (h : ∀ y : ℝ, 0 < y → Polynomial.aeval (∑ a : Fin (D + 1), ((y : ℂ) ^ (a : ℕ)) • N a) q = 0) :
    Polynomial.aeval (N 0) q = 0
```

### `Polynomial.aeval_notMem_of_height_eq_one_of_map_residue_ne_zero`

`Thm_Polynomial_aeval_notMem_of_height_eq_one_of_map_residue_ne_zero` — Height-one vertical primes avoid polynomials with non-zero reduction

```lean
theorem Polynomial.aeval_notMem_of_height_eq_one_of_map_residue_ne_zero
    {A C : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing C] [IsDomain C] [Algebra A C]
    (x : C) (hx : Function.Injective (Polynomial.aeval (R := A) x))
    (hint : (Polynomial.aeval (R := A) x).toRingHom.IsIntegral)
    (Q : Ideal C) [Q.IsPrime] (hQ : Q.height = 1)
    (hQm : (IsLocalRing.maximalIdeal A).map (algebraMap A C) ≤ Q)
    (P : Polynomial A) (hP : P.map (IsLocalRing.residue A) ≠ 0) :
    Polynomial.aeval x P ∉ Q
```

### `Polynomial.aeval_pow_card_eq_pow_card`

`Thm_Polynomial_aeval_pow_card_eq_pow_card` — q-power map commutes with polynomial evaluation over 𝔽_q

```lean
theorem Polynomial.aeval_pow_card_eq_pow_card
    (F : Type) [Field F] [Fintype F] (E : Type) [CommRing E] [Algebra F E] (p : F[X]) (x : E) :
    Polynomial.aeval (x ^ Fintype.card F) p = (Polynomial.aeval x p) ^ Fintype.card F
```

### `Polynomial.coeff_countP_roots_isDominant_of_isAlgClosed`

`Thm_Polynomial_coeff_countP_roots_isDominant_of_isAlgClosed` — Coefficients of maximal valuation count roots in the unit disc

```lean
theorem Polynomial.coeff_countP_roots_isDominant_of_isAlgClosed
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (p : Polynomial K) (hp : p ≠ 0) :
    ((∀ j : ℕ, Valued.v (p.coeff j) ≤ Valued.v (p.coeff (p.roots.countP fun α => Valued.v α ≤ 1))) ∧
      ∀ j : ℕ, (p.roots.countP fun α => Valued.v α ≤ 1) < j →
        Valued.v (p.coeff j) < Valued.v (p.coeff (p.roots.countP fun α => Valued.v α ≤ 1))) ∧
    ((∀ j : ℕ, Valued.v (p.coeff j) ≤ Valued.v (p.coeff (p.roots.countP fun α => Valued.v α < 1))) ∧
      ∀ j : ℕ, j < (p.roots.countP fun α => Valued.v α < 1) →
        Valued.v (p.coeff j) < Valued.v (p.coeff (p.roots.countP fun α => Valued.v α < 1)))
```

### `Polynomial.dvd_of_monic_of_map_eq_prod_X_sub_C_of_forall_eval_eq_zero`

`Thm_Polynomial_dvd_of_monic_of_map_eq_prod_X_sub_C_of_forall_eval_eq_zero` — Monic polynomial with separated roots divides any common vanishing polynomial

```lean
theorem Polynomial.dvd_of_monic_of_map_eq_prod_X_sub_C_of_forall_eval_eq_zero
    {T : Type u} {S : Type v} [CommRing T] [CommRing S] (f : T →+* S) (hf : Function.Injective f)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (h : Polynomial T) (hh : h.Monic) (r : ι → S)
    (hsplit : h.map f = ∏ i, (Polynomial.X - Polynomial.C (r i)))
    (hsep : ∀ i j, i ≠ j → IsUnit (r i - r j))
    (F : Polynomial T) (hF : ∀ i, (F.map f).eval (r i) = 0) :
    h ∣ F
```

### `Polynomial.eq_of_abv_sub_lt_abv_derivative_eval`

`Thm_Polynomial_eq_of_abv_sub_lt_abv_derivative_eval` — Uniqueness of roots within μ(g'(a)) (non-archimedean)

```lean
theorem Polynomial.eq_of_abv_sub_lt_abv_derivative_eval
    {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ)
    (g : Polynomial K) (hg : ∀ i, μ (g.coeff i) ≤ 1) {a b : K} (ha : μ a ≤ 1) (hb : μ b ≤ 1)
    (hga : g.eval a = 0) (hgb : g.eval b = 0)
    (hlt : μ (a - b) < μ ((Polynomial.derivative g).eval a)) : a = b
```

### `Polynomial.eq_of_forall_abs_resultant_X_pow_add_C_le`

`Thm_Polynomial_eq_of_forall_abs_resultant_X_pow_add_C_le` — Monic rational polynomials determined by resultant inequalities

```lean
theorem Polynomial.eq_of_forall_abs_resultant_X_pow_add_C_le (P Q : Polynomial ℚ)
    (hP : P.Monic) (hQ : Q.Monic) (hdeg : P.natDegree = Q.natDegree)
    (S : Set ℤ) (hS₁ : ∀ b : ℤ, ∃ c ∈ S, b ≤ c) (hS₂ : ∀ b : ℤ, ∃ c ∈ S, c ≤ b)
    (h : ∀ n : ℕ, 0 < n → ∀ c ∈ S,
      (Polynomial.X ^ n + Polynomial.C (c : ℚ) : Polynomial ℚ).resultant P ≠ 0 →
        |(Polynomial.X ^ n + Polynomial.C (c : ℚ) : Polynomial ℚ).resultant Q| ≤
          |(Polynomial.X ^ n + Polynomial.C (c : ℚ) : Polynomial ℚ).resultant P|) :
    P = Q
```

### `Polynomial.eq_of_forall_natAbs_resultant_X_pow_add_C_le`

`Thm_Polynomial_eq_of_forall_natAbs_resultant_X_pow_add_C_le` — Monic integer polynomials determined by resultant inequalities

```lean
theorem Polynomial.eq_of_forall_natAbs_resultant_X_pow_add_C_le (P Q : Polynomial ℤ)
    (hP : P.Monic) (hQ : Q.Monic) (hdeg : P.natDegree = Q.natDegree)
    (S : Set ℤ) (hS₁ : ∀ b : ℤ, ∃ c ∈ S, b ≤ c) (hS₂ : ∀ b : ℤ, ∃ c ∈ S, c ≤ b)
    (h : ∀ n : ℕ, 0 < n → ∀ c ∈ S,
      (Polynomial.X ^ n + Polynomial.C c : Polynomial ℤ).resultant P ≠ 0 →
        ((Polynomial.X ^ n + Polynomial.C c : Polynomial ℤ).resultant Q).natAbs ≤
          ((Polynomial.X ^ n + Polynomial.C c : Polynomial ℤ).resultant P).natAbs) :
    P = Q
```

### `Polynomial.eq_of_forall_sum_roots_pow_eq`

`Thm_Polynomial_eq_of_forall_sum_roots_pow_eq` — Monic split polynomials are determined by power sums of roots

```lean
theorem Polynomial.eq_of_forall_sum_roots_pow_eq {K : Type*} [Field K] [CharZero K]
    (P Q : Polynomial K) (hP : P.Monic) (hQ : Q.Monic) (hPs : P.Splits) (hQs : Q.Splits)
    (hdeg : P.natDegree = Q.natDegree)
    (h : ∀ n : ℕ, 0 < n →
      (P.roots.map (fun z => z ^ n)).sum = (Q.roots.map (fun z => z ^ n)).sum) :
    P = Q
```

### `Polynomial.eq_one_or_eq_neg_one_of_map_eq_C_mul_X_add_C_pow`

`Thm_Polynomial_eq_one_or_eq_neg_one_of_map_eq_C_mul_X_add_C_pow` — Rationality forces r=±1 for ℓ-adic linear factors

```lean
theorem Polynomial.eq_one_or_eq_neg_one_of_map_eq_C_mul_X_add_C_pow
    (ℓ : ℕ) [Fact ℓ.Prime] (g : ℕ) (hg : 1 ≤ g) (P : ℚ[X]) (a : ℚ) (ha : a = 1 ∨ a = -1)
    (h0 : P.coeff 0 = 1 ∨ P.coeff 0 = -1) (r : ℚ_[ℓ])
    (hP : P.map (algebraMap ℚ ℚ_[ℓ]) = C (algebraMap ℚ ℚ_[ℓ] a) * (X + C r) ^ g) :
    r = 1 ∨ r = -1
```

### `Polynomial.eq_sq_of_mul_comp_neg_X_sub_C_eq_pow_four_of_irreducible`

`Thm_Polynomial_eq_sq_of_mul_comp_neg_X_sub_C_eq_pow_four_of_irreducible` — A quartic functional equation forces P = N²

```lean
theorem Polynomial.eq_sq_of_mul_comp_neg_X_sub_C_eq_pow_four_of_irreducible
    (t n : ℤ) (P : Polynomial ℚ)
    (hirr : Irreducible (X ^ 2 + C (t : ℚ) * X + C (n : ℚ) : Polynomial ℚ))
    (hP : P.natDegree ≤ 4)
    (hPQ : P * P.comp (-X - C (t : ℚ)) = (X ^ 2 + C (t : ℚ) * X + C (n : ℚ)) ^ 4)
    (hpos : ∃ m : ℤ, 0 < P.eval (m : ℚ)) :
    P = (X ^ 2 + C (t : ℚ) * X + C (n : ℚ)) ^ 2
```

### `Polynomial.existsUnique_constantCoeff_eq_and_evalEval_C_add_X_eq_zero`

`Thm_Polynomial_existsUnique_constantCoeff_eq_and_evalEval_C_add_X_eq_zero` — Formal branch through a simple point of a plane curve

```lean
theorem Polynomial.existsUnique_constantCoeff_eq_and_evalEval_C_add_X_eq_zero
    {K : Type*} [Field K] (G : Polynomial (Polynomial K)) (z₀ y₀ : K)
    (h0 : G.evalEval z₀ y₀ = 0) (hsep : (Polynomial.derivative G).evalEval z₀ y₀ ≠ 0) :
    ∃! Y : PowerSeries K, PowerSeries.constantCoeff Y = y₀ ∧
      (G.map (Polynomial.mapRingHom (algebraMap K (PowerSeries K)))).evalEval
        (PowerSeries.C z₀ + PowerSeries.X) Y = 0
```

### `Polynomial.existsUnique_monic_map_eq_dvd_of_isCoprime_of_ker_pow_eq_bot`

`Thm_Polynomial_existsUnique_monic_map_eq_dvd_of_isCoprime_of_ker_pow_eq_bot` — Hensel lifting of a monic coprime factor along a nilpotent thickening

```lean
theorem Polynomial.existsUnique_monic_map_eq_dvd_of_isCoprime_of_ker_pow_eq_bot
    {T T' : Type u} [CommRing T] [CommRing T'] (π : T →+* T') (hπ : Function.Surjective π)
    (hnil : ∃ n : ℕ, RingHom.ker π ^ n = ⊥)
    (f : Polynomial T) (g' k' : Polynomial T') (hg' : g'.Monic) (hcop : IsCoprime g' k')
    (hfac : f.map π = g' * k') :
    ∃! g : Polynomial T, g.Monic ∧ g.map π = g' ∧ g ∣ f
```

### `Polynomial.exists_approximants_at_infty`

`Thm_Polynomial_exists_approximants_at_infty` — Truncated factorisation at infinity of a weighted polynomial

```lean
theorem Polynomial.exists_approximants_at_infty {K : Type*} [Field K] (n w : ℕ) (F : Polynomial (Polynomial K)) (hF : F.natDegree ≤ n) (hwt : ∀ k j : ℕ, w * (n - k) < j → (F.coeff k).coeff j = 0) (c : K) (hlead : F.coeff n = C c) (r : Fin n → K) (hr : Function.Injective r) (h0 : ∀ i, (∑ k ∈ Finset.range (n + 1), C ((F.coeff k).coeff (w * (n - k))) * X ^ k).eval (r i) = 0) (h1 : ∀ i, (derivative (∑ k ∈ Finset.range (n + 1), C ((F.coeff k).coeff (w * (n - k))) * X ^ k)).eval (r i) ≠ 0) : ∃ P : Fin n → Polynomial K, (∀ i, (P i).natDegree ≤ w) ∧ (∀ i, (P i).coeff w = r i) ∧ ∀ k j : ℕ, w * (n - k) ≤ j + w → ((F - C (C c) * ∏ i, (X - C (P i))).coeff k).coeff j = 0
```

### `Polynomial.exists_branch_near_root`

`Thm_Polynomial_exists_branch_near_root` — Roots of large specialisations lie near a branch

```lean
theorem Polynomial.exists_branch_near_root {n w : ℕ} (F : Polynomial (Polynomial ℂ)) (hF : F.natDegree ≤ n) (hwt : ∀ k j : ℕ, w * (n - k) < j → (F.coeff k).coeff j = 0) (c : ℂ) (hc : c ≠ 0) (hlead : F.coeff n = C c) (P : Fin n → Polynomial ℂ) (hP : ∀ i, (P i).natDegree ≤ w) (hPinj : Function.Injective fun i => (P i).coeff w) (hR : ∀ k j : ℕ, w * (n - k) ≤ j + w → ((F - C (C c) * ∏ i, (X - C (P i))).coeff k).coeff j = 0) : ∃ C₀ T : ℝ, 0 < C₀ ∧ ∀ t : ℂ, T ≤ ‖t‖ → ∀ x : ℂ, (F.map (Polynomial.evalRingHom t)).IsRoot x → ∃ i, ‖x - (P i).eval t‖ ≤ C₀ / ‖t‖
```

### `Polynomial.exists_coeff_eval_sum_monomial_eq_zero_of_isUnit_derivative`

`Thm_Polynomial_exists_coeff_eval_sum_monomial_eq_zero_of_isUnit_derivative` — Truncated Newton jets with unit derivative

```lean
theorem Polynomial.exists_coeff_eval_sum_monomial_eq_zero_of_isUnit_derivative
    {A : Type*} [CommRing A] (F : Polynomial (Polynomial A)) (w₀ : A)
    (h0 : (F.eval (Polynomial.C w₀)).coeff 0 = 0)
    (hder : IsUnit ((F.derivative.eval (Polynomial.C w₀)).coeff 0)) (m : ℕ) :
    ∃ w : Fin (m + 1) → A, w 0 = w₀ ∧
      ∀ r : Fin (m + 1), (F.eval (∑ r' : Fin (m + 1), Polynomial.monomial (r' : ℕ) (w r'))).coeff r = 0
```

### `Polynomial.exists_coeff_sum_monomial_mul_sub_one_eq_zero_of_isUnit_coeff_zero`

`Thm_Polynomial_exists_coeff_sum_monomial_mul_sub_one_eq_zero_of_isUnit_coeff_zero` — Truncated inverse of a polynomial with unit constant term

```lean
theorem Polynomial.exists_coeff_sum_monomial_mul_sub_one_eq_zero_of_isUnit_coeff_zero
    {A : Type*} [CommRing A] (s : Polynomial A) (hs : IsUnit (s.coeff 0)) (m : ℕ) :
    ∃ σ : Fin (m + 1) → A,
      ∀ r : Fin (m + 1), ((∑ r' : Fin (m + 1), Polynomial.monomial (r' : ℕ) (σ r')) * s - 1).coeff r = 0
```

### `Polynomial.exists_eval_eq_coeff_zero_add_pow_mul`

`Thm_Polynomial_exists_eval_eq_coeff_zero_add_pow_mul` — Polynomial values along t = N^K m are N-adically close to p(0)

```lean
theorem Polynomial.exists_eval_eq_coeff_zero_add_pow_mul (p : Polynomial ℚ) (N : ℤ) (hN : N ≠ 0) (hden : ∀ k : ℕ, ∀ q : ℕ, q.Prime → q ∣ (p.coeff k).den → (q : ℤ) ∣ N) : ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ m : ℤ, ∃ z : ℤ, p.eval ((N : ℚ) ^ K * m) = p.coeff 0 + (N : ℚ) ^ (K - K₀) * z
```

### `Polynomial.exists_eval_mul_cpow_mul_eval_eq_of_ne_zero`

`Thm_Polynomial_exists_eval_mul_cpow_mul_eval_eq_of_ne_zero` — Clearing denominators for a ratio of q^s-rational functions

```lean
theorem Polynomial.exists_eval_mul_cpow_mul_eval_eq_of_ne_zero
    (q : ℂ) (hq : q ≠ 0) (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (hP : P ≠ 0) (hQd : Qd ≠ 0) :
    ∃ (R₁ R₂ : Polynomial ℂ) (r : ℤ), R₂ ≠ 0 ∧
      ∀ s : ℂ,
        R₂.eval (q ^ s) * (q ^ ((md : ℂ) * s) * Pd.eval (q ^ (-s))) * Q.eval (q ^ s) =
          (R₁.eval (q ^ s) * q ^ ((r : ℂ) * s)) * (q ^ ((m : ℂ) * (-s)) * P.eval (q ^ s)) * Qd.eval (q ^ (-s))
```

### `Polynomial.exists_factorization_resultant_X_pow_sub_one_eq_mul_add_of_not_dvd`

`Thm_Polynomial_exists_factorization_resultant_X_pow_sub_one_eq_mul_add_of_not_dvd` — Lifting the exponent for Res(Xⁿ-1,P) along ℓ-power multiples

```lean
theorem Polynomial.exists_factorization_resultant_X_pow_sub_one_eq_mul_add_of_not_dvd
    (P : Polynomial ℤ) (hP : P.Monic) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : ¬ ((ℓ : ℤ) ∣ P.coeff 0))
    (hres : ∀ n : ℕ, 0 < n → (Polynomial.X ^ n - 1 : Polynomial ℤ).resultant P ≠ 0) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∃ c : ℕ, ∀ j : ℕ, 0 < j → ¬ ℓ ∣ j → ∀ k : ℕ,
        ((Polynomial.X ^ (m₀ * j * ℓ ^ k) - 1 : Polynomial ℤ).resultant P).natAbs.factorization ℓ =
          P.natDegree * k + c
```

### `Polynomial.exists_forall_not_isRoot_of_weighted`

`Thm_Polynomial_exists_forall_not_isRoot_of_weighted` — Rootless integral specialisations of a weighted polynomial

```lean
theorem Polynomial.exists_forall_not_isRoot_of_weighted (n w : ℕ) (F : Polynomial (Polynomial ℚ)) (hF : F.natDegree ≤ n) (hwt : ∀ k j : ℕ, w * (n - k) < j → (F.coeff k).coeff j = 0) (hlead : (F.coeff n).coeff 0 ≠ 0) (hsep : (∑ k ∈ Finset.range (n + 1), C ((F.coeff k).coeff (w * (n - k))) * X ^ k : Polynomial ℚ).Separable) (hroot : ∀ g : Polynomial ℚ, F.eval g ≠ 0) (M : ℕ) (hM : M ≠ 0) (m₀ : ℕ) : ∃ m : ℕ, m₀ ≤ m ∧ ∀ x : ℚ, ¬ (F.map (Polynomial.evalRingHom ((M : ℚ) * m))).IsRoot x
```

### `Polynomial.exists_isDiscreteValuationRing_algebra_adjoin_eq_top_forall_exists_algHom_map_eq_one_sub_of_sum_range_pow_eq_zero`

`Thm_Polynomial_exists_isDiscreteValuationRing_algebra_adjoin_eq_top_forall_exists_algHom_map_eq_one_sub_of_sum_range_pow_eq_zero` — A universal cyclotomic discrete valuation ring over Z₀

```lean
theorem Polynomial.exists_isDiscreteValuationRing_algebra_adjoin_eq_top_forall_exists_algHom_map_eq_one_sub_of_sum_range_pow_eq_zero
    (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q)
    (Z₀ : Type) [CommRing Z₀] [IsDomain Z₀] [IsDiscreteValuationRing Z₀]
    (hZ₀ : maximalIdeal Z₀ = Ideal.span {(q : Z₀)}) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra Z₀ V)
      (_ : Module.Finite Z₀ V) (_ : Module.Free Z₀ V)
      (_ : Finite (ResidueField Z₀) → Finite (ResidueField V))
      (ϖ : V) (_ : maximalIdeal V = Ideal.span {ϖ}) (_ : Algebra.adjoin Z₀ {ϖ} = ⊤)
      (ε : V) (_ : IsUnit ε) (_ : ϖ ^ (q - 1) = ε * (q : V))
      (_ : ∑ i ∈ Finset.range q, (1 - ϖ) ^ i = 0),
      ∀ (R : Type) [CommRing R] [Algebra Z₀ R] (ζ : R), ∑ i ∈ Finset.range q, ζ ^ i = 0 →
        ∃ ι : V →ₐ[Z₀] R, ι ϖ = 1 - ζ
```

### `Polynomial.exists_isDiscreteValuationRing_algebra_adjoin_eq_top_forall_exists_algHom_map_eq_one_sub_of_sum_range_pow_eq_zero_of_prime`

`Thm_Polynomial_exists_isDiscreteValuationRing_algebra_adjoin_eq_top_forall_exists_algHom_map_eq_one_sub_of_sum_range_pow_eq_zero_of_prime` — Cyclotomic extension with uniformiser 1-ζ_q, all primes q

```lean
theorem Polynomial.exists_isDiscreteValuationRing_algebra_adjoin_eq_top_forall_exists_algHom_map_eq_one_sub_of_sum_range_pow_eq_zero_of_prime
    (q : ℕ) [Fact q.Prime]
    (Z₀ : Type) [CommRing Z₀] [IsDomain Z₀] [IsDiscreteValuationRing Z₀]
    (hZ₀ : maximalIdeal Z₀ = Ideal.span {(q : Z₀)}) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra Z₀ V)
      (_ : Module.Finite Z₀ V) (_ : Module.Free Z₀ V)
      (_ : Finite (ResidueField Z₀) → Finite (ResidueField V))
      (ϖ : V) (_ : maximalIdeal V = Ideal.span {ϖ}) (_ : Algebra.adjoin Z₀ {ϖ} = ⊤)
      (ε : V) (_ : IsUnit ε) (_ : ϖ ^ (q - 1) = ε * (q : V))
      (_ : ∑ i ∈ Finset.range q, (1 - ϖ) ^ i = 0),
      ∀ (R : Type) [CommRing R] [Algebra Z₀ R] (ζ : R), ∑ i ∈ Finset.range q, ζ ^ i = 0 →
        ∃ ι : V →ₐ[Z₀] R, ι ϖ = 1 - ζ
```

### `Polynomial.exists_isIntegral_adjoin_inv_of_bivariate_eq_zero_of_monic_of_symm`

`Thm_Polynomial_exists_isIntegral_adjoin_inv_of_bivariate_eq_zero_of_monic_of_symm` — Integrality of y⁻¹ from a monic symmetric bivariate relation

```lean
theorem Polynomial.exists_isIntegral_adjoin_inv_of_bivariate_eq_zero_of_monic_of_symm
    (R : Type*) [CommRing R] (A : Type*) [Field A] [Algebra R A]
    (n : ℕ) (P : Polynomial (Polynomial R)) (hmon : P.Monic) (hdeg : P.natDegree = n + 1)
    (hsym : ∀ i j, (P.coeff i).coeff j = (P.coeff j).coeff i) :
    ∃ h : Polynomial R,
      ∀ (x y c : A), x ≠ 0 → y ≠ 0 →
        P.eval₂ (Polynomial.eval₂RingHom (algebraMap R A) x) y = 0 →
        c * (1 + x⁻¹ * Polynomial.aeval x⁻¹ h) = 1 →
        IsIntegral (Algebra.adjoin R ({x⁻¹, c} : Set A)) y⁻¹
```

### `Polynomial.exists_isRoot_and_valuation_lt_one`

`Thm_Polynomial_exists_isRoot_and_valuation_lt_one` — A root of valuation less than one from the Newton polygon

```lean
theorem Polynomial.exists_isRoot_and_valuation_lt_one {K : Type*} [Field K] [IsAlgClosed K] (A : ValuationSubring K) {f : Polynomial K} (h0 : A.valuation (f.coeff 0) < 1) {n : ℕ} (hn : A.valuation (f.coeff n) = 1) : ∃ r : K, f.IsRoot r ∧ A.valuation r < 1
```

### `Polynomial.exists_isUnit_aeval_of_sub_mem_maximalIdeal_imp_eq`

`Thm_Polynomial_exists_isUnit_aeval_of_sub_mem_maximalIdeal_imp_eq` — Unit value of a polynomial at one of deg D+1 residues

```lean
theorem Polynomial.exists_isUnit_aeval_of_sub_mem_maximalIdeal_imp_eq
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S] [IsLocalRing S]
    (D : Polynomial R) (hD : ∃ i, IsUnit (D.coeff i))
    (x : Fin (D.natDegree + 1) → S) (hx : ∀ i j, x i - x j ∈ IsLocalRing.maximalIdeal S → i = j) :
    ∃ i, IsUnit (Polynomial.aeval (x i) D)
```

### `Polynomial.exists_le_card_lt_monic_irreducible_map_pairwise_isCoprime`

`Thm_Polynomial_exists_le_card_lt_monic_irreducible_map_pairwise_isCoprime` — Many coprime irreducible polynomials mod ℓ of prescribed large degree

```lean
theorem Polynomial.exists_le_card_lt_monic_irreducible_map_pairwise_isCoprime
    (ℓ : ℕ) [Fact ℓ.Prime] (n₀ A₀ B₀ c N₀ : ℕ)
    (avoid : Polynomial (ZMod ℓ)) (havoid : avoid ≠ 0) :
    ∃ (D M : ℕ) (g : Fin M → Polynomial ℤ),
      2 ≤ D ∧ N₀ ≤ D ∧ A₀ * (c * D) ^ n₀ + B₀ < M ∧
      (∀ i, (g i).Monic ∧ (g i).natDegree = D) ∧
      (∀ i, Irreducible ((g i).map (Int.castRingHom (ZMod ℓ)))) ∧
      (∀ i, ((g i).map (Int.castRingHom (ZMod ℓ))).Separable) ∧
      (∀ i j, i ≠ j →
        IsCoprime ((g i).map (Int.castRingHom (ZMod ℓ))) ((g j).map (Int.castRingHom (ZMod ℓ)))) ∧
      (∀ i, IsCoprime ((g i).map (Int.castRingHom (ZMod ℓ))) avoid) ∧
      (∀ i, ((g i).map (Int.castRingHom (ZMod ℓ))).eval 0 ≠ 0)
```

### `Polynomial.exists_mem_roots_gaussNorm_mul_abv_sub_pow_le`

`Thm_Polynomial_exists_mem_roots_gaussNorm_mul_abv_sub_pow_le` — Nearest root on the non-archimedean closed unit disc

```lean
theorem Polynomial.exists_mem_roots_gaussNorm_mul_abv_sub_pow_le {K : Type*} [Field K]
    [IsAlgClosed K] (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) (p : K[X])
    {z : K} (hz : v z ≤ 1) (hlt : v (p.eval z) < p.gaussNorm v 1) :
    ∃ a ∈ p.roots, v a ≤ 1 ∧ p.gaussNorm v 1 * v (z - a) ^ p.natDegree ≤ v (p.eval z)
```

### `Polynomial.exists_mem_roots_gaussNorm_mul_abv_sub_pow_le_of_evalEval_eq_zero`

`Thm_Polynomial_exists_mem_roots_gaussNorm_mul_abv_sub_pow_le_of_evalEval_eq_zero` — Non-archimedean proximity of y to the fibre H(X,0)=0

```lean
theorem Polynomial.exists_mem_roots_gaussNorm_mul_abv_sub_pow_le_of_evalEval_eq_zero
    {K : Type*} [Field K] [IsAlgClosed K] (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (H : K[X][Y]) {B : ℝ} (hB : ∀ j, (H.coeff j).gaussNorm v 1 ≤ B)
    {y w : K} (hy : v y ≤ 1) (hH : H.evalEval y w = 0)
    (hlt : B * v w < (H.eval 0).gaussNorm v 1) :
    ∃ a ∈ (H.eval 0).roots, v a ≤ 1 ∧
      (H.eval 0).gaussNorm v 1 * v (y - a) ^ (H.eval 0).natDegree ≤ B * v w
```

### `Polynomial.exists_monic_eq_resultant_of_mul_of_forall_exists_mvPolynomial`

`Thm_Polynomial_exists_monic_eq_resultant_of_mul_of_forall_exists_mvPolynomial` — Multiplicative polynomial functions of monic integer polynomials are resultants

```lean
theorem Polynomial.exists_monic_eq_resultant_of_mul_of_forall_exists_mvPolynomial
    (K : Type*) [Field K] (D : Polynomial ℤ → ℚ) (n : ℕ) (hn : Even n) (h1 : D 1 = 1)
    (hmul : ∀ G H : Polynomial ℤ, G.Monic → H.Monic → ((G.coeff 0 : ℤ) : K) ≠ 0 →
      ((H.coeff 0 : ℤ) : K) ≠ 0 → D (G * H) = D G * D H)
    (hpoly : ∀ b : ℕ, ∃ N : MvPolynomial (Fin (b + 1)) ℚ, N.totalDegree ≤ n ∧
      N.coeff (Finsupp.single 0 n) = 1 ∧
      ∀ G : Polynomial ℤ, G.Monic → G.natDegree = b + 1 → ((G.coeff 0 : ℤ) : K) ≠ 0 →
        MvPolynomial.eval (fun i : Fin (b + 1) => ((G.coeff (i : ℕ) : ℤ) : ℚ)) N = D G) :
    ∃ P : Polynomial ℚ, P.Monic ∧ P.natDegree = n ∧
      ∀ G : Polynomial ℤ, G.Monic → ((G.coeff 0 : ℤ) : K) ≠ 0 →
        D G = (G.map (Int.castRingHom ℚ)).resultant P
```

### `Polynomial.exists_monic_mul_eq_and_map_eq_of_isCoprime_of_isAdicComplete`

`Thm_Polynomial_exists_monic_mul_eq_and_map_eq_of_isCoprime_of_isAdicComplete` — Hensel's lemma for coprime monic factorisations

```lean
theorem Polynomial.exists_monic_mul_eq_and_map_eq_of_isCoprime_of_isAdicComplete
    {R S : Type*} [CommRing R] [CommRing S] (π : R →+* S) (hπ : Function.Surjective π)
    [IsAdicComplete (RingHom.ker π) R]
    {F : Polynomial R} (hF : F.Monic) {g₀ h₀ : Polynomial S} (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcop : IsCoprime g₀ h₀) (hF₀ : F.map π = g₀ * h₀) :
    ∃ g h : Polynomial R, g.Monic ∧ h.Monic ∧ g * h = F ∧
      g.map π = g₀ ∧ h.map π = h₀ ∧ IsCoprime g h ∧
      ∀ g' : Polynomial R, g'.Monic → g'.map π = g₀ → g' ∣ F → g' = g
```

### `Polynomial.exists_mvPolynomial_forall_hasSum_torusWeight_mul_eq_of_separated_recurrence`

`Thm_Polynomial_exists_mvPolynomial_forall_hasSum_torusWeight_mul_eq_of_separated_recurrence` — Rationality of a torus-weighted double generating series

```lean
theorem Polynomial.exists_mvPolynomial_forall_hasSum_torusWeight_mul_eq_of_separated_recurrence
    (A : ℤ × ℤ → ℂ) (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ)
    (hD₁ : D₁.eval 0 ≠ 0) (hD₂ : D₂.eval 0 ≠ 0)
    (hsupp : ∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → A n = 0)
    (hrec : ∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
      ∑ i ∈ Finset.range (D₁.natDegree + 1), ∑ l ∈ Finset.range (D₂.natDegree + 1),
        D₁.coeff i * D₂.coeff l * A (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0) :
    ∃ P : MvPolynomial (Fin 4) ℂ, ∀ b₁ b₂ : ℂ, ∃ r : ℝ, 0 < r ∧ ∀ X Y : ℂ, ‖X‖ < r → ‖Y‖ < r →
      Summable (fun m : ℕ × ℕ =>
        ‖A (N₁ + (m.1 : ℤ), N₁ + (m.2 : ℤ)) *
          (∑ i ∈ Finset.range (m.1 + 1), b₁ ^ i * b₂ ^ (m.1 - i)) * X ^ m.1 * Y ^ m.2‖) ∧
      (∑' m : ℕ × ℕ,
          A (N₁ + (m.1 : ℤ), N₁ + (m.2 : ℤ)) *
            (∑ i ∈ Finset.range (m.1 + 1), b₁ ^ i * b₂ ^ (m.1 - i)) * X ^ m.1 * Y ^ m.2) *
        (D₁.eval (b₁ * X) * D₁.eval (b₂ * X) * D₂.eval Y) =
        MvPolynomial.eval (![X, Y, b₁, b₂] : Fin 4 → ℂ) P
```

### `Polynomial.exists_polynomial_forall_tsum_mul_zpow_eq_of_shellRecurrent_finsum_line`

`Thm_Polynomial_exists_polynomial_forall_tsum_mul_zpow_eq_of_shellRecurrent_finsum_line` — Recurrent line sums make a double Laurent series rational

```lean
theorem Polynomial.exists_polynomial_forall_tsum_mul_zpow_eq_of_shellRecurrent_finsum_line
    (w : ℤ × ℤ → ℂ) (N₁ : ℤ) (hw : ∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → w n = 0)
    (e₁ e₂ : ℕ) (he₁ : 0 < e₁) (he₂ : 0 < e₂)
    (hc : (∃ (N : ℤ) (E : Polynomial ℂ) (M : ℕ), E.eval 0 ≠ 0 ∧ (∀ m : ℤ, m < N → (fun t : ℤ => ∑ᶠ n : ℤ × ℤ, if (e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2 = t then w n else 0) m = 0) ∧
      (∀ m : ℕ, M ≤ m → ∑ i ∈ Finset.range (E.natDegree + 1), E.coeff i * (fun t : ℤ => ∑ᶠ n : ℤ × ℤ, if (e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2 = t then w n else 0) (N + (m : ℤ) - (i : ℤ)) = 0))) :
    ∃ (P Q : Polynomial ℂ) (m₀ : ℤ), Q ≠ 0 ∧
      ∀ X : ℂ, X ≠ 0 →
        Summable (fun n : ℤ × ℤ => w n * X ^ ((e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2)) →
        (∑' n : ℤ × ℤ, w n * X ^ ((e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2)) * Q.eval X = X ^ m₀ * P.eval X
```

### `Polynomial.exists_polynomial_forall_tsum_mul_zpow_mul_eval_eq_zpow_mul_eval_of_separatedRational_of_shellRecurrence`

`Thm_Polynomial_exists_polynomial_forall_tsum_mul_zpow_mul_eval_eq_zpow_mul_eval_of_separatedRational_of_shellRecurrence` — Rationality of torus sums of separated-recurrent double arrays

```lean
theorem Polynomial.exists_polynomial_forall_tsum_mul_zpow_mul_eval_eq_zpow_mul_eval_of_separatedRational_of_shellRecurrence
    (A : ℤ × ℤ → ℂ) (b : ℤ → ℂ) (α β : ℂ) (hα : α ≠ 0) (hβ : β ≠ 0)
    (e₁ e₂ : ℕ) (he₁ : 0 < e₁) (he₂ : 0 < e₂)
    (hA : ∃ (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ), D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧
      (∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → A n = 0) ∧
      (∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
        ∑ i ∈ Finset.range (D₁.natDegree + 1), ∑ l ∈ Finset.range (D₂.natDegree + 1),
          D₁.coeff i * D₂.coeff l * A (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0))
    (hb : ∃ (N₂ : ℤ) (E : Polynomial ℂ) (M' : ℕ), E.eval 0 ≠ 0 ∧
      (∀ m : ℤ, m < N₂ → b m = 0) ∧
      (∀ m : ℕ, M' ≤ m →
        ∑ i ∈ Finset.range (E.natDegree + 1), E.coeff i * b (N₂ + (m : ℤ) - (i : ℤ)) = 0)) :
    ∃ (P Q : Polynomial ℂ) (m₀ : ℤ), Q ≠ 0 ∧
      ∀ X : ℂ, X ≠ 0 →
        Summable (fun n : ℤ × ℤ =>
          A n * b n.1 * α ^ n.1 * β ^ n.2 * X ^ ((e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2)) →
        (∑' n : ℤ × ℤ, A n * b n.1 * α ^ n.1 * β ^ n.2 * X ^ ((e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2)) * Q.eval X =
          X ^ m₀ * P.eval X
```

### `Polynomial.exists_root_reducing_to_simple_root`

`Thm_Polynomial_exists_root_reducing_to_simple_root` — Simple roots lift under reduction of a split polynomial

```lean
theorem Polynomial.exists_root_reducing_to_simple_root {A k : Type*} [CommRing A] [IsDomain A] [CommRing k] [IsDomain k] (red : A →+* k) (s : Multiset A) (b : k) (hb : ((s.map fun a => Polynomial.X - Polynomial.C a).prod.map red).rootMultiplicity b = 1) : ∃ a ∈ s, red a = b ∧ (s.map fun a => Polynomial.X - Polynomial.C a).prod.rootMultiplicity a = 1 ∧ ∀ a' ∈ s, red a' = b → a' = a
```

### `Polynomial.finite_setOf_criticalValue`

`Thm_Polynomial_finite_setOf_criticalValue` — Finiteness of the critical values of a polynomial

```lean
theorem Polynomial.finite_setOf_criticalValue
    {k : Type u} [Field k] (P : k[X]) (hP : derivative P ≠ 0) :
    {c : k | ∃ x : k, P.eval x = c ∧ (derivative P).eval x = 0}.Finite
```

### `Polynomial.finrank_torsionBy_X_pow_sub_one_eq_sum_finrank_torsionBy_cyclotomic`

`Thm_Polynomial_finrank_torsionBy_X_pow_sub_one_eq_sum_finrank_torsionBy_cyclotomic` — Dimension of (X^e-1)-torsion as a sum over divisors

```lean
theorem Polynomial.finrank_torsionBy_X_pow_sub_one_eq_sum_finrank_torsionBy_cyclotomic
    {M : Type u} [AddCommGroup M] [Module ℚ[X] M] [Module ℚ M] [IsScalarTower ℚ ℚ[X] M] [FiniteDimensional ℚ M]
    {e : ℕ} (he : 0 < e) :
    Module.finrank ℚ (Submodule.torsionBy ℚ[X] M ((X : ℚ[X]) ^ e - 1)) =
      ∑ d ∈ e.divisors, Module.finrank ℚ (Submodule.torsionBy ℚ[X] M (cyclotomic d ℚ))
```

### `Polynomial.irreducible_X_pow_sub_C_of_monoidHom_units_coprime`

`Thm_Polynomial_irreducible_X_pow_sub_C_of_monoidHom_units_coprime` — Irreducibility of X^N-β via a valuation-like homomorphism

```lean
theorem Polynomial.irreducible_X_pow_sub_C_of_monoidHom_units_coprime
    {K : Type u} [Field K] {N : ℕ} (hN : 0 < N) {β : K} (hβ : β ≠ 0)
    (φ : Kˣ →* Multiplicative ℤ)
    (hφ : (Multiplicative.toAdd (φ (Units.mk0 β hβ))).natAbs.Coprime N) :
    Irreducible (X ^ N - C β)
```

### `Polynomial.irreducible_cyclotomic_fractionRing_of_maximalIdeal_eq_span`

`Thm_Polynomial_irreducible_cyclotomic_fractionRing_of_maximalIdeal_eq_span` — Irreducibility of Φ_q over a DVR with uniformiser q

```lean
theorem Polynomial.irreducible_cyclotomic_fractionRing_of_maximalIdeal_eq_span
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] (q : ℕ) [Fact q.Prime]
    (hA₀q : IsLocalRing.maximalIdeal A₀ = Ideal.span {(q : A₀)}) :
    Irreducible (Polynomial.cyclotomic q (FractionRing A₀))
```

### `Polynomial.irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range`

`Thm_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range` — Absolute irreducibility of F under separable closedness in L

```lean
theorem Polynomial.irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range
    {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]
    (hsc : ∀ θ : L, IsSeparable K θ → θ ∈ (algebraMap K L).range)
    {d : ℕ} (x : Fin d → L) (hx : AlgebraicIndependent K x) (y : L)
    (F : Polynomial (MvPolynomial (Fin d) K)) (hFm : F.Monic)
    (hFirr : Irreducible (F.map (algebraMap (MvPolynomial (Fin d) K)
      (FractionRing (MvPolynomial (Fin d) K)))))
    (hFsep : (F.map (algebraMap (MvPolynomial (Fin d) K)
      (FractionRing (MvPolynomial (Fin d) K)))).Separable)
    (hroot : F.eval₂ (MvPolynomial.aeval x : MvPolynomial (Fin d) K →ₐ[K] L).toRingHom y = 0) :
    Irreducible (F.map (MvPolynomial.map (algebraMap K (AlgebraicClosure K))))
```

### `Polynomial.irreducible_of_transitive_ringAut`

`Thm_Polynomial_irreducible_of_transitive_ringAut` — Irreducibility from an automorphism cycling all but one root

```lean
theorem Polynomial.irreducible_of_transitive_ringAut {F L : Type*} [Field F] [Field L] [Algebra F L] (P : Polynomial F) (hP : P.Monic) (hPs : (P.map (algebraMap F L)).Splits) (σ : L ≃+* L) (hσ : ∀ a : F, σ (algebraMap F L a) = algebraMap F L a) (y₀ : L) (r : ℕ → L) (n : ℕ) (hroots : (P.map (algebraMap F L)).roots = y₀ ::ₘ (Multiset.range n).map r) (hnodup : (P.map (algebraMap F L)).roots.Nodup) (hcycle : ∀ i < n, σ (r i) = r ((i + 1) % n)) (hy₀ : y₀ ∉ (algebraMap F L).range) : Irreducible P
```

### `Polynomial.isCoprime_and_wronskian_ne_zero_comp_of_wronskian_ne_zero`

`Thm_Polynomial_isCoprime_and_wronskian_ne_zero_comp_of_wronskian_ne_zero` — Coprimality and non-vanishing Wronskian for composed rational functions

```lean
theorem Polynomial.isCoprime_and_wronskian_ne_zero_comp_of_wronskian_ne_zero {k : Type*} [Field k] [IsAlgClosed k] {u v s t U V : Polynomial k} (huv : IsCoprime u v) (hu : 0 < max u.natDegree v.natDegree) (hw : Polynomial.wronskian u v ≠ 0) (hst : IsCoprime s t) (hs : 0 < max s.natDegree t.natDegree) (hw' : Polynomial.wronskian s t ≠ 0) (hU : ∀ x : k, v.eval x ≠ 0 → U.eval x = v.eval x ^ max s.natDegree t.natDegree * s.eval (u.eval x / v.eval x)) (hV : ∀ x : k, v.eval x ≠ 0 → V.eval x = v.eval x ^ max s.natDegree t.natDegree * t.eval (u.eval x / v.eval x)) : IsCoprime U V ∧ 0 < max U.natDegree V.natDegree ∧ Polynomial.wronskian U V ≠ 0
```

### `Polynomial.isCoprime_of_monic_of_isCoprime_map_of_maximalIdeal_le_ker`

`Thm_Polynomial_isCoprime_of_monic_of_isCoprime_map_of_maximalIdeal_le_ker` — Coprimality lifts from the residue field for monic f

```lean
theorem Polynomial.isCoprime_of_monic_of_isCoprime_map_of_maximalIdeal_le_ker
    {R k : Type*} [CommRing R] [IsLocalRing R] [Field k] (φ : R →+* k)
    (hφ : IsLocalRing.maximalIdeal R ≤ RingHom.ker φ)
    (f g : R[X]) (hf : f.Monic) (h : IsCoprime (f.map φ) (g.map φ)) :
    IsCoprime f g
```

### `Polynomial.isDomain_tensor_of_isFractionRing`

`Thm_Polynomial_isDomain_tensor_of_isFractionRing` — Geometric integrality of the rational function field

```lean
theorem Polynomial.isDomain_tensor_of_isFractionRing
    (F₀ : Type u₁) (κ : Type u₂) (k : Type u₃) [Field F₀] [CommRing κ] [Field k]
    [Algebra F₀[X] κ] [IsFractionRing F₀[X] κ] [Algebra F₀ κ] [IsScalarTower F₀ F₀[X] κ]
    [Algebra F₀ k] : IsDomain (κ ⊗[F₀] k)
```

### `Polynomial.isReduced_quotient_span_singleton_of_separable_map`

`Thm_Polynomial_isReduced_quotient_span_singleton_of_separable_map` — Reducedness of D[X]/(g) for g monic and separable over Frac D

```lean
theorem Polynomial.isReduced_quotient_span_singleton_of_separable_map
    {D : Type*} [CommRing D] [IsDomain D] {g : D[X]} (hg : g.Monic)
    (hsep : (g.map (algebraMap D (FractionRing D))).Separable) :
    IsReduced (D[X] ⧸ Ideal.span {g})
```

### `Polynomial.log_abv_eval_eq_log_gaussNorm_add_sum`

`Thm_Polynomial_log_abv_eval_eq_log_gaussNorm_add_sum` — Non-archimedean Jensen formula on the closed unit disc

```lean
theorem Polynomial.log_abv_eval_eq_log_gaussNorm_add_sum {K : Type*} [Field K] [IsAlgClosed K]
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) (p : K[X]) (hp : p ≠ 0)
    {z : K} (hz : v z ≤ 1) (hpz : p.eval z ≠ 0) :
    Real.log (v (p.eval z)) = Real.log (p.gaussNorm v 1)
      + ((p.roots.filter fun a => v a ≤ 1).map fun a => Real.log (v (z - a))).sum
```

### `Polynomial.log_norm_coeff_le_logMahlerMeasure_add`

`Thm_Polynomial_log_norm_coeff_le_logMahlerMeasure_add` — Coefficient bound by logarithmic Mahler measure

```lean
theorem Polynomial.log_norm_coeff_le_logMahlerMeasure_add {p : Polynomial ℂ} {k : ℕ} (hk : p.coeff k ≠ 0) :
    Real.log ‖p.coeff k‖ ≤ p.logMahlerMeasure + p.natDegree * Real.log 2
```

### `Polynomial.map_eq_C_mul_X_add_C_pow_of_forall_dvd_eval`

`Thm_Polynomial_map_eq_C_mul_X_add_C_pow_of_forall_dvd_eval` — Rational polynomial with ℓ-adically divisible values is a_g(X+c)^g

```lean
theorem Polynomial.map_eq_C_mul_X_add_C_pow_of_forall_dvd_eval
    (ℓ : ℕ) [Fact ℓ.Prime] (g : ℕ) (P : ℚ[X]) (hdeg : P.natDegree ≤ g)
    (χ : ℕ → ℤ) (hχ : ∀ m : ℕ, P.eval (m : ℚ) = (χ m : ℚ)) (c : ℤ_[ℓ])
    (hval : ∀ m : ℕ, (m : ℤ_[ℓ]) + c ≠ 0 → ((m : ℤ_[ℓ]) + c) ^ g ∣ (χ m : ℤ_[ℓ])) :
    P.map (algebraMap ℚ ℚ_[ℓ]) =
      C (algebraMap ℚ ℚ_[ℓ] (P.coeff g)) * (X + C (c : ℚ_[ℓ])) ^ g
```

### `Polynomial.mem_range_aeval_of_isCoprime_of_pow_mul_eq`

`Thm_Polynomial_mem_range_aeval_of_isCoprime_of_pow_mul_eq` — Coprime denominators: z is a polynomial in a transcendental x

```lean
theorem Polynomial.mem_range_aeval_of_isCoprime_of_pow_mul_eq
    {F A : Type*} [Field F] [CommRing A] [IsDomain A] [Algebra F A]
    (x : A) (hx : Transcendental F x) {f g : Polynomial F} (hfg : IsCoprime f g) (z : A) (m n : ℕ)
    (P Q : Polynomial F) (hf : Polynomial.aeval x f ^ m * z = Polynomial.aeval x P)
    (hg : Polynomial.aeval x g ^ n * z = Polynomial.aeval x Q) :
    z ∈ (Polynomial.aeval (R := F) x).range
```

### `Polynomial.mem_range_of_eval_eq_const`

`Thm_Polynomial_mem_range_of_eval_eq_const` — A value attained too often lies in the base field

```lean
theorem Polynomial.mem_range_of_eval_eq_const {F L : Type*} [Field F] [Field L] [Algebra F L] (g : Polynomial F) (x : L) (s : Finset L) (hcard : g.natDegree < s.card) (hval : ∀ y ∈ s, Polynomial.aeval y g = x) : x ∈ (algebraMap F L).range
```

### `Polynomial.mem_range_of_unique_common_root`

`Thm_Polynomial_mem_range_of_unique_common_root` — Unique common root of a split separable polynomial is rational

```lean
theorem Polynomial.mem_range_of_unique_common_root {F L : Type*} [Field F] [Field L] [Algebra F L] (A B : Polynomial F) (hA : A ≠ 0) (hAs : (A.map (algebraMap F L)).Splits) (hAnd : (A.map (algebraMap F L)).roots.Nodup) (x : L) (hxA : Polynomial.aeval x A = 0) (hxB : Polynomial.aeval x B = 0) (huniq : ∀ y : L, Polynomial.aeval y A = 0 → Polynomial.aeval y B = 0 → y = x) : x ∈ (algebraMap F L).range
```

### `Polynomial.natDegree_aeval_symm_minpoly_adjoin_coeff_le_of_transcendental`

`Thm_Polynomial_natDegree_aeval_symm_minpoly_adjoin_coeff_le_of_transcendental` — Two-chart degree bound on minimal polynomial coefficients

```lean
theorem Polynomial.natDegree_aeval_symm_minpoly_adjoin_coeff_le_of_transcendental
    {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]
    (x : F) (hxL : Transcendental L x) (hx0 : x ≠ 0)
    (f : F) (hint : IsIntegral (Algebra.adjoin L ({x} : Set F)) f) (m : ℕ)
    (h₂ : ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → x ∉ V →
      f * (x ^ m)⁻¹ ∈ V)
    (j : ℕ) (c : Polynomial L)
    (hc : Polynomial.aeval x c =
      (((minpoly (Algebra.adjoin L ({x} : Set F)) f).coeff j :
        Algebra.adjoin L ({x} : Set F)) : F)) :
    c.natDegree ≤ ((minpoly (Algebra.adjoin L ({x} : Set F)) f).natDegree - j) * m
```

### `Polynomial.natDegree_le_of_aeval_mul_inv_pow_mem_adjoin_inv`

`Thm_Polynomial_natDegree_le_of_aeval_mul_inv_pow_mem_adjoin_inv` — Degree bound from membership in L[x⁻¹]

```lean
theorem Polynomial.natDegree_le_of_aeval_mul_inv_pow_mem_adjoin_inv
    {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]
    (x : F) (hxL : Transcendental L x) (hx0 : x ≠ 0)
    (c : Polynomial L) (n : ℕ)
    (h : Polynomial.aeval x c * (x ^ n)⁻¹ ∈ Algebra.adjoin L ({x⁻¹} : Set F)) :
    c.natDegree ≤ n
```

### `Polynomial.nonempty_linearEquiv_of_finrank_torsionBy_cyclotomic_eq`

`Thm_Polynomial_nonempty_linearEquiv_of_finrank_torsionBy_cyclotomic_eq` — Cyclotomic torsion dimensions classify ℚ[X]-modules killed by Xⁿ-1

```lean
theorem Polynomial.nonempty_linearEquiv_of_finrank_torsionBy_cyclotomic_eq
    {M : Type u} [AddCommGroup M] [Module ℚ[X] M] [Module ℚ M] [IsScalarTower ℚ ℚ[X] M] [FiniteDimensional ℚ M]
    {N : Type v} [AddCommGroup N] [Module ℚ[X] N] [Module ℚ N] [IsScalarTower ℚ ℚ[X] N] [FiniteDimensional ℚ N]
    {n : ℕ} (hn : 0 < n) (hM : Module.IsTorsionBy ℚ[X] M ((X : ℚ[X]) ^ n - 1)) (hN : Module.IsTorsionBy ℚ[X] N ((X : ℚ[X]) ^ n - 1))
    (h : ∀ d, d ∣ n → Module.finrank ℚ (Submodule.torsionBy ℚ[X] M (cyclotomic d ℚ)) =
      Module.finrank ℚ (Submodule.torsionBy ℚ[X] N (cyclotomic d ℚ))) :
    Nonempty (M ≃ₗ[ℚ[X]] N)
```

### `Polynomial.nonempty_ringEquiv_tensor_quotient_span_singleton`

`Thm_Polynomial_nonempty_ringEquiv_tensor_quotient_span_singleton` — Base change of κ[X]/(f) to D[X]/(f)

```lean
theorem Polynomial.nonempty_ringEquiv_tensor_quotient_span_singleton
    (κ : Type u₁) (D : Type u₂) [CommRing κ] [CommRing D] [Algebra κ D] (f : κ[X]) :
    Nonempty (D ⊗[κ] (κ[X] ⧸ Ideal.span {f}) ≃+* D[X] ⧸ Ideal.span {f.map (algebraMap κ D)})
```

### `Polynomial.prime_and_isDomain_adjoinRoot_of_monic_of_coeff_mem_maximalIdeal_powerSeries_of_coeff_zero_eq_natCast_mul`

`Thm_Polynomial_prime_and_isDomain_adjoinRoot_of_monic_of_coeff_mem_maximalIdeal_powerSeries_of_coeff_zero_eq_natCast_mul` — Eisenstein polynomials over W₀[[t]] are prime

```lean
theorem Polynomial.prime_and_isDomain_adjoinRoot_of_monic_of_coeff_mem_maximalIdeal_powerSeries_of_coeff_zero_eq_natCast_mul
    (q : ℕ) [Fact q.Prime] (hq : 2 ≤ q)
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (g : Polynomial (PowerSeries W₀)) (hgm : g.Monic) (hgdeg : g.natDegree = q - 1)
    (hgcoeff : ∀ i < q - 1, g.coeff i ∈ maximalIdeal (PowerSeries W₀))
    (hg0 : ∃ u : PowerSeries W₀, IsUnit u ∧ g.coeff 0 = (q : PowerSeries W₀) * u) :
    Prime g ∧ IsDomain (AdjoinRoot g)
```

### `Polynomial.roots_filter_valuation_eq_singleton_of_kroneckerShape`

`Thm_Polynomial_roots_filter_valuation_eq_singleton_of_kroneckerShape` — Exactly one large root of a Kronecker-shape polynomial

```lean
theorem Polynomial.roots_filter_valuation_eq_singleton_of_kroneckerShape
    {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
    {q : ℕ} (hq : 1 < q) (x₀ c : K) (hx : 1 < v x₀) (hc : v c ≤ 1)
    (H : Polynomial K) (hHdeg : H.natDegree ≤ q)
    (hHb : ∀ b < q, v (H.coeff b) ≤ v x₀ ^ q) (hHq : v (H.coeff q) ≤ v x₀ ^ (q - 1))
    (hsplit : ((Polynomial.C (x₀ ^ q) - Polynomial.X) * (Polynomial.C x₀ - Polynomial.X ^ q)
      + Polynomial.C c * H).Splits) :
    ∃ y₀ : K, (((Polynomial.C (x₀ ^ q) - Polynomial.X) * (Polynomial.C x₀ - Polynomial.X ^ q)
        + Polynomial.C c * H).roots.filter fun y => v y = v x₀ ^ q) = {y₀}
```

### `Polynomial.separable_sub_C_of_forall_eval_derivative`

`Thm_Polynomial_separable_sub_C_of_forall_eval_derivative` — Separability of P-c at a non-critical value c

```lean
theorem Polynomial.separable_sub_C_of_forall_eval_derivative
    {k : Type u} [Field k] [IsAlgClosed k] (P : k[X]) (c : k)
    (hc : ∀ x : k, (derivative P).eval x = 0 → P.eval x ≠ c) :
    (P - C c).Separable
```

### `Polynomial.shellRecurrent_finsum_line_of_separatedRational_of_shellRecurrence`

`Thm_Polynomial_shellRecurrent_finsum_line_of_separatedRational_of_shellRecurrence` — Line sums of a separated-rational array satisfy a linear recurrence

```lean
theorem Polynomial.shellRecurrent_finsum_line_of_separatedRational_of_shellRecurrence
    (A : ℤ × ℤ → ℂ) (b : ℤ → ℂ) (α β : ℂ) (hα : α ≠ 0) (hβ : β ≠ 0)
    (e₁ e₂ : ℕ) (he₁ : 0 < e₁) (he₂ : 0 < e₂)
    (hA : ∃ (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ), D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧
      (∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → A n = 0) ∧
      (∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
        ∑ i ∈ Finset.range (D₁.natDegree + 1), ∑ l ∈ Finset.range (D₂.natDegree + 1),
          D₁.coeff i * D₂.coeff l * A (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0))
    (hb : ∃ (N₂ : ℤ) (E : Polynomial ℂ) (M' : ℕ), E.eval 0 ≠ 0 ∧
      (∀ m : ℤ, m < N₂ → b m = 0) ∧
      (∀ m : ℕ, M' ≤ m →
        ∑ i ∈ Finset.range (E.natDegree + 1), E.coeff i * b (N₂ + (m : ℤ) - (i : ℤ)) = 0)) :
    (∃ (N : ℤ) (E : Polynomial ℂ) (M : ℕ), E.eval 0 ≠ 0 ∧ (∀ m : ℤ, m < N → (fun t : ℤ => ∑ᶠ n : ℤ × ℤ,
        if (e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2 = t then A n * b n.1 * α ^ n.1 * β ^ n.2 else 0) m = 0) ∧
      (∀ m : ℕ, M ≤ m → ∑ i ∈ Finset.range (E.natDegree + 1), E.coeff i * (fun t : ℤ => ∑ᶠ n : ℤ × ℤ,
        if (e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2 = t then A n * b n.1 * α ^ n.1 * β ^ n.2 else 0) (N + (m : ℤ) - (i : ℤ)) = 0))
```

### `Polynomial.squarefree_of_squarefree_map`

`Thm_Polynomial_squarefree_of_squarefree_map` — Squarefreeness descends along a map from a field into a domain

```lean
theorem Polynomial.squarefree_of_squarefree_map {κ L : Type*} [Field κ] [CommRing L] [IsDomain L]
    (φ : κ →+* L) {f : Polynomial κ} (hf : Squarefree (f.map φ)) : Squarefree f
```

### `Polynomial.valuation_div_sub_one_lt_one_of_kroneckerShape`

`Thm_Polynomial_valuation_div_sub_one_lt_one_of_kroneckerShape` — Kronecker-shape root estimate, quotient form

```lean
theorem Polynomial.valuation_div_sub_one_lt_one_of_kroneckerShape
    {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
    {q : ℕ} (hq : 1 < q) (x₀ c : K) (hx : 1 < v x₀) (hc : v c ≤ 1)
    (H : K[X]) (hHdeg : H.natDegree ≤ q)
    (hHb : ∀ b < q, v (H.coeff b) ≤ v x₀ ^ q) (hHq : v (H.coeff q) ≤ v x₀ ^ (q - 1))
    (y : K) (hy : ((C (x₀ ^ q) - X) * (C x₀ - X ^ q) + C c * H).IsRoot y) :
    v (y / x₀ ^ q - 1) < 1 ∨ (1 < v y ∧ v (x₀ / y ^ q - 1) < 1)
```

### `Polynomial.valuation_root_dichotomy_of_kroneckerShape`

`Thm_Polynomial_valuation_root_dichotomy_of_kroneckerShape` — Root-size dichotomy for Kronecker-shaped polynomials over a valued field

```lean
theorem Polynomial.valuation_root_dichotomy_of_kroneckerShape
    {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
    {q : ℕ} (hq : 1 < q) (x₀ c : K) (hx : 1 < v x₀) (hc : v c ≤ 1)
    (H : K[X]) (hHdeg : H.natDegree ≤ q)
    (hHb : ∀ b < q, v (H.coeff b) ≤ v x₀ ^ q) (hHq : v (H.coeff q) ≤ v x₀ ^ (q - 1))
    (y : K) (hy : ((C (x₀ ^ q) - X) * (C x₀ - X ^ q) + C c * H).IsRoot y) :
    (v y = v x₀ ^ q ∧ v (y - x₀ ^ q) ≤ v c * v x₀ ^ (q - 1)) ∨
      (v y ^ q = v x₀ ∧ v (x₀ - y ^ q) ≤ v c * v y ^ (q - 1))
```

## Complex (64)

### `Complex.circleIntegral_div_sub_eq_sum_div_deriv`

`Thm_Complex_circleIntegral_div_sub_eq_sum_div_deriv` — Circle integral of Ψ/(R-t) over simple solutions of R=t

```lean
theorem Complex.circleIntegral_div_sub_eq_sum_div_deriv {R Ψ : ℂ → ℂ} {c t : ℂ} {r : ℝ}
    (hr : 0 < r) (hR : ∀ z ∈ Metric.closedBall c r, AnalyticAt ℂ R z)
    (hΨ : ∀ z ∈ Metric.closedBall c r, AnalyticAt ℂ Ψ z)
    (hne : ∀ z ∈ Metric.sphere c r, R z ≠ t) (Z : Finset ℂ)
    (hZ : ∀ a, a ∈ Z ↔ a ∈ Metric.ball c r ∧ R a = t) (hsimple : ∀ a ∈ Z, deriv R a ≠ 0) :
    (∮ z in C(c, r), Ψ z / (R z - t)) =
      2 * Real.pi * Complex.I * ∑ a ∈ Z, Ψ a / deriv R a
```

### `Complex.circleIntegral_eq_sum_residue_of_simplePole`

`Thm_Complex_circleIntegral_eq_sum_residue_of_simplePole` — Residue theorem on a circle for simple poles

```lean
theorem Complex.circleIntegral_eq_sum_residue_of_simplePole
    {R : ℝ} {z₀ : ℂ} (hR : 0 < R) (h c : ℂ → ℂ) (Z : Finset ℂ)
    (hZ : ∀ a ∈ Z, a ∈ Metric.ball z₀ R)
    (hh : ∀ z ∈ Metric.closedBall z₀ R, z ∉ Z → AnalyticAt ℂ h z)
    (hloc : ∀ a ∈ Z, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      ∀ᶠ z in 𝓝[≠] a, h z = c a / (z - a) + g z) :
    (∮ z in C(z₀, R), h z) = 2 * Real.pi * Complex.I * ∑ a ∈ Z, c a
```

### `Complex.circleIntegral_mul_deriv_div_sub_eq_sum_analyticOrderNatAt`

`Thm_Complex_circleIntegral_mul_deriv_div_sub_eq_sum_analyticOrderNatAt` — Weighted argument principle on a disc

```lean
theorem Complex.circleIntegral_mul_deriv_div_sub_eq_sum_analyticOrderNatAt
    {R G : ℂ → ℂ} {z₀ t : ℂ} {r : ℝ} (hr : 0 < r)
    (hR : ∀ z ∈ Metric.closedBall z₀ r, AnalyticAt ℂ R z)
    (hG : ∀ z ∈ Metric.closedBall z₀ r, AnalyticAt ℂ G z)
    (hne : ∀ z ∈ Metric.sphere z₀ r, R z ≠ t) :
    ∃ Z : Finset ℂ, (∀ a, a ∈ Z ↔ a ∈ Metric.ball z₀ r ∧ R a = t) ∧
      (∮ z in C(z₀, r), G z * deriv R z / (R z - t)) =
        2 * π * Complex.I *
          ∑ a ∈ Z, (analyticOrderNatAt (fun z => R z - t) a : ℂ) * G a
```

### `Complex.contDiffOn_infty_of_differentiableOn_pi`

`Thm_Complex_contDiffOn_infty_of_differentiableOn_pi` — Complex differentiability on open U⊆ℂⁿ implies C^∞

```lean
theorem Complex.contDiffOn_infty_of_differentiableOn_pi {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : (Fin n → ℂ) → E} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) : ContDiffOn ℂ ∞ f U
```

### `Complex.contDiffOn_one_of_differentiableOn_pi`

`Thm_Complex_contDiffOn_one_of_differentiableOn_pi` — Osgood's lemma: holomorphic maps on ℂⁿ are C¹

```lean
theorem Complex.contDiffOn_one_of_differentiableOn_pi {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : (Fin n → ℂ) → E} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) : ContDiffOn ℂ 1 f U
```

### `Complex.countable_setOf_re_gt_and_eq_zero_of_differentiableOn_of_exists_ne_zero`

`Thm_Complex_countable_setOf_re_gt_and_eq_zero_of_differentiableOn_of_exists_ne_zero` — Countability of the zeros in a right half-plane

```lean
theorem Complex.countable_setOf_re_gt_and_eq_zero_of_differentiableOn_of_exists_ne_zero
    (f : ℂ → ℂ) (σ : ℝ)
    (hf : DifferentiableOn ℂ f {s : ℂ | σ < s.re})
    (hne : ∃ s : ℂ, σ < s.re ∧ f s ≠ 0) :
    Set.Countable {s : ℂ | σ < s.re ∧ f s = 0}
```

### `Complex.differentiableOn_integral_mul_of_memLp_two_of_tendsto_eLpNorm_of_forall_differentiableOn`

`Thm_Complex_differentiableOn_integral_mul_of_memLp_two_of_tendsto_eLpNorm_of_forall_differentiableOn` — Holomorphy of L²-pairings of a holomorphic family

```lean
theorem Complex.differentiableOn_integral_mul_of_memLp_two_of_tendsto_eLpNorm_of_forall_differentiableOn
    {Y : Type*} [MeasurableSpace Y] (μ : MeasureTheory.Measure Y) [MeasureTheory.SFinite μ]
    {U : Set ℂ} (hU : IsOpen U)
    (v : ℂ → Y → ℂ) (w : Y → ℂ)
    (hw : MeasureTheory.MemLp w 2 μ)
    (hvm : ∀ z ∈ U, Measurable (v z))
    (hv : ∀ z ∈ U, MeasureTheory.MemLp (v z) 2 μ)
    (hvc : ∀ z₀ ∈ U, Filter.Tendsto (fun z => MeasureTheory.eLpNorm (v z - v z₀) 2 μ)
      (nhdsWithin z₀ U) (nhds 0))
    (hhol : ∀ y : Y, DifferentiableOn ℂ (fun z => v z y) U) :
    DifferentiableOn ℂ (fun z => ∫ y, v z y * w y ∂μ) U
```

### `Complex.differentiableOn_integral_of_continuousOn_of_forall_differentiableOn`

`Thm_Complex_differentiableOn_integral_of_continuousOn_of_forall_differentiableOn` — Holomorphy of integrals with compactly supported continuous integrand

```lean
theorem Complex.differentiableOn_integral_of_continuousOn_of_forall_differentiableOn
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (ν : MeasureTheory.Measure Y) [MeasureTheory.IsFiniteMeasureOnCompacts ν]
    {U : Set ℂ} (hU : IsOpen U) {S : Set Y} (hS : IsCompact S)
    (F : ℂ → Y → ℂ) (hF : ContinuousOn (Function.uncurry F) (U ×ˢ Set.univ))
    (hFS : ∀ z ∈ U, ∀ a ∉ S, F z a = 0)
    (hhol : ∀ a : Y, DifferentiableOn ℂ (fun z => F z a) U) :
    DifferentiableOn ℂ (fun z => ∫ a, F z a ∂ν) U
```

### `Complex.div_le_one_sub_of_apply_eq_zero_of_norm_le_exp_of_three_four_one_nonneg`

`Thm_Complex_div_le_one_sub_of_apply_eq_zero_of_norm_le_exp_of_three_four_one_nonneg` — De la Vallée Poussin–Landau zero-free region deduction

```lean
theorem Complex.div_le_one_sub_of_apply_eq_zero_of_norm_le_exp_of_three_four_one_nonneg
    (F₁ F₂ : ℂ → ℂ) (β γ r 𝓛 C₀ : ℝ)
    (hr : 0 < r) (hr1 : r ≤ 1) (h𝓛 : 1 ≤ r * 𝓛) (hC₀ : 0 ≤ C₀) (hC₀𝓛 : C₀ ≤ 𝓛)
    (hρ : F₁ ((β : ℂ) + γ * Complex.I) = 0)
    (h1nz : ∀ s : ℂ, 1 < s.re → F₁ s ≠ 0)
    (h2nz : ∀ s : ℂ, 1 < s.re → F₂ s ≠ 0)
    (h1an : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      AnalyticOnNhd ℂ F₁ (Metric.closedBall ((σ : ℂ) + γ * Complex.I) r))
    (h2an : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      AnalyticOnNhd ℂ F₂ (Metric.closedBall ((σ : ℂ) + 2 * γ * Complex.I) r))
    (h1up : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      ∀ s ∈ Metric.closedBall ((σ : ℂ) + γ * Complex.I) r, ‖F₁ s‖ ≤ Real.exp 𝓛)
    (h2up : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      ∀ s ∈ Metric.closedBall ((σ : ℂ) + 2 * γ * Complex.I) r, ‖F₂ s‖ ≤ Real.exp 𝓛)
    (h1lo : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      (σ - 1) ^ 2 * Real.exp (-𝓛) ≤ ‖F₁ ((σ : ℂ) + γ * Complex.I)‖)
    (h2lo : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      (σ - 1) ^ 2 * Real.exp (-𝓛) ≤ ‖F₂ ((σ : ℂ) + 2 * γ * Complex.I)‖)
    (h341 : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      0 ≤ 3 * (1 / (σ - 1) + C₀)
        + 4 * (-(deriv F₁ ((σ : ℂ) + γ * Complex.I) / F₁ ((σ : ℂ) + γ * Complex.I))).re
        + (-(deriv F₂ ((σ : ℂ) + 2 * γ * Complex.I) / F₂ ((σ : ℂ) + 2 * γ * Complex.I))).re) :
    r / (20000 * 𝓛) ≤ 1 - β
```

### `Complex.eq_zero_of_summable_norm_mul_zpow_of_forall_tsum_mul_zpow_eq_zero`

`Thm_Complex_eq_zero_of_summable_norm_mul_zpow_of_forall_tsum_mul_zpow_eq_zero` — Uniqueness of Laurent coefficients on an annulus

```lean
theorem Complex.eq_zero_of_summable_norm_mul_zpow_of_forall_tsum_mul_zpow_eq_zero
    (e : ℤ → ℂ) {r₁ r₂ : ℝ} (h0 : 0 < r₁) (h12 : r₁ < r₂)
    (hs₁ : Summable fun m : ℤ => ‖e m‖ * r₁ ^ m) (hs₂ : Summable fun m : ℤ => ‖e m‖ * r₂ ^ m)
    (hz : ∀ z : ℂ, r₁ < ‖z‖ → ‖z‖ < r₂ → ∑' m : ℤ, e m * z ^ m = 0) : e = 0
```

### `Complex.exists_analyticOnNhd_comp_pow_of_forall_mul_eq`

`Thm_Complex_exists_analyticOnNhd_comp_pow_of_forall_mul_eq` — Rotation-invariant holomorphic functions on a disc factor through z^e

```lean
theorem Complex.exists_analyticOnNhd_comp_pow_of_forall_mul_eq {e : ℕ} (he : 0 < e) {ω : ℂ} (hω : IsPrimitiveRoot ω e)
    {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (Metric.ball 0 r))
    (hinv : ∀ z ∈ Metric.ball 0 r, f (ω * z) = f z) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (Metric.ball 0 (r ^ e)) ∧ ∀ z ∈ Metric.ball 0 r, f z = F (z ^ e)
```

### `Complex.exists_contDiffOn_norm_one_sub_exp_sq_mul_log_eq_mul_add`

`Thm_Complex_exists_contDiffOn_norm_one_sub_exp_sq_mul_log_eq_mul_add` — Local normal form of the germ |1-e^z|²log|1-e^z|

```lean
theorem Complex.exists_contDiffOn_norm_one_sub_exp_sq_mul_log_eq_mul_add :
    ∃ a b : ℝ × ℝ → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) a {p : ℝ × ℝ | |p.2| < 1 / 2} ∧
      ContDiffOn ℝ (⊤ : ℕ∞) b {p : ℝ × ℝ | |p.2| < 1 / 2} ∧
      (∀ p : ℝ × ℝ, |p.2| < 1 / 2 → 0 < a p) ∧
      (∀ p : ℝ × ℝ, |p.2| < 1 / 2 →
        ‖(1 : ℂ) - Complex.exp ((p.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 : ℝ))‖ ^ 2 *
            Real.log ‖(1 : ℂ) - Complex.exp ((p.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 : ℝ))‖ =
          a p * ((p.1 ^ 2 / 4 + 4 * Real.pi ^ 2 * p.2 ^ 2) *
              Real.log (p.1 ^ 2 / 4 + 4 * Real.pi ^ 2 * p.2 ^ 2)) +
            (p.1 ^ 2 / 4 + 4 * Real.pi ^ 2 * p.2 ^ 2) * b p) ∧
      (∀ p : ℝ × ℝ,
        Complex.exp ((p.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 : ℝ)) = 1 ↔
          p.1 = 0 ∧ ∃ k : ℤ, p.2 = k) ∧
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : ℝ × ℝ =>
          ‖(1 : ℂ) - Complex.exp ((p.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 : ℝ))‖ ^ 2 *
            Real.log ‖(1 : ℂ) - Complex.exp ((p.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 : ℝ))‖)
        {p : ℝ × ℝ | Complex.exp ((p.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 : ℝ)) ≠ 1}
```

### `Complex.exists_differentiableOn_forall_evalEval_eq_zero_iff_eq_of_evalEval_derivative_ne_zero`

`Thm_Complex_exists_differentiableOn_forall_evalEval_eq_zero_iff_eq_of_evalEval_derivative_ne_zero` — Holomorphic implicit function theorem for a bivariate polynomial

```lean
theorem Complex.exists_differentiableOn_forall_evalEval_eq_zero_iff_eq_of_evalEval_derivative_ne_zero
    (F : Polynomial (Polynomial ℂ)) (z₀ w₀ : ℂ)
    (h₀ : F.evalEval z₀ w₀ = 0) (hd : (Polynomial.derivative F).evalEval z₀ w₀ ≠ 0) :
    ∃ (r ρ : ℝ) (φ : ℂ → ℂ), 0 < r ∧ 0 < ρ ∧ φ z₀ = w₀ ∧
      DifferentiableOn ℂ φ (Metric.ball z₀ r) ∧
      (∀ z ∈ Metric.ball z₀ r, φ z ∈ Metric.ball w₀ ρ ∧ F.evalEval z (φ z) = 0) ∧
      (∀ z ∈ Metric.ball z₀ r, ∀ w ∈ Metric.ball w₀ ρ, F.evalEval z w = 0 → w = φ z)
```

### `Complex.exists_differentiableOn_forall_eval_map_eval_eq_zero_iff_eq_of_derivative_ne_zero_pi`

`Thm_Complex_exists_differentiableOn_forall_eval_map_eval_eq_zero_iff_eq_of_derivative_ne_zero_pi` — Holomorphic implicit function for a polynomial in one dependent variable

```lean
theorem Complex.exists_differentiableOn_forall_eval_map_eval_eq_zero_iff_eq_of_derivative_ne_zero_pi
    {n : ℕ} (F : Polynomial (MvPolynomial (Fin n) ℂ)) (z₀ : Fin n → ℂ) (w₀ : ℂ)
    (h₀ : (F.map (MvPolynomial.eval z₀)).eval w₀ = 0)
    (hd : ((Polynomial.derivative F).map (MvPolynomial.eval z₀)).eval w₀ ≠ 0) :
    ∃ (r ρ : ℝ) (φ : (Fin n → ℂ) → ℂ), 0 < r ∧ 0 < ρ ∧ φ z₀ = w₀ ∧
      DifferentiableOn ℂ φ (Metric.ball z₀ r) ∧ ContDiffOn ℂ ⊤ φ (Metric.ball z₀ r) ∧
      (∀ z ∈ Metric.ball z₀ r, φ z ∈ Metric.ball w₀ ρ ∧ (F.map (MvPolynomial.eval z)).eval (φ z) = 0) ∧
      (∀ z ∈ Metric.ball z₀ r, ∀ w ∈ Metric.ball w₀ ρ, (F.map (MvPolynomial.eval z)).eval w = 0 → w = φ z)
```

### `Complex.exists_differentiable_eqOn_halfPlane_of_forall_exists_entire_mul_eq`

`Thm_Complex_exists_differentiable_eqOn_halfPlane_of_forall_exists_entire_mul_eq` — Entire continuation glued from local quotients Z/(cE)

```lean
theorem Complex.exists_differentiable_eqOn_halfPlane_of_forall_exists_entire_mul_eq
    (L : ℂ → ℂ) (σ : ℝ) (hL : ContinuousOn L {s : ℂ | σ < s.re})
    (h : ∀ s₁ : ℂ, ∃ (Z E : ℂ → ℂ) (c : ℂ) (σ' : ℝ), Differentiable ℂ Z ∧ Differentiable ℂ E ∧ c ≠ 0 ∧
      E s₁ ≠ 0 ∧ ∀ s : ℂ, σ' < s.re → Z s = c * E s * L s) :
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ ∃ σ'' : ℝ, ∀ s : ℂ, σ'' < s.re → Λ s = L s
```

### `Complex.exists_forall_ne_zero_re_gt_of_differentiableOn_of_exists_ne_zero`

`Thm_Complex_exists_forall_ne_zero_re_gt_of_differentiableOn_of_exists_ne_zero` — Simultaneous non-vanishing far right in a half-plane

```lean
theorem Complex.exists_forall_ne_zero_re_gt_of_differentiableOn_of_exists_ne_zero
    {ι : Type} (t : Finset ι) (f : ι → ℂ → ℂ) (σ : ℝ)
    (hf : ∀ i ∈ t, DifferentiableOn ℂ (f i) {s : ℂ | σ < s.re})
    (hne : ∀ i ∈ t, ∃ s : ℂ, σ < s.re ∧ f i s ≠ 0)
    (σ' : ℝ) :
    ∃ s : ℂ, σ' < s.re ∧ σ < s.re ∧ ∀ i ∈ t, f i s ≠ 0
```

### `Complex.exists_forall_norm_Gamma_le_mul_exp_and_exp_le_mul_norm_Gamma_of_re_mem_Icc_of_one_le_abs_im`

`Thm_Complex_exists_forall_norm_Gamma_le_mul_exp_and_exp_le_mul_norm_Gamma_of_re_mem_Icc_of_one_le_abs_im` — Two-sided exponential bounds for Γ on vertical strips

```lean
theorem Complex.exists_forall_norm_Gamma_le_mul_exp_and_exp_le_mul_norm_Gamma_of_re_mem_Icc_of_one_le_abs_im
    (σ₁ σ₂ : ℝ) :
    ∃ (A : ℝ) (N : ℕ), ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₂ → 1 ≤ |w.im| →
      ‖Complex.Gamma w‖ ≤ A * (1 + |w.im|) ^ N * Real.exp (-(Real.pi / 2) * |w.im|) ∧
        Real.exp (-(Real.pi / 2) * |w.im|) ≤ A * (1 + |w.im|) ^ N * ‖Complex.Gamma w‖
```

### `Complex.exists_forall_norm_digamma_le_mul_log_and_norm_logDeriv_GammaReal_le_and_norm_logDeriv_GammaComplex_le_of_le_re`

`Thm_Complex_exists_forall_norm_digamma_le_mul_log_and_norm_logDeriv_GammaReal_le_and_norm_logDeriv_GammaComplex_le_of_le_re` — Logarithmic growth of ψ and archimedean Γ-factors in a strip

```lean
theorem Complex.exists_forall_norm_digamma_le_mul_log_and_norm_logDeriv_GammaReal_le_and_norm_logDeriv_GammaComplex_le_of_le_re
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, δ ≤ s.re → s.re ≤ 2 →
      ‖Complex.digamma s‖ ≤ C * Real.log (2 + |s.im|) ∧
      ‖logDeriv Complex.Gammaℝ s‖ ≤ C * Real.log (2 + |s.im|) ∧
      ‖logDeriv Complex.Gammaℂ s‖ ≤ C * Real.log (2 + |s.im|)
```

### `Complex.exists_forall_norm_digamma_le_mul_log_norm_and_norm_logDeriv_GammaReal_le_and_norm_logDeriv_GammaComplex_le_of_le_re`

`Thm_Complex_exists_forall_norm_digamma_le_mul_log_norm_and_norm_logDeriv_GammaReal_le_and_norm_logDeriv_GammaComplex_le_of_le_re` — Logarithmic growth of ψ and archimedean Γ-factors on a half-plane

```lean
theorem Complex.exists_forall_norm_digamma_le_mul_log_norm_and_norm_logDeriv_GammaReal_le_and_norm_logDeriv_GammaComplex_le_of_le_re
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, δ ≤ s.re →
      ‖Complex.digamma s‖ ≤ C * Real.log (2 + ‖s‖) ∧
      ‖logDeriv Complex.Gammaℝ s‖ ≤ C * Real.log (2 + ‖s‖) ∧
      ‖logDeriv Complex.Gammaℂ s‖ ≤ C * Real.log (2 + ‖s‖)
```

### `Complex.exists_forall_norm_digamma_le_mul_log_of_le_re`

`Thm_Complex_exists_forall_norm_digamma_le_mul_log_of_le_re` — Logarithmic growth of digamma in a vertical strip

```lean
theorem Complex.exists_forall_norm_digamma_le_mul_log_of_le_re
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, δ ≤ s.re → s.re ≤ 2 →
      ‖Complex.digamma s‖ ≤ C * Real.log (2 + |s.im|)
```

### `Complex.exists_forall_not_countable_setOf_re_gt_mem_of_finite`

`Thm_Complex_exists_forall_not_countable_setOf_re_gt_mem_of_finite` — Pigeonhole over abscissae for a finite family in ℂ

```lean
theorem Complex.exists_forall_not_countable_setOf_re_gt_mem_of_finite
    {ι : Type} [Finite ι] (S : ι → Set ℂ)
    (h : ∀ σ' : ℝ, ¬ Set.Countable {s : ℂ | σ' < s.re ∧ ∃ i, s ∈ S i}) :
    ∃ i, ∀ σ' : ℝ, ¬ Set.Countable {s : ℂ | σ' < s.re ∧ s ∈ S i}
```

### `Complex.exists_grid_reProdIm`

`Thm_Complex_exists_grid_reProdIm` — Finite δ-net of a complex rectangle with short δ-chains

```lean
theorem Complex.exists_grid_reProdIm {a₁ a₂ b₁ b₂ δ : ℝ} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) (hδ : 0 < δ) :
    ∃ (m n : ℕ) (c : Fin (m + 1) × Fin (n + 1) → ℂ),
      (∀ i, c i ∈ Set.Icc a₁ a₂ ×ℂ Set.Icc b₁ b₂) ∧
      (∀ w ∈ Set.Icc a₁ a₂ ×ℂ Set.Icc b₁ b₂, ∃ i, dist w (c i) < δ) ∧
      (∀ i j, ∃ (L : ℕ) (π : ℕ → Fin (m + 1) × Fin (n + 1)),
        L ≤ m + n ∧ π 0 = i ∧ π L = j ∧ ∀ l < L, dist (c (π l)) (c (π (l + 1))) ≤ δ)
```

### `Complex.exists_hasDerivAt_of_starConvex`

`Thm_Complex_exists_hasDerivAt_of_starConvex` — Primitives of holomorphic functions on star-shaped domains

```lean
theorem Complex.exists_hasDerivAt_of_starConvex {U : Set ℂ} (hU : IsOpen U) {q : ℂ} (hq : q ∈ U)
    (hstar : StarConvex ℝ q U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    ∃ g : ℂ → ℂ, g q = 0 ∧ ∀ z ∈ U, HasDerivAt g (f z) z
```

### `Complex.exists_le_setIntegral_ball_log_norm_sum_mul`

`Thm_Complex_exists_le_setIntegral_ball_log_norm_sum_mul` — Uniform lower bound for int_Blog|a·φ| over unit covectors

```lean
theorem Complex.exists_le_setIntegral_ball_log_norm_sum_mul {r : ℕ} {φ : ℂ → Fin r → ℂ} {z_c : ℂ} {R R' : ℝ}
    (hR : 0 < R) (hRR' : 3 * R < R') (hφ : ∀ j, DifferentiableOn ℂ (fun z ↦ φ z j) (Metric.ball z_c R'))
    (hnd : ∀ a : Fin r → ℂ, a ≠ 0 → ∃ z ∈ Metric.ball z_c R', ∑ j, a j * φ z j ≠ 0) :
    ∃ C : ℝ, ∀ a : Fin r → ℂ, ‖a‖ = 1 →
      IntegrableOn (fun z ↦ Real.log ‖∑ j, a j * φ z j‖) (Metric.ball z_c R) ∧
      C ≤ ∫ z in Metric.ball z_c R, Real.log ‖∑ j, a j * φ z j‖
```

### `Complex.exists_lipschitzWith_divided_minor`

`Thm_Complex_exists_lipschitzWith_divided_minor` — Lipschitz divided minors of a holomorphic map

```lean
theorem Complex.exists_lipschitzWith_divided_minor {r : ℕ} {φ : ℂ → Fin r → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hφ : ∀ i, DifferentiableOn ℂ (fun z ↦ φ z i) (Metric.ball c R)) :
    ∃ ρ > 0, ∃ L ≥ 0, ∃ Ψ : ℂ → ℂ → (Fin r × Fin r → ℂ),
      (∀ w ∈ Metric.ball c ρ, ∀ z ∈ Metric.ball c ρ, ∀ p : Fin r × Fin r,
          φ w p.1 * φ z p.2 - φ w p.2 * φ z p.1 = (z - w) * Ψ w z p) ∧
      (∀ w ∈ Metric.ball c ρ, ∀ p : Fin r × Fin r,
          Ψ w w p = φ w p.1 * deriv (fun z ↦ φ z p.2) w - φ w p.2 * deriv (fun z ↦ φ z p.1) w) ∧
      (∀ w ∈ Metric.ball c ρ, ∀ z ∈ Metric.ball c ρ, ∀ z' ∈ Metric.ball c ρ,
          ‖Ψ w z - Ψ w z'‖ ≤ L * ‖z - z'‖)
```

### `Complex.exists_mul_norm_sub_le_iSup_norm_minor_of_wedge_deriv_ne_zero`

`Thm_Complex_exists_mul_norm_sub_le_iSup_norm_minor_of_wedge_deriv_ne_zero` — Minor lower bound near an immersed point of a holomorphic curve

```lean
theorem Complex.exists_mul_norm_sub_le_iSup_norm_minor_of_wedge_deriv_ne_zero {r : ℕ} {φ : ℂ → Fin r → ℂ} {c : ℂ}
    {R : ℝ} (hR : 0 < R) (hφ : ∀ i, DifferentiableOn ℂ (fun z ↦ φ z i) (Metric.ball c R))
    (hw : ∃ p : Fin r × Fin r,
      φ c p.1 * deriv (fun z ↦ φ z p.2) c - φ c p.2 * deriv (fun z ↦ φ z p.1) c ≠ 0) :
    ∃ ρ > 0, ∃ C > 0, ∀ z ∈ Metric.ball c ρ, ∀ w ∈ Metric.ball c ρ,
      C * ‖z - w‖ ≤ ⨆ p : Fin r × Fin r, ‖φ z p.1 * φ w p.2 - φ z p.2 * φ w p.1‖
```

### `Complex.exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto`

`Thm_Complex_exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto` — Boundedness of a continuous logarithm near a non-zero boundary limit

```lean
theorem Complex.exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto
    {Λ ℓ : ℝ → ℂ} {a : ℝ} {c : ℂ} (hΛ : ContinuousOn Λ (Set.Ioi a))
    (hexp : ∀ s : ℝ, a < s → Complex.exp (Λ s) = ℓ s)
    (hlim : Filter.Tendsto ℓ (nhdsWithin a (Set.Ioi a)) (nhds c)) (hc : c ≠ 0) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ s : ℝ, a < s → s < a + δ → ‖Λ s‖ ≤ C
```

### `Complex.exists_ringHom_comp_eq_subtype_of_isDiscreteValuationRing_of_finite_residueField`

`Thm_Complex_exists_ringHom_comp_eq_subtype_of_isDiscreteValuationRing_of_finite_residueField` — A complete DVR with finite residue field embeds into ℂ

```lean
theorem Complex.exists_ringHom_comp_eq_subtype_of_isDiscreteValuationRing_of_finite_residueField
    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] [Finite (IsLocalRing.ResidueField O')] [CharZero O']
    (R : Subring ℂ) [Countable R] (iota : R →+* O') (hinj : Function.Injective iota) :
    ∃ e' : O' →+* ℂ, ∀ x : R, e' (iota x) = x
```

### `Complex.exists_ringHom_integralClosure_int_apply_eq_of_isPrimitiveRoot`

`Thm_Complex_exists_ringHom_integralClosure_int_apply_eq_of_isPrimitiveRoot` — Reduction of ℤ̄ to K sending e^{2π i/M} to ζ

```lean
theorem Complex.exists_ringHom_integralClosure_int_apply_eq_of_isPrimitiveRoot
    (ℓ : ℕ) [Fact ℓ.Prime] (M : ℕ) [NeZero M] (hℓM : ¬ ℓ ∣ M)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ]
    (ζ : K) (hζ : IsPrimitiveRoot ζ M) :
    ∃ φ : integralClosure ℤ ℂ →+* K,
      ∀ z : integralClosure ℤ ℂ,
        (z : ℂ) = Complex.exp (2 * Real.pi * Complex.I / M) → φ z = ζ
```

### `Complex.exists_trivialization_add_pow`

`Thm_Complex_exists_trivialization_add_pow` — Trivialising ζ ↦ b + ζ^e away from a ray

```lean
theorem Complex.exists_trivialization_add_pow {b : ℂ} {θ : ℝ} {e : ℕ} (he : e ≠ 0) {U : Set ℂ}
    (hray : ∀ z ∈ U, ∀ t : ℝ, 0 ≤ t → b + t * Complex.exp (θ * Complex.I) ≠ z) :
    ∃ H : ((fun ζ : ℂ => b + ζ ^ e) ⁻¹' U) ≃ₜ U × Fin e,
      ∀ ζ, ((H ζ).1 : ℂ) = b + (ζ : ℂ) ^ e
```

### `Complex.forall_cpow_mul_eval_mul_eval_eq_and_exists_finset_forall_eq_mul_of_infinite`

`Thm_Complex_forall_cpow_mul_eval_mul_eval_eq_and_exists_finset_forall_eq_mul_of_infinite` — Laurent identity in q^{-s} and cancellation of the denominator

```lean
theorem Complex.forall_cpow_mul_eval_mul_eval_eq_and_exists_finset_forall_eq_mul_of_infinite
    (q : ℕ) (hq : 1 < q) (P Q₁ Q₂ : Polynomial ℂ) (hQ₂ : Q₂ ≠ 0) (m k : ℤ) (γ Zd : ℂ → ℂ) (S S₁ : Set ℂ)
    (hS : {t : ℝ | (t : ℂ) ∈ S}.Infinite)
    (h : ∀ s ∈ S,
      (q : ℂ) ^ ((m : ℂ) * s) * P.eval ((q : ℂ) ^ (-s)) * Q₂.eval ((q : ℂ) ^ (-s)) =
        Q₁.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ ((k : ℂ) * s))
    (h₁ : ∀ s ∈ S₁,
      Zd s * Q₂.eval ((q : ℂ) ^ (-s)) = Q₁.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ ((k : ℂ) * s) * γ s) :
    (∀ s : ℂ, (q : ℂ) ^ ((m : ℂ) * s) * P.eval ((q : ℂ) ^ (-s)) * Q₂.eval ((q : ℂ) ^ (-s)) =
        Q₁.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ ((k : ℂ) * s)) ∧
    ∃ R : Finset ℝ, ∀ s ∈ S₁, (q : ℝ) ^ (-s.re) ∉ R →
      Zd s = γ s * ((q : ℂ) ^ ((m : ℂ) * s) * P.eval ((q : ℂ) ^ (-s)))
```

### `Complex.forall_mul_polynomial_eval_cpow_eq_of_differentiableOn_of_forall_lt_re`

`Thm_Complex_forall_mul_polynomial_eval_cpow_eq_of_differentiableOn_of_forall_lt_re` — Analytic continuation of a Dirichlet-polynomial identity to a half-plane

```lean
theorem Complex.forall_mul_polynomial_eval_cpow_eq_of_differentiableOn_of_forall_lt_re
    (N : ℝ) (hN : 0 < N) (σ₂ σ₀ : ℝ) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f {s : ℂ | σ₂ < s.re})
    (P Q : Polynomial ℂ)
    (h : ∀ s : ℂ, σ₀ < s.re → f s * Q.eval ((N : ℂ) ^ (-s)) = P.eval ((N : ℂ) ^ (-s))) :
    ∀ s : ℂ, σ₂ < s.re → f s * Q.eval ((N : ℂ) ^ (-s)) = P.eval ((N : ℂ) ^ (-s))
```

### `Complex.hasDerivAt_circleIntegral_mul_deriv_div_sub`

`Thm_Complex_hasDerivAt_circleIntegral_mul_deriv_div_sub` — Holomorphic dependence on t of oint G Φ'/(Φ-t)

```lean
theorem Complex.hasDerivAt_circleIntegral_mul_deriv_div_sub
    {Φ G : ℂ → ℂ} {z₀ t₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hΦ : ∀ z ∈ Metric.sphere z₀ r, AnalyticAt ℂ Φ z)
    (hG : ∀ z ∈ Metric.sphere z₀ r, AnalyticAt ℂ G z)
    (hne : ∀ z ∈ Metric.sphere z₀ r, Φ z ≠ t₀) :
    HasDerivAt (fun t : ℂ => ∮ z in C(z₀, r), G z * deriv Φ z / (Φ z - t))
      (∮ z in C(z₀, r), deriv G z / (Φ z - t₀)) t₀
```

### `Complex.hasSum_one_div_add_one_sub_one_div_add_eq_digamma_add_eulerMascheroniConstant`

`Thm_Complex_hasSum_one_div_add_one_sub_one_div_add_eq_digamma_add_eulerMascheroniConstant` — Gauss partial-fraction series for ψ on Re s>0

```lean
theorem Complex.hasSum_one_div_add_one_sub_one_div_add_eq_digamma_add_eulerMascheroniConstant
    (s : ℂ) (hs : 0 < s.re) :
    HasSum (fun k : ℕ => (1 : ℂ) / ((k : ℂ) + 1) - 1 / ((k : ℂ) + s))
      (Complex.digamma s + (Real.eulerMascheroniConstant : ℂ))
```

### `Complex.integrableOn_and_integral_Ioi_cpow_mul_one_add_cpow_neg_eq_Gamma_mul_Gamma_div`

`Thm_Complex_integrableOn_and_integral_Ioi_cpow_mul_one_add_cpow_neg_eq_Gamma_mul_Gamma_div` — Half-line Euler beta integral equals Γ(a)Γ(b)/Γ(a+b)

```lean
theorem Complex.integrableOn_and_integral_Ioi_cpow_mul_one_add_cpow_neg_eq_Gamma_mul_Gamma_div
    (a b : ℂ) (ha : 0 < a.re) (hb : 0 < b.re) :
    IntegrableOn (fun v : ℝ => (v : ℂ) ^ (a - 1) * (((1 + v : ℝ)) : ℂ) ^ (-(a + b))) (Set.Ioi 0) ∧
      ∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ (a - 1) * (((1 + v : ℝ)) : ℂ) ^ (-(a + b)) =
        Complex.Gamma a * Complex.Gamma b / Complex.Gamma (a + b)
```

### `Complex.integrableOn_ball_iff_integrableOn_smul_circleMap`

`Thm_Complex_integrableOn_ball_iff_integrableOn_smul_circleMap` — Integrability on a disc via polar coordinates

```lean
theorem Complex.integrableOn_ball_iff_integrableOn_smul_circleMap {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℂ → E) (c : ℂ) (R : ℝ) :
    MeasureTheory.IntegrableOn f (Metric.ball c R) ↔
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ ↦ p.1 • f (circleMap c p.1 p.2))
        (Set.Ioo 0 R ×ˢ Set.Ioo (-Real.pi) Real.pi)
```

### `Complex.integrable_and_integral_prod_Ioi_exp_neg_add_mul_cpow_mul_cpow_mul_add_cpow_neg`

`Thm_Complex_integrable_and_integral_prod_Ioi_exp_neg_add_mul_cpow_mul_cpow_mul_add_cpow_neg` — Dirichlet double integral Γ(α+β-γ)Γ(α)Γ(β)/Γ(α+β)

```lean
theorem Complex.integrable_and_integral_prod_Ioi_exp_neg_add_mul_cpow_mul_cpow_mul_add_cpow_neg
    (α β γ : ℂ) (hα : 0 < α.re) (hβ : 0 < β.re) (hγ : 0 < (α + β - γ).re) :
    Integrable (fun p : ℝ × ℝ => Complex.exp (-(((p.1 + p.2 : ℝ)) : ℂ)) * (p.1 : ℂ) ^ (α - 1) *
        (p.2 : ℂ) ^ (β - 1) * (((p.1 + p.2 : ℝ)) : ℂ) ^ (-γ))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Ioi (0 : ℝ)))) ∧
      ∫ p : ℝ × ℝ, Complex.exp (-(((p.1 + p.2 : ℝ)) : ℂ)) * (p.1 : ℂ) ^ (α - 1) *
          (p.2 : ℂ) ^ (β - 1) * (((p.1 + p.2 : ℝ)) : ℂ) ^ (-γ)
        ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Ioi (0 : ℝ)))) =
        Complex.Gamma (α + β - γ) * Complex.Gamma α * Complex.Gamma β / Complex.Gamma (α + β)
```

### `Complex.integral_Ioi_integral_Ioi_cpow_mul_one_add_cpow_neg_mul_one_add_add_cpow_neg_of_balance`

`Thm_Complex_integral_Ioi_integral_Ioi_cpow_mul_one_add_cpow_neg_mul_one_add_add_cpow_neg_of_balance` — Balanced double Euler integral in closed Gamma form

```lean
theorem Complex.integral_Ioi_integral_Ioi_cpow_mul_one_add_cpow_neg_mul_one_add_add_cpow_neg_of_balance
    (A a b D : ℂ) (hA : 0 < A.re) (hbA : 0 < (b - A).re) (haD : 0 < (a + D - A).re) (hba : 0 < (b - a).re) :
    ∫ x in Set.Ioi (0:ℝ), ∫ y in Set.Ioi (0:ℝ),
        (x : ℂ) ^ (A - 1) * ((1 + x : ℝ) : ℂ) ^ (-a) *
          ((y : ℂ) ^ (a + D - 1) * ((1 + y : ℝ) : ℂ) ^ (-b)) * ((1 + x + y : ℝ) : ℂ) ^ (-D)
      = Complex.Gamma A * Complex.Gamma (b - A) * Complex.Gamma (a + D - A) * Complex.Gamma (b - a) /
          (Complex.Gamma b * Complex.Gamma (D + b - A))
```

### `Complex.integral_ball_eq_integral_smul_circleMap`

`Thm_Complex_integral_ball_eq_integral_smul_circleMap` — Polar coordinates on a disc

```lean
theorem Complex.integral_ball_eq_integral_smul_circleMap {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℂ → E) (c : ℂ) (R : ℝ) :
    ∫ z in Metric.ball c R, f z
      = ∫ p in Set.Ioo 0 R ×ˢ Set.Ioo (-Real.pi) Real.pi, p.1 • f (circleMap c p.1 p.2)
```

### `Complex.integral_ball_eq_integral_smul_intervalIntegral_circleMap`

`Thm_Complex_integral_ball_eq_integral_smul_intervalIntegral_circleMap` — Polar coordinates on a disc, iterated form

```lean
theorem Complex.integral_ball_eq_integral_smul_intervalIntegral_circleMap {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℂ → E} {c : ℂ} {R : ℝ}
    (hf : MeasureTheory.IntegrableOn f (Metric.ball c R)) :
    ∫ z in Metric.ball c R, f z = ∫ r in Set.Ioo 0 R, r • ∫ θ in 0..2 * Real.pi, f (circleMap c r θ)
```

### `Complex.integral_inv_sub_mul_dbar_eq_neg_pi_mul`

`Thm_Complex_integral_inv_sub_mul_dbar_eq_neg_pi_mul` — One-pole Cauchy–Pompeiu formula for C¹ test functions

```lean
theorem Complex.integral_inv_sub_mul_dbar_eq_neg_pi_mul
    (a : ℂ) (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h) (hsupp : HasCompactSupport h) :
    ∫ z, (z - a)⁻¹ * ((fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2) = -π * h a
```

### `Complex.integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv`

`Thm_Complex_integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv` — Argument principle in Stokes form for algebraic local models

```lean
theorem Complex.integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv
    (U : Set ℂ) (hU : IsOpen U) (Φ : ℂ → ℂ) (n : ℂ → ℤ)
    (hloc : ∀ τ ∈ U, ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ τ ∧ Ψ τ ≠ 0 ∧
      Φ =ᶠ[𝓝 τ] fun z => (z - τ) ^ (n τ) * Ψ z)
    (E E' : ℂ → ℂ) (hE : ∀ z ∈ U, HasDerivAt E (E' z) z)
    (h : ℂ → ℂ) (hh : ContDiff ℝ 2 h) (hsupp : HasCompactSupport h) (hU' : tsupport h ⊆ U) :
    Integrable (fun z : ℂ => E z / Φ z *
        (fderiv ℝ Φ z 1 * fderiv ℝ h z I - fderiv ℝ Φ z I * fderiv ℝ h z 1)) ∧
    Integrable (fun z : ℂ => E' z * h z *
        ((fderiv ℝ Φ z 1 + I * fderiv ℝ Φ z I) / 2 / Φ z)) ∧
    I / π * (∫ z : ℂ, E z / Φ z *
        (fderiv ℝ Φ z 1 * fderiv ℝ h z I - fderiv ℝ Φ z I * fderiv ℝ h z 1)) +
      2 * ∑ᶠ a : ℂ, (n a : ℂ) * E a * h a =
    2 / π * ∫ z : ℂ, E' z * h z * ((fderiv ℝ Φ z 1 + I * fderiv ℝ Φ z I) / 2 / Φ z)
```

### `Complex.integral_modularFundamentalDomain_eq_boundary_of_hasFDerivAt`

`Thm_Complex_integral_modularFundamentalDomain_eq_boundary_of_hasFDerivAt` — Stokes' theorem for Φ dz on the modular fundamental domain

```lean
theorem Complex.integral_modularFundamentalDomain_eq_boundary_of_hasFDerivAt
    (Φ : ℂ → ℂ) (Φ' : ℂ → ℂ →L[ℝ] ℂ) (U : Set ℂ) (δ : ℝ) (hδ : 0 < δ) (hU : IsOpen U)
    (hDU : {z : ℂ | |z.re| ≤ 1 / 2 ∧ 1 ≤ ‖z‖ ∧ 0 < z.im} ⊆ U)
    (hd : ∀ z ∈ U, HasFDerivAt Φ (Φ' z) z) (hc : ContinuousOn Φ' U)
    (hΦ : ∃ C : ℝ, ∀ z ∈ U, ‖Φ z‖ ≤ C * Real.exp (-δ * z.im))
    (hΦ' : ∃ C : ℝ, ∀ z ∈ U, ‖Φ' z‖ ≤ C * Real.exp (-δ * z.im)) :
    (∫ z in {z : ℂ | |z.re| ≤ 1 / 2 ∧ 1 ≤ ‖z‖ ∧ 0 < z.im}, (Complex.I • Φ' z 1 - Φ' z Complex.I)) =
      Complex.I • (∫ y in Set.Ioi (Real.sqrt 3 / 2), Φ (1 / 2 + y * Complex.I))
        - Complex.I • (∫ y in Set.Ioi (Real.sqrt 3 / 2), Φ (-(1 / 2) + y * Complex.I))
        - ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
            Φ (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I))
```

### `Complex.integral_mul_dbar_eq_neg_pi_mul_finsum_residue`

`Thm_Complex_integral_mul_dbar_eq_neg_pi_mul_finsum_residue` — Cauchy–Pompeiu formula for simple poles

```lean
theorem Complex.integral_mul_dbar_eq_neg_pi_mul_finsum_residue
    (U : Set ℂ) (hU : IsOpen U) (F c : ℂ → ℂ)
    (hloc : ∀ a ∈ U, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      ∀ᶠ z in 𝓝[≠] a, F z = c a / (z - a) + g z)
    (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h) (hsupp : HasCompactSupport h) (hU' : tsupport h ⊆ U) :
    ∫ z, F z * ((fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2) = -π * ∑ᶠ a, c a * h a
```

### `Complex.integral_mul_dbar_eq_zero_of_differentiableOn`

`Thm_Complex_integral_mul_dbar_eq_zero_of_differentiableOn` — Holomorphic functions are weak solutions of partial̄

```lean
theorem Complex.integral_mul_dbar_eq_zero_of_differentiableOn
    (V : Set ℂ) (hV : IsOpen V) (G : ℂ → ℂ) (hG : DifferentiableOn ℂ G V)
    (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h) (hsupp : HasCompactSupport h) (hV' : tsupport h ⊆ V) :
    ∫ z, G z * ((fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2) = 0
```

### `Complex.integral_mul_logDeriv_mul_dbar_eq_neg_pi_mul_finsum`

`Thm_Complex_integral_mul_logDeriv_mul_dbar_eq_neg_pi_mul_finsum` — Stokes form of the argument principle for E F'/F

```lean
theorem Complex.integral_mul_logDeriv_mul_dbar_eq_neg_pi_mul_finsum
    (U : Set ℂ) (hU : IsOpen U) (F : ℂ → ℂ) (hF : ∀ z ∈ U, MeromorphicAt F z)
    (hF' : ∀ z ∈ U, meromorphicOrderAt F z ≠ ⊤)
    (E : ℂ → ℂ) (hE : DifferentiableOn ℂ E U)
    (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h) (hsupp : HasCompactSupport h) (hU' : tsupport h ⊆ U) :
    ∫ z, E z * (deriv F z / F z) * ((fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2) =
      -π * ∑ᶠ a, (((meromorphicOrderAt F a).untop₀ : ℤ) : ℂ) * E a * h a
```

### `Complex.integral_radial_loop_eq_two_mul_I_mul_setIntegral`

`Thm_Complex_integral_radial_loop_eq_two_mul_I_mul_setIntegral` — Green–Pompeiu formula on a radially parametrised region

```lean
theorem Complex.integral_radial_loop_eq_two_mul_I_mul_setIntegral
    (c : ℂ) (r : ℝ → ℝ) (hcont : Continuous r) (hper : Function.Periodic r (2 * Real.pi))
    (hpos : ∀ φ, 0 < r φ)
    (N : ℕ) (φs : Fin (N + 1) → ℝ) (hφ0 : φs 0 = 0) (hφN : φs (Fin.last N) = 2 * Real.pi)
    (hmono : StrictMono φs)
    (hC2 : ∀ i : Fin N, ContDiffOn ℝ 2 r (Set.Icc (φs i.castSucc) (φs i.succ)))
    (P Q : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hKU : ∀ z : ℂ, ‖z - c‖ ≤ r (arg (z - c)) → z ∈ U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) :
    ∫ φ in (0 : ℝ)..(2 * Real.pi),
        (P (c + r φ * exp (φ * I)) * ((((deriv r φ : ℝ) : ℂ) + r φ * I) * exp (φ * I)) +
          Q (c + r φ * exp (φ * I)) *
            (starRingEnd ℂ) ((((deriv r φ : ℝ) : ℂ) + r φ * I) * exp (φ * I))) =
      2 * I * ∫ z in {z : ℂ | ‖z - c‖ ≤ r (arg (z - c))},
        ((fderiv ℝ P z 1 + I * fderiv ℝ P z I) / 2 - (fderiv ℝ Q z 1 - I * fderiv ℝ Q z I) / 2)
```

### `Complex.integral_radial_loop_eq_two_pi_I_mul_sum_residue`

`Thm_Complex_integral_radial_loop_eq_two_pi_I_mul_sum_residue` — Residue theorem for a radially parametrised star-shaped loop

```lean
theorem Complex.integral_radial_loop_eq_two_pi_I_mul_sum_residue
    (c : ℂ) (r : ℝ → ℝ) (hcont : Continuous r) (hper : Function.Periodic r (2 * Real.pi))
    (hpos : ∀ φ, 0 < r φ)
    (N : ℕ) (φs : Fin (N + 1) → ℝ) (hφ0 : φs 0 = 0) (hφN : φs (Fin.last N) = 2 * Real.pi)
    (hmono : StrictMono φs)
    (hC2 : ∀ i : Fin N, ContDiffOn ℝ 2 r (Set.Icc (φs i.castSucc) (φs i.succ)))
    (f : ℂ → ℂ) (P : Finset ℂ) (res : ℂ → ℂ)
    (hint : ∀ p ∈ P, ‖p - c‖ < r (arg (p - c)))
    (han : ∀ z : ℂ, ‖z - c‖ ≤ r (arg (z - c)) → z ∉ P → AnalyticAt ℂ f z)
    (hpole : ∀ p ∈ P, ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧
      ∀ᶠ z in nhdsWithin p {p}ᶜ, f z = res p / (z - p) + g z) :
    ∫ φ in (0 : ℝ)..(2 * Real.pi),
        f (c + r φ * exp (φ * I)) * ((((deriv r φ : ℝ) : ℂ) + r φ * I) * exp (φ * I)) =
      2 * Real.pi * I * ∑ p ∈ P, res p
```

### `Complex.isOpen_image_and_exists_differentiableOn_leftInverse_of_injOn_ball`

`Thm_Complex_isOpen_image_and_exists_differentiableOn_leftInverse_of_injOn_ball` — Injective holomorphic map on a disc: open image, holomorphic inverse

```lean
theorem Complex.isOpen_image_and_exists_differentiableOn_leftInverse_of_injOn_ball
    (f : ℂ → ℂ) (z₀ : ℂ) (ε : ℝ) (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ ε)) (hinj : Set.InjOn f (Metric.ball z₀ ε)) :
    IsOpen (f '' Metric.ball z₀ ε) ∧
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (f '' Metric.ball z₀ ε) ∧
      (∀ z ∈ Metric.ball z₀ ε, g (f z) = z) ∧
      (∀ w ∈ f '' Metric.ball z₀ ε, g w ∈ Metric.ball z₀ ε ∧ f (g w) = w)
```

### `Complex.locallyIntegrableOn_of_simplePoles`

`Thm_Complex_locallyIntegrableOn_of_simplePoles` — Functions with at most simple poles are locally integrable

```lean
theorem Complex.locallyIntegrableOn_of_simplePoles
    (U : Set ℂ) (hU : IsOpen U) (F c : ℂ → ℂ)
    (hloc : ∀ a ∈ U, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      ∀ᶠ z in 𝓝[≠] a, F z = c a / (z - a) + g z) :
    LocallyIntegrableOn F U
```

### `Complex.log_add_log_eq_log_sub_of_re_pos`

`Thm_Complex_log_add_log_eq_log_sub_of_re_pos` — Branch rule for log on the right half-plane

```lean
theorem Complex.log_add_log_eq_log_sub_of_re_pos {u v w : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) (hw : 0 < w.re) (h : u * v = -Complex.I * w) : Complex.log u + Complex.log v = Complex.log w - Real.pi * Complex.I / 2
```

### `Complex.mellinConvergent_cpow_mul_exp_neg_mul_and_mellin_eq`

`Thm_Complex_mellinConvergent_cpow_mul_exp_neg_mul_and_mellin_eq` — Mellin transform of t^ke^{-rt} equals r^{-(s+k)}Γ(s+k)

```lean
theorem Complex.mellinConvergent_cpow_mul_exp_neg_mul_and_mellin_eq
    (k r : ℝ) (hr : 0 < r) (s : ℂ) (hs : -k < s.re) :
    MellinConvergent (fun t : ℝ => ((t : ℂ) ^ (k : ℂ)) * Complex.exp (-((r : ℂ) * (t : ℂ)))) s ∧
    mellin (fun t : ℝ => ((t : ℂ) ^ (k : ℂ)) * Complex.exp (-((r : ℂ) * (t : ℂ)))) s =
      (1 / (r : ℂ)) ^ (s + (k : ℂ)) * Complex.Gamma (s + (k : ℂ))
```

### `Complex.mul_integral_Ioi_integral_Ioi_cpow_add_mul_integral_Ioi_integral_Ioi_cpow_eq_of_balance`

`Thm_Complex_mul_integral_Ioi_integral_Ioi_cpow_add_mul_integral_Ioi_integral_Ioi_cpow_eq_of_balance` — Two-term contiguity relation for balanced double Euler integrals

```lean
theorem Complex.mul_integral_Ioi_integral_Ioi_cpow_add_mul_integral_Ioi_integral_Ioi_cpow_eq_of_balance
    (A a b D : ℂ) (hA : 0 < A.re) (ha : 0 < a.re) (hD : 0 < D.re) (hba : 0 < (b - a).re)
    (hbA : 0 < (b - A + 1).re) (haD : 0 < (a + D - A + 1).re) :
    a * (∫ x in Set.Ioi (0:ℝ), ∫ y in Set.Ioi (0:ℝ),
        (x : ℂ) ^ (A - 1) * ((1 + x : ℝ) : ℂ) ^ (-(a + 1)) *
          ((y : ℂ) ^ (a + D - 1) * ((1 + y : ℝ) : ℂ) ^ (-b)) * ((1 + x + y : ℝ) : ℂ) ^ (-D)) +
    D * (∫ x in Set.Ioi (0:ℝ), ∫ y in Set.Ioi (0:ℝ),
        (x : ℂ) ^ (A - 1) * ((1 + x : ℝ) : ℂ) ^ (-a) *
          ((y : ℂ) ^ (a + D - 1) * ((1 + y : ℝ) : ℂ) ^ (-b)) * ((1 + x + y : ℝ) : ℂ) ^ (-(D + 1)))
      = Complex.Gamma A * Complex.Gamma (b - A + 1) * Complex.Gamma (a + D - A + 1) * Complex.Gamma (b - a) /
          (Complex.Gamma b * Complex.Gamma (D + b - A + 1))
```

### `Complex.neg_re_deriv_div_le_sub_sum_re_inv_sub_of_norm_le_exp_of_ne_zero_of_lt_re`

`Thm_Complex_neg_re_deriv_div_le_sub_sum_re_inv_sub_of_norm_le_exp_of_ne_zero_of_lt_re` — Landau's lemma on the logarithmic derivative

```lean
theorem Complex.neg_re_deriv_div_le_sub_sum_re_inv_sub_of_norm_le_exp_of_ne_zero_of_lt_re
    (f : ℂ → ℂ) (s₀ : ℂ) (r M : ℝ) (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall s₀ r)) (h₀ : f s₀ ≠ 0)
    (hM : ∀ s ∈ Metric.closedBall s₀ r, ‖f s‖ ≤ Real.exp M * ‖f s₀‖)
    (hne : ∀ s ∈ Metric.closedBall s₀ (r / 2), s₀.re < s.re → f s ≠ 0)
    (Z : Finset ℂ) (hZ : ∀ ρ ∈ Z, ρ ∈ Metric.closedBall s₀ (r / 2) ∧ f ρ = 0) :
    -(deriv f s₀ / f s₀).re ≤ 8 * (M + 1) / r - ∑ ρ ∈ Z, ((s₀ - ρ)⁻¹).re
```

### `Complex.normSq_conj_add_conj_mul_eq_and_complete_square`

`Thm_Complex_normSq_conj_add_conj_mul_eq_and_complete_square` — The quadratic form |̄ z+̄ r z|² and its two completions of the square

```lean
theorem Complex.normSq_conj_add_conj_mul_eq_and_complete_square
    (r z : ℂ) :
    (‖(starRingEnd ℂ) z + (starRingEnd ℂ) r * z‖ ^ 2 =
        ‖1 + r‖ ^ 2 * z.re ^ 2 + 4 * r.im * z.re * z.im + ‖1 - r‖ ^ 2 * z.im ^ 2) ∧
    (‖1 + r‖ ^ 2 + ‖1 - r‖ ^ 2 = 2 * (1 + ‖r‖ ^ 2)) ∧
    (‖1 + r‖ ≠ 0 →
      (1 - ‖r‖ ^ 2) ^ 2 + ‖(starRingEnd ℂ) z + (starRingEnd ℂ) r * z‖ ^ 2 =
        ‖1 + r‖ ^ 2 * ((z.re + 2 * r.im * z.im / ‖1 + r‖ ^ 2) ^ 2 +
          ((1 - ‖r‖ ^ 2) * Real.sqrt (z.im ^ 2 + ‖1 + r‖ ^ 2) / ‖1 + r‖ ^ 2) ^ 2)) ∧
    (‖1 - r‖ ≠ 0 →
      (1 - ‖r‖ ^ 2) ^ 2 + ‖(starRingEnd ℂ) z + (starRingEnd ℂ) r * z‖ ^ 2 =
        ‖1 - r‖ ^ 2 * ((z.im + 2 * r.im * z.re / ‖1 - r‖ ^ 2) ^ 2 +
          ((1 - ‖r‖ ^ 2) * Real.sqrt (z.re ^ 2 + ‖1 - r‖ ^ 2) / ‖1 - r‖ ^ 2) ^ 2))
```

### `Complex.norm_deriv_le_mul_norm_and_exp_neg_le_norm_of_forall_ne_zero_of_norm_le_exp`

`Thm_Complex_norm_deriv_le_mul_norm_and_exp_neg_le_norm_of_forall_ne_zero_of_norm_le_exp` — Landau's lemma on F'/F on a zero-free disc

```lean
theorem Complex.norm_deriv_le_mul_norm_and_exp_neg_le_norm_of_forall_ne_zero_of_norm_le_exp
    (F : ℂ → ℂ) (s₀ : ℂ) (R M : ℝ) (hR : 0 < R) (hM : 0 < M)
    (hd : DifferentiableOn ℂ F (Metric.ball s₀ R))
    (hnz : ∀ z ∈ Metric.ball s₀ R, F z ≠ 0)
    (hup : ∀ z ∈ Metric.ball s₀ R, ‖F z‖ ≤ Real.exp M)
    (hlo : Real.exp (-M) ≤ ‖F s₀‖) :
    ∀ s ∈ Metric.closedBall s₀ (R / 2),
      ‖deriv F s‖ ≤ 48 * M / R * ‖F s‖ ∧ Real.exp (-(5 * M)) ≤ ‖F s‖
```

### `Complex.norm_one_sub_inv_exp_and_sq_mul_log_eq_and_contDiff`

`Thm_Complex_norm_one_sub_inv_exp_and_sq_mul_log_eq_and_contDiff` — Inversion identities for ‖1-exp(X/2+2π iTheta)⁻¹‖

```lean
theorem Complex.norm_one_sub_inv_exp_and_sq_mul_log_eq_and_contDiff :
    (∀ X Θ : ℝ, ‖(1 : ℂ) - (Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ)))⁻¹‖ =
        Real.exp (-(X / 2)) * ‖(1 : ℂ) - Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ))‖) ∧
    (∀ X Θ : ℝ, ‖(1 : ℂ) - (Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ)))⁻¹‖ ^ 2 *
          Real.log ‖(1 : ℂ) - (Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ)))⁻¹‖ =
        Real.exp (-X) *
          (‖(1 : ℂ) - Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ))‖ ^ 2 *
              Real.log ‖(1 : ℂ) - Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ))‖ -
            X / 2 * ‖(1 : ℂ) - Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ))‖ ^ 2)) ∧
    (∀ X Θ : ℝ, ‖(1 : ℂ) - Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ))‖ ^ 2 =
        1 - 2 * Real.exp (X / 2) * Real.cos (2 * Real.pi * Θ) + Real.exp X) ∧
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => 1 - 2 * Real.exp (p.1 / 2) * Real.cos (2 * Real.pi * p.2) + Real.exp p.1)
```

### `Complex.sqrt_mul_sqrt_eq_of_re_pos`

`Thm_Complex_sqrt_mul_sqrt_eq_of_re_pos` — Product rule for the principal square root across a quarter-turn

```lean
theorem Complex.sqrt_mul_sqrt_eq_of_re_pos {u v w : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) (hw : 0 < w.re) (h : u * v = -Complex.I * w) : Complex.sqrt u * Complex.sqrt v = Complex.sqrt (-Complex.I) * Complex.sqrt w
```

### `Complex.tsum_int_one_div_add_sq_eq_pi_sq_div_sin_sq`

`Thm_Complex_tsum_int_one_div_add_sq_eq_pi_sq_div_sin_sq` — Partial fraction expansion of π²/sin²(π z)

```lean
theorem Complex.tsum_int_one_div_add_sq_eq_pi_sq_div_sin_sq (z : ℂ) (hz : z ∈ Complex.integerComplement) :
    ∑' n : ℤ, 1 / (z + n) ^ 2 = (π : ℂ) ^ 2 / Complex.sin (π * z) ^ 2
```

### `Complex.tsum_one_div_add_int_pow_four`

`Thm_Complex_tsum_one_div_add_int_pow_four` — Fourth-order Lipschitz formula sum_{n∈ℤ}(x+n)⁻⁴

```lean
theorem Complex.tsum_one_div_add_int_pow_four (x : ℝ) (hx : ∀ n : ℤ, (x : ℝ) ≠ n) :
    ∑' n : ℤ, 1 / ((x : ℂ) + n) ^ 4 =
      (2 * π * I) ^ 4 / 6 *
        (Complex.exp (2 * π * I * x) * (Complex.exp (2 * π * I * x) ^ 2 + 4 * Complex.exp (2 * π * I * x) + 1) /
          (1 - Complex.exp (2 * π * I * x)) ^ 4)
```

### `Complex.tsum_one_div_add_int_pow_three`

`Thm_Complex_tsum_one_div_add_int_pow_three` — Lipschitz formula of order three on the real line

```lean
theorem Complex.tsum_one_div_add_int_pow_three (x : ℝ) (hx : ∀ n : ℤ, (x : ℝ) ≠ n) :
    ∑' n : ℤ, 1 / ((x : ℂ) + n) ^ 3 =
      -((2 * π * I) ^ 3 / 2) *
        (Complex.exp (2 * π * I * x) * (1 + Complex.exp (2 * π * I * x)) / (1 - Complex.exp (2 * π * I * x)) ^ 3)
```

### `Complex.volume_ball_inter_exists_sum_mul_eq_zero_le`

`Thm_Complex_volume_ball_inter_exists_sum_mul_eq_zero_le` — Rare vanishing of a random linear form along a small arc

```lean
theorem Complex.volume_ball_inter_exists_sum_mul_eq_zero_le {n : ℕ} (c : ℂ → Fin n → ℂ) (z₀ : ℂ) (K : Set ℂ)
    (hc : c z₀ ≠ 0) {δ : ℝ} (hδ : ∀ z ∈ K, ‖c z - c z₀‖ ≤ δ) :
    volume {b : Fin n → ℂ | b ∈ Metric.ball 0 1 ∧ ∃ z ∈ K, ∑ j, b j * c z j = 0}
      ≤ ENNReal.ofReal ((n * δ / ‖c z₀‖) ^ 2) * volume (Metric.ball (0 : Fin n → ℂ) 1)
```

### `Complex.volume_ball_inter_exists_sum_mul_eq_zero_le_mul_volume`

`Thm_Complex_volume_ball_inter_exists_sum_mul_eq_zero_le_mul_volume` — Crofton-type bound for random hyperplanes meeting c(S)

```lean
theorem Complex.volume_ball_inter_exists_sum_mul_eq_zero_le_mul_volume {n : ℕ} (c : ℂ → Fin n → ℂ)
    (S : Set ℂ) {η L : ℝ} (hη : 0 < η) (hηc : ∀ z ∈ S, η ≤ ‖c z‖)
    (hLip : ∀ z ∈ S, ∃ δ > 0, ∀ y ∈ Metric.closedBall z δ, ‖c y - c z‖ ≤ L * ‖y - z‖) :
    volume {b : Fin n → ℂ | b ∈ Metric.ball 0 1 ∧ ∃ z ∈ S, ∑ j, b j * c z j = 0}
      ≤ ENNReal.ofReal ((n * L / η) ^ 2 / Real.pi) * volume (Metric.ball (0 : Fin n → ℂ) 1) * volume S
```

### `Complex.volume_ball_inter_norm_sum_mul_le`

`Thm_Complex_volume_ball_inter_norm_sum_mul_le` — Small-value bound for a linear form on the unit polydisc

```lean
theorem Complex.volume_ball_inter_norm_sum_mul_le {n : ℕ} (w : Fin n → ℂ) (hw : w ≠ 0) (ε : ℝ) :
    volume {b : Fin n → ℂ | b ∈ Metric.ball 0 1 ∧ ‖∑ j, b j * w j‖ ≤ ε}
      ≤ ENNReal.ofReal ((ε / ‖w‖) ^ 2) * volume (Metric.ball (0 : Fin n → ℂ) 1)
```

## MvPolynomial (62)

### `MvPolynomial.IsHomogeneous.iterate_pderiv_eq_zero_of_lt`

`Thm_MvPolynomial_IsHomogeneous_iterate_pderiv_eq_zero_of_lt` — Iterated partial derivatives of order >n annihilate degree-n forms

```lean
theorem MvPolynomial.IsHomogeneous.iterate_pderiv_eq_zero_of_lt {σ R : Type*} [CommSemiring R] {φ : MvPolynomial σ R}
    {n : ℕ} (hφ : φ.IsHomogeneous n) (k : σ) {i : ℕ} (hi : n < i) :
    (MvPolynomial.pderiv k)^[i] φ = 0
```

### `MvPolynomial.abv_eval_div_sub_eval_div_le`

`Thm_MvPolynomial_abv_eval_div_sub_eval_div_le` — Non-archimedean Lipschitz bound for a rational function near a point

```lean
theorem MvPolynomial.abv_eval_div_sub_eval_div_le
    {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ)
    {r : ℕ} (A B : MvPolynomial (Fin r) K) (CA CB : ℝ)
    (hA : ∀ m, μ (A.coeff m) ≤ CA) (hB : ∀ m, μ (B.coeff m) ≤ CB)
    (x v : Fin r → K) (hx : ∀ l, μ (x l) ≤ 1) (hv : ∀ l, μ (v l) ≤ 1)
    (hBv : MvPolynomial.eval v B ≠ 0)
    (hclose : CB * (⨆ l, μ (x l - v l)) < μ (MvPolynomial.eval v B)) :
    μ (MvPolynomial.eval x B) = μ (MvPolynomial.eval v B) ∧
      μ (MvPolynomial.eval x A / MvPolynomial.eval x B - MvPolynomial.eval v A / MvPolynomial.eval v B)
        ≤ max (CA * μ (MvPolynomial.eval v B)) (CB * μ (MvPolynomial.eval v A)) / μ (MvPolynomial.eval v B) ^ 2
          * ⨆ l, μ (x l - v l)
```

### `MvPolynomial.abv_eval_sub_eval_le_mul_iSup`

`Thm_MvPolynomial_abv_eval_sub_eval_le_mul_iSup` — Non-archimedean Lipschitz bound for polynomials on the unit polydisc

```lean
theorem MvPolynomial.abv_eval_sub_eval_le_mul_iSup
    {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ)
    {r : ℕ} (G : MvPolynomial (Fin r) K) (C : ℝ) (hC : ∀ m, μ (G.coeff m) ≤ C)
    (x v : Fin r → K) (hx : ∀ l, μ (x l) ≤ 1) (hv : ∀ l, μ (v l) ≤ 1) :
    μ (MvPolynomial.eval x G - MvPolynomial.eval v G) ≤ C * ⨆ l, μ (x l - v l)
```

### `MvPolynomial.ae_restrict_torusBox_eval_circleMap_ne_zero`

`Thm_MvPolynomial_ae_restrict_torusBox_eval_circleMap_ne_zero` — Non-zero polynomials vanish almost nowhere on the torus

```lean
theorem MvPolynomial.ae_restrict_torusBox_eval_circleMap_ne_zero {n : ℕ} {P : MvPolynomial (Fin n) ℂ} (hP : P ≠ 0) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict (MvPolynomial.torusBox n)),
      MvPolynomial.eval (fun i ↦ circleMap 0 1 (θ i)) P ≠ 0
```

### `MvPolynomial.bijective_algHom_truncated_of_forall_exists_sub_mem_sq`

`Thm_MvPolynomial_bijective_algHom_truncated_of_forall_exists_sub_mem_sq` — Endomorphism of a truncated polynomial ring onto mod t² is bijective

```lean
theorem MvPolynomial.bijective_algHom_truncated_of_forall_exists_sub_mem_sq
    (k : Type*) [Field k] (N M : ℕ)
    (θ : (MvPolynomial (Fin N) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin N) k →+* k)) ^ (M + 1)) →ₐ[k]
      (MvPolynomial (Fin N) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin N) k →+* k)) ^ (M + 1)))
    (hθ : ∀ j : Fin N, ∃ t, θ t - Ideal.Quotient.mk _ (MvPolynomial.X j) ∈
      (Ideal.map (Ideal.Quotient.mk ((RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin N) k →+* k)) ^ (M + 1)))
        (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin N) k →+* k))) ^ 2) :
    Function.Bijective θ
```

### `MvPolynomial.eq_of_forall_eval_rpow_eq`

`Thm_MvPolynomial_eq_of_forall_eval_rpow_eq` — Polynomial identity on S × {N^u} holds identically

```lean
theorem MvPolynomial.eq_of_forall_eval_rpow_eq (N : ℕ) (hN : 1 < N) (u₀ : ℝ) (S : Set ℂ)
    (hS : S.Infinite) (P Q : MvPolynomial (Fin 2) ℂ)
    (h : ∀ x ∈ S, ∀ u : ℝ, u₀ < u →
      MvPolynomial.eval ![x, (((N : ℝ) ^ u : ℝ) : ℂ)] P =
        MvPolynomial.eval ![x, (((N : ℝ) ^ u : ℝ) : ℂ)] Q) :
    P = Q
```

### `MvPolynomial.eq_of_forall_rpow_infinite_setOf_eval_eq`

`Thm_MvPolynomial_eq_of_forall_rpow_infinite_setOf_eval_eq` — Two-variable polynomial identity along real powers of N

```lean
theorem MvPolynomial.eq_of_forall_rpow_infinite_setOf_eval_eq (N : ℕ) (hN : 1 < N) (u₀ : ℝ)
    (P Q : MvPolynomial (Fin 2) ℂ)
    (h : ∀ u : ℝ, u₀ < u →
      Set.Infinite {x : ℂ | MvPolynomial.eval ![x, (((N : ℝ) ^ u : ℝ) : ℂ)] P =
        MvPolynomial.eval ![x, (((N : ℝ) ^ u : ℝ) : ℂ)] Q}) :
    P = Q
```

### `MvPolynomial.exists_algEquiv_localization_atPrime_mvPowerSeries_quotient_apply_mk`

`Thm_MvPolynomial_exists_algEquiv_localization_atPrime_mvPowerSeries_quotient_apply_mk` — Localization at a rational point as a power series quotient

```lean
theorem MvPolynomial.exists_algEquiv_localization_atPrime_mvPowerSeries_quotient_apply_mk
    (K : Type*) [Field K] {m r : ℕ} (g : Fin r → MvPolynomial (Fin m) K)
    (𝔫 : Ideal (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g))) [𝔫.IsMaximal]
    (h𝔫 : ∀ j, Ideal.Quotient.mk (Ideal.span (Set.range g)) (MvPolynomial.X j) ∈ 𝔫)
    [Module.Finite K (Localization.AtPrime 𝔫)] :
    ∃ e : Localization.AtPrime 𝔫 ≃ₐ[K]
      (MvPowerSeries (Fin m) K ⧸ Ideal.span (Set.range fun i => (g i : MvPowerSeries (Fin m) K))),
      ∀ p : MvPolynomial (Fin m) K,
        e (algebraMap (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g)) (Localization.AtPrime 𝔫)
            (Ideal.Quotient.mk (Ideal.span (Set.range g)) p)) =
          Ideal.Quotient.mk (Ideal.span (Set.range fun i => (g i : MvPowerSeries (Fin m) K)))
            (p : MvPowerSeries (Fin m) K)
```

### `MvPolynomial.exists_coeff_aeval_optionElim_eq_zero_of_isUnit_eval_pderiv`

`Thm_MvPolynomial_exists_coeff_aeval_optionElim_eq_zero_of_isUnit_eval_pderiv` — Truncated implicit functions for a triangular pair of relations

```lean
theorem MvPolynomial.exists_coeff_aeval_optionElim_eq_zero_of_isUnit_eval_pderiv
    {A : Type*} [CommRing A] (m : ℕ) (u : A) (w0 : Fin 2 → A) (G : Fin 2 → MvPolynomial (Option (Fin 2)) A)
    (hvars : (some 1 : Option (Fin 2)) ∉ (G 0).vars)
    (hroot : ∀ j, MvPolynomial.eval (fun o => Option.elim o u w0) (G j) = 0)
    (hder : ∀ j, IsUnit (MvPolynomial.eval (fun o => Option.elim o u w0) (MvPolynomial.pderiv (some j) (G j)))) :
    ∃ w : Fin 2 → Fin (m + 1) → A, (∀ j, w j 0 = w0 j) ∧
      ∀ (j : Fin 2) (r : Fin (m + 1)),
        (MvPolynomial.aeval (fun o : Option (Fin 2) => Option.elim o (Polynomial.C u + Polynomial.X)
            (fun j => ∑ r' : Fin (m + 1), Polynomial.monomial (r' : ℕ) (w j r'))) (G j)).coeff r = 0
```

### `MvPolynomial.exists_eq_C_mul_X_add_X_pow_of_totalDegree_le_of_forall_eval_eq_pow_mul_eval`

`Thm_MvPolynomial_exists_eq_C_mul_X_add_X_pow_of_totalDegree_le_of_forall_eval_eq_pow_mul_eval` — Scaling rigidity forcing P = c (X₀+X₁)^g

```lean
theorem MvPolynomial.exists_eq_C_mul_X_add_X_pow_of_totalDegree_le_of_forall_eval_eq_pow_mul_eval
    (g n : ℕ) (hn : 2 ≤ n) (α β : ℕ) (hαβ : α + β = n ^ 2) (hα : α = β + n)
    (P : MvPolynomial (Fin 2) ℚ) (hP : P.totalDegree ≤ g)
    (h : ∀ a b : ℕ,
      MvPolynomial.eval ![((α * a + β * b : ℕ) : ℚ), ((β * a + α * b : ℕ) : ℚ)] P =
        (n : ℚ) ^ (2 * g) * MvPolynomial.eval ![(a : ℚ), (b : ℚ)] P) :
    ∃ c : ℚ, P = MvPolynomial.C c * (MvPolynomial.X 0 + MvPolynomial.X 1) ^ g
```

### `MvPolynomial.exists_faithfullyFlat_algHom_lift_family_of_forall_isArtinianRing_exists_algHom_lift`

`Thm_MvPolynomial_exists_faithfullyFlat_algHom_lift_family_of_forall_isArtinianRing_exists_algHom_lift` — Faithfully flat lift family from Artinian lifting property

```lean
theorem MvPolynomial.exists_faithfullyFlat_algHom_lift_family_of_forall_isArtinianRing_exists_algHom_lift
    (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] {n : ℕ}
    (I J : Ideal (MvPolynomial (Fin n) R)) (hIJ : I ≤ J) (hJ : J.IsMaximal)
    (hlift : ∀ (T' T : Type) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [IsAlgClosed (ResidueField T')]
      (ℓ : ℕ) [Fact ℓ.Prime] [CharP (ResidueField T') ℓ]
      [CommRing T] [Nontrivial T] [Algebra R T'] [Algebra R T]
      (p : T' →ₐ[R] T), Function.Surjective p → RingHom.ker p.toRingHom * maximalIdeal T' = ⊥ →
      ∀ m : (MvPolynomial (Fin n) R ⧸ I) →ₐ[R] T,
        ∃ m' : (MvPolynomial (Fin n) R ⧸ I) →ₐ[R] T', p.comp m' = m) :
    ∃ (D : ℕ → Type) (_ : ∀ N, CommRing (D N)) (_ : ∀ N, Algebra R (D N))
      (_ : ∀ N, Algebra (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N))
      (_ : ∀ N, IsScalarTower R (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N))
      (_ : ∀ N, Module.FaithfullyFlat (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N))
      (σ : ∀ N, (MvPolynomial (Fin n) R ⧸ I) →ₐ[R] D N),
      ∀ (N : ℕ) (f : MvPolynomial (Fin n) R),
        σ N (Ideal.Quotient.mk I f) -
            algebraMap (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N) (Ideal.Quotient.mk (J ^ N ⊔ J * I) f) ∈
          Ideal.map (algebraMap (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N))
            (Ideal.map (Ideal.Quotient.mk (J ^ N ⊔ J * I)) (J ^ N ⊔ I))
```

### `MvPolynomial.exists_faithfullyFlat_algHom_lift_family_of_forall_isArtinianRing_exists_algHom_lift_of_isNoetherianRing`

`Thm_MvPolynomial_exists_faithfullyFlat_algHom_lift_family_of_forall_isArtinianRing_exists_algHom_lift_of_isNoetherianRing` — Faithfully flat Artin-local lift families over a Noetherian base

```lean
theorem MvPolynomial.exists_faithfullyFlat_algHom_lift_family_of_forall_isArtinianRing_exists_algHom_lift_of_isNoetherianRing
    (R : Type) [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (I J : Ideal (MvPolynomial (Fin n) R)) (hIJ : I ≤ J) (hJ : J.IsMaximal)
    (hlift : ∀ (T' T : Type) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [IsAlgClosed (ResidueField T')]
      [CommRing T] [Nontrivial T] [Algebra R T'] [Algebra R T]
      (p : T' →ₐ[R] T), Function.Surjective p → RingHom.ker p.toRingHom * maximalIdeal T' = ⊥ →
      ∀ m : (MvPolynomial (Fin n) R ⧸ I) →ₐ[R] T,
        ∃ m' : (MvPolynomial (Fin n) R ⧸ I) →ₐ[R] T', p.comp m' = m) :
    ∃ (D : ℕ → Type) (_ : ∀ N, CommRing (D N)) (_ : ∀ N, Algebra R (D N))
      (_ : ∀ N, Algebra (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N))
      (_ : ∀ N, IsScalarTower R (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N))
      (_ : ∀ N, Module.FaithfullyFlat (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N))
      (σ : ∀ N, (MvPolynomial (Fin n) R ⧸ I) →ₐ[R] D N),
      ∀ (N : ℕ) (f : MvPolynomial (Fin n) R),
        σ N (Ideal.Quotient.mk I f) -
            algebraMap (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N) (Ideal.Quotient.mk (J ^ N ⊔ J * I) f) ∈
          Ideal.map (algebraMap (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N))
            (Ideal.map (Ideal.Quotient.mk (J ^ N ⊔ J * I)) (J ^ N ⊔ I))
```

### `MvPolynomial.exists_finset_sum_mul_eq_of_isHomogeneous_of_mem_span`

`Thm_MvPolynomial_exists_finset_sum_mul_eq_of_isHomogeneous_of_mem_span` — Homogeneous elements of an ideal generated by forms

```lean
theorem MvPolynomial.exists_finset_sum_mul_eq_of_isHomogeneous_of_mem_span
    {σ A : Type} [CommRing A] (J₀ : Set (MvPolynomial σ A))
    (hJ₀ : ∀ G ∈ J₀, ∃ e : ℕ, G.IsHomogeneous e)
    {d : ℕ} {F : MvPolynomial σ A} (hF : F.IsHomogeneous d) (hFJ : F ∈ Ideal.span J₀) :
    ∃ (s : Finset (MvPolynomial σ A)) (e : MvPolynomial σ A → ℕ) (c : MvPolynomial σ A → MvPolynomial σ A),
      ↑s ⊆ J₀ ∧
      (∀ G ∈ s, e G ≤ d ∧ G.IsHomogeneous (e G) ∧ (c G).IsHomogeneous (d - e G)) ∧
      F = ∑ G ∈ s, c G * G
```

### `MvPolynomial.exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le`

`Thm_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le` — Green's hyperplane restriction theorem for a general linear form

```lean
theorem MvPolynomial.exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le
    (n d : ℕ) (hd : 1 ≤ d) (K : Type) [Field K] [Infinite K]
    (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (hJ : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J) :
    ∃ G : MvPolynomial (Fin (n + 1)) K, G ≠ 0 ∧ ∀ a : Fin (n + 1) → K, MvPolynomial.eval a G ≠ 0 →
      Nat.macaulayPow d (Module.finrank K (piece (J ⊔ Ideal.span {∑ i, C (a i) * X i}) d)) +
          Module.finrank K (piece J d) ≤
        Nat.macaulayPow d (Module.finrank K (piece J d))
```

### `MvPolynomial.exists_forall_eval_ne_zero_mem_of_mul_mem_and_finrank_piece_sup_eq_macaulayPow`

`Thm_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_and_finrank_piece_sup_eq_macaulayPow` — Maximal growth persists under a general hyperplane section

```lean
theorem MvPolynomial.exists_forall_eval_ne_zero_mem_of_mul_mem_and_finrank_piece_sup_eq_macaulayPow
    (n m : ℕ) (K : Type) [Field K] [Infinite K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
    (hmax : Module.finrank K (piece J (m + 1)) = Nat.macaulayPow m (Module.finrank K (piece J m))) :
    ∃ G : MvPolynomial (Fin (n + 1)) K, G ≠ 0 ∧ ∀ a : Fin (n + 1) → K, MvPolynomial.eval a G ≠ 0 →
      (∀ f : MvPolynomial (Fin (n + 1)) K, f.IsHomogeneous m → (∑ i, C (a i) * X i) * f ∈ J → f ∈ J) ∧
      Module.finrank K (piece (J ⊔ Ideal.span {∑ i, C (a i) * X i}) (m + 1)) =
        Nat.macaulayPow m (Module.finrank K (piece (J ⊔ Ideal.span {∑ i, C (a i) * X i}) m)) ∧
      Nat.macaulayPow m (Module.finrank K (piece (J ⊔ Ideal.span {∑ i, C (a i) * X i}) m)) +
          Module.finrank K (piece J m) = Nat.macaulayPow m (Module.finrank K (piece J m))
```

### `MvPolynomial.exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow`

`Thm_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow` — Gotzmann maximal growth: general linear form regular in degrees ≥ m

```lean
theorem MvPolynomial.exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow
    (n m : ℕ) (K : Type) [Field K] [Infinite K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
    (hmax : Module.finrank K (piece J (m + 1)) = Nat.macaulayPow m (Module.finrank K (piece J m))) :
    ∃ G : MvPolynomial (Fin (n + 1)) K, G ≠ 0 ∧ ∀ a : Fin (n + 1) → K, MvPolynomial.eval a G ≠ 0 →
      ∀ k : ℕ, m ≤ k → ∀ f : MvPolynomial (Fin (n + 1)) K, f.IsHomogeneous k →
        (∑ i, C (a i) * X i) * f ∈ J → f ∈ J
```

### `MvPolynomial.exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval`

`Thm_MvPolynomial_exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval` — Existence of a Gotzmann bound for a Hilbert polynomial

```lean
theorem MvPolynomial.exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval
    (n : ℕ) (P : Polynomial ℚ)
    (hP : ∃ (K : Type) (_ : Field K) (I : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) ∧
      ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d → (Module.finrank K (piece I d) : ℚ) = P.eval (d : ℚ)) :
    ∃ D₀ : ℕ, ∀ e : ℕ, D₀ ≤ e →
      (∀ (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
        (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) →
        (Module.finrank K (piece J e) : ℚ) = P.eval (e : ℚ) →
        (Module.finrank K (piece J (e + 1)) : ℚ) ≤ P.eval ((e : ℚ) + 1)) ∧
      ∃ (K : Type) (_ : Field K) (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
        (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) ∧
        (Module.finrank K (piece J e) : ℚ) = P.eval (e : ℚ) ∧
        (Module.finrank K (piece J (e + 1)) : ℚ) = P.eval ((e : ℚ) + 1)
```

### `MvPolynomial.exists_forall_sum_C_mul_X_mul_mem_imp_of_forall_exists_X_pow_mul_mem`

`Thm_MvPolynomial_exists_forall_sum_C_mul_X_mul_mem_imp_of_forall_exists_X_pow_mul_mem` — A linear form that is a non-zero-divisor modulo a saturated homogeneous ideal

```lean
theorem MvPolynomial.exists_forall_sum_C_mul_X_mul_mem_imp_of_forall_exists_X_pow_mul_mem
    (n : ℕ) (K : Type) [Field K] [Infinite K] (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hI : ∀ p ∈ I, ∀ i : ℕ, homogeneousComponent i p ∈ I)
    (hsat : ∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) K), F.IsHomogeneous d →
      (∀ i : Fin (n + 1), ∃ N : ℕ, MvPolynomial.X i ^ N * F ∈ I) → F ∈ I) :
    ∃ a : Fin (n + 1) → K, ∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) K), F.IsHomogeneous d →
      (∑ i : Fin (n + 1), MvPolynomial.C (a i) * MvPolynomial.X i) * F ∈ I → F ∈ I
```

### `MvPolynomial.exists_isHomogeneous_eq_sub_sub_of_cocycle_of_symmetric`

`Thm_MvPolynomial_exists_isHomogeneous_eq_sub_sub_of_cocycle_of_symmetric` — Symmetric homogeneous 2-cocycles are coboundaries (Lazard)

```lean
theorem MvPolynomial.exists_isHomogeneous_eq_sub_sub_of_cocycle_of_symmetric
    {R : Type u} [CommRing R] {σ : Type v} [Finite σ] (n : ℕ) (hn : IsUnit (n : R))
    (Γ : MvPolynomial (σ ⊕ σ) R) (hhom : Γ.IsHomogeneous n)
    (hsymm : MvPolynomial.rename Sum.swap Γ = Γ)
    (hcoc :
      MvPolynomial.aeval (Sum.elim (fun s => (MvPolynomial.X (Sum.inr (Sum.inl s)) : MvPolynomial (σ ⊕ (σ ⊕ σ)) R))
          (fun s => MvPolynomial.X (Sum.inr (Sum.inr s)))) Γ
        - MvPolynomial.aeval (Sum.elim (fun s => (MvPolynomial.X (Sum.inl s) + MvPolynomial.X (Sum.inr (Sum.inl s)) :
            MvPolynomial (σ ⊕ (σ ⊕ σ)) R)) (fun s => MvPolynomial.X (Sum.inr (Sum.inr s)))) Γ
        + MvPolynomial.aeval (Sum.elim (fun s => (MvPolynomial.X (Sum.inl s) : MvPolynomial (σ ⊕ (σ ⊕ σ)) R))
            (fun s => MvPolynomial.X (Sum.inr (Sum.inl s)) + MvPolynomial.X (Sum.inr (Sum.inr s)))) Γ
        - MvPolynomial.aeval (Sum.elim (fun s => (MvPolynomial.X (Sum.inl s) : MvPolynomial (σ ⊕ (σ ⊕ σ)) R))
            (fun s => MvPolynomial.X (Sum.inr (Sum.inl s)))) Γ = 0) :
    ∃ h : MvPolynomial σ R, h.IsHomogeneous n ∧
      Γ = MvPolynomial.aeval (fun s => (MvPolynomial.X (Sum.inl s) + MvPolynomial.X (Sum.inr s) : MvPolynomial (σ ⊕ σ) R)) h
        - MvPolynomial.rename Sum.inl h - MvPolynomial.rename Sum.inr h
```

### `MvPolynomial.exists_isStandardSmooth_algHom_isUnit_det_pderiv_basis_kaehlerDifferential`

`Thm_MvPolynomial_exists_isStandardSmooth_algHom_isUnit_det_pderiv_basis_kaehlerDifferential` — Standard smooth quotient inverting a Jacobian minor

```lean
theorem MvPolynomial.exists_isStandardSmooth_algHom_isUnit_det_pderiv_basis_kaehlerDifferential
    {R : Type u} [CommRing R] {ι : Type} [Finite ι] {m : ℕ} (h : Fin m → MvPolynomial (ι ⊕ Fin m) R) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C) (φ : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] C),
      Algebra.IsStandardSmooth R C ∧
      (∀ a, φ (h a) = 0) ∧
      IsUnit (φ (Matrix.det (Matrix.of fun a b : Fin m => MvPolynomial.pderiv (Sum.inr b) (h a)))) ∧
      (∀ (B : Type u) [CommRing B] [Algebra R B] (ψ : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] B),
          (∀ a, ψ (h a) = 0) →
          IsUnit (ψ (Matrix.det (Matrix.of fun a b : Fin m => MvPolynomial.pderiv (Sum.inr b) (h a)))) →
          ∃ χ : C →ₐ[R] B, χ.comp φ = ψ) ∧
      ∃ b : Module.Basis ι C Ω[C⁄R], ∀ i, b i = D R C (φ (MvPolynomial.X (Sum.inl i)))
```

### `MvPolynomial.exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure`

`Thm_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure` — Bertini–Noether: absolute irreducibility spreads out

```lean
theorem MvPolynomial.exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure
    {R : Type u} [CommRing R] [IsDomain R] {σ : Type v} [Finite σ] (F : MvPolynomial σ R)
    (hF : Irreducible (MvPolynomial.map (algebraMap R (AlgebraicClosure (FractionRing R))) F)) :
    ∃ c : R, c ≠ 0 ∧ ∀ (E : Type w) [Field E] (φ : R →+* E), φ c ≠ 0 →
      Irreducible (MvPolynomial.map φ F)
```

### `MvPolynomial.exists_pair_clearDenominator_deformation`

`Thm_MvPolynomial_exists_pair_clearDenominator_deformation` — Uniform clearing of denominators in a deformation parameter

```lean
theorem MvPolynomial.exists_pair_clearDenominator_deformation
    (r b₁ b₂ ω c : ℂ) (hr : r ≠ 0) (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) (hω : ω ≠ 0)
    (P : MvPolynomial (Fin 3) ℂ) (D₁ D₂ : Polynomial ℂ) (e : ℕ)
    (hD₁ : D₁.eval 0 ≠ 0) (hD₂ : D₂.eval 0 ≠ 0) :
    ∃ p q : MvPolynomial (Fin 2) ℂ,
      (∀ y : ℂ, y ≠ 0 → ∃ x : ℂ, MvPolynomial.eval ![x, y] q ≠ 0) ∧
      ∀ (x y Z : ℂ), y ≠ 0 →
        Z * (D₁.eval (b₁ * y⁻¹ * (r * x)) * D₁.eval (b₂ * y * (r * x)) * D₂.eval (ω * (r * x) ^ 2) *
            (ω * (r * x) ^ 2) ^ e) =
          c * MvPolynomial.eval ![r * x, b₁ * y⁻¹, b₂ * y] P →
        Z * MvPolynomial.eval ![x, y] q = MvPolynomial.eval ![x, y] p
```

### `MvPolynomial.exists_polynomial_forall_tsum_row_mul_eval_eq_and_tsum_mul_eval_eq_of_tsum_mul_eval_eq`

`Thm_MvPolynomial_exists_polynomial_forall_tsum_row_mul_eval_eq_and_tsum_mul_eval_eq_of_tsum_mul_eval_eq` — Row-wise continuation of a two-variable series with separated denominators

```lean
theorem MvPolynomial.exists_polynomial_forall_tsum_row_mul_eval_eq_and_tsum_mul_eval_eq_of_tsum_mul_eval_eq
    (A : ℕ × ℕ → ℂ) (D₁ D₂ : Polynomial ℂ) (P : MvPolynomial (Fin 2) ℂ) (r : ℝ)
    (hD₂ : D₂.eval 0 ≠ 0) (hr : 0 < r)
    (h : ∀ X Y : ℂ, ‖X‖ < r → ‖Y‖ < r →
      Summable (fun m : ℕ × ℕ => ‖A m * X ^ m.1 * Y ^ m.2‖) ∧
      (∑' m : ℕ × ℕ, A m * X ^ m.1 * Y ^ m.2) * (D₁.eval X * D₂.eval Y) = MvPolynomial.eval ![X, Y] P) :
    ∃ (q : ℕ → Polynomial ℂ) (r₂ : ℝ), 0 < r₂ ∧
      (∀ (j : ℕ) (X : ℂ), ‖X‖ < r →
        Summable (fun m₁ : ℕ => ‖A (m₁, j) * X ^ m₁‖) ∧
        (∑' m₁ : ℕ, A (m₁, j) * X ^ m₁) * D₁.eval X = (q j).eval X) ∧
      (∀ X Y : ℂ, ‖Y‖ < r₂ →
        Summable (fun j : ℕ => ‖(q j).eval X * Y ^ j‖) ∧
        (∑' j : ℕ, (q j).eval X * Y ^ j) * D₂.eval Y = MvPolynomial.eval ![X, Y] P)
```

### `MvPolynomial.exists_quotient_span_quotient_span_singleton_algEquiv_of_isIdempotentElem`

`Thm_MvPolynomial_exists_quotient_span_quotient_span_singleton_algEquiv_of_isIdempotentElem` — Killing an idempotent costs one variable and one relation

```lean
theorem MvPolynomial.exists_quotient_span_quotient_span_singleton_algEquiv_of_isIdempotentElem
    (R : Type u) [CommRing R] (N : ℕ) (f : Fin N → MvPolynomial (Fin N) R)
    (e : MvPolynomial (Fin N) R ⧸ Ideal.span (Set.range f)) (he : IsIdempotentElem e) :
    ∃ f' : Fin (N + 1) → MvPolynomial (Fin (N + 1)) R,
      Nonempty ((MvPolynomial (Fin (N + 1)) R ⧸ Ideal.span (Set.range f')) ≃ₐ[R]
        ((MvPolynomial (Fin N) R ⧸ Ideal.span (Set.range f)) ⧸ Ideal.span {e}))
```

### `MvPolynomial.exists_skew_eq_sum_mul_X_of_sum_mul_X_eq_zero`

`Thm_MvPolynomial_exists_skew_eq_sum_mul_X_of_sum_mul_X_eq_zero` — Linear syzygies among the variables are skew-symmetric

```lean
theorem MvPolynomial.exists_skew_eq_sum_mul_X_of_sum_mul_X_eq_zero
    (B : Type*) [CommRing B] {m : ℕ} (c : Fin m → MvPolynomial (Fin m) B)
    (hc : ∑ j, c j * MvPolynomial.X j = 0) :
    ∃ e : Fin m → Fin m → MvPolynomial (Fin m) B,
      (∀ j k, e j k = -e k j) ∧ (∀ j, e j j = 0) ∧ ∀ j, c j = ∑ k, e j k * MvPolynomial.X k
```

### `MvPolynomial.exists_span_monomial_finrank_piece_eq_and_finrank_piece_succ_eq_macaulayPow`

`Thm_MvPolynomial_exists_span_monomial_finrank_piece_eq_and_finrank_piece_succ_eq_macaulayPow` — Macaulay's bound is attained by a homogeneous ideal

```lean
theorem MvPolynomial.exists_span_monomial_finrank_piece_eq_and_finrank_piece_succ_eq_macaulayPow
    (n d : ℕ) (hd : 1 ≤ d) (a : ℕ) (ha : a ≤ (n + d).choose n) (K : Type) [Field K] :
    ∃ J : Ideal (MvPolynomial (Fin (n + 1)) K),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous d) ∧ J = Ideal.span s) ∧
      Module.finrank K (piece J d) = a ∧ Module.finrank K (piece J (d + 1)) = Nat.macaulayPow d a
```

### `MvPolynomial.exists_subst_X_add_sum_mul_X_pow_sub_X_coeff_mem_span_of_isNilpotent`

`Thm_MvPolynomial_exists_subst_X_add_sum_mul_X_pow_sub_X_coeff_mem_span_of_isNilpotent` — Polynomial inverse mod p of X + C X⁽ᵖ⁾

```lean
theorem MvPolynomial.exists_subst_X_add_sum_mul_X_pow_sub_X_coeff_mem_span_of_isNilpotent
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    {d : ℕ} (C : Matrix (Fin d) (Fin d) 𝓞) (hC : IsNilpotent (C.map (algebraMap 𝓞 (ZMod p)))) :
    ∃ χ : Fin d → MvPolynomial (Fin d) 𝓞, (∀ i, MvPolynomial.constantCoeff (χ i) = 0) ∧
      (∀ (i : Fin d) (m : Fin d →₀ ℕ),
        (subst (fun j => (χ j : MvPowerSeries (Fin d) 𝓞))
            ((MvPowerSeries.X i : MvPowerSeries (Fin d) 𝓞) +
              ∑ j, MvPowerSeries.C (C i j) * (MvPowerSeries.X j : MvPowerSeries (Fin d) 𝓞) ^ p)).coeff m -
          (MvPowerSeries.X i : MvPowerSeries (Fin d) 𝓞).coeff m ∈ Ideal.span {(p : 𝓞)}) ∧
      (∀ (i : Fin d) (m : Fin d →₀ ℕ),
        (MvPolynomial.aeval (fun j => (MvPolynomial.X j : MvPolynomial (Fin d) 𝓞) +
            ∑ l, MvPolynomial.C (C j l) * MvPolynomial.X l ^ p) (χ i)).coeff m -
          (MvPolynomial.X i : MvPolynomial (Fin d) 𝓞).coeff m ∈ Ideal.span {(p : 𝓞)})
```

### `MvPolynomial.exists_tensor_kaehlerDifferential_linearEquiv_pi_of_isLocalization`

`Thm_MvPolynomial_exists_tensor_kaehlerDifferential_linearEquiv_pi_of_isLocalization` — Differentials of a localised polynomial ring after base change

```lean
theorem MvPolynomial.exists_tensor_kaehlerDifferential_linearEquiv_pi_of_isLocalization
    (R : Type) [CommRing R] {n : ℕ} (M : Submonoid (MvPolynomial (Fin n) R))
    (P : Type) [CommRing P] [Algebra (MvPolynomial (Fin n) R) P] [IsLocalization M P]
    [Algebra R P] [IsScalarTower R (MvPolynomial (Fin n) R) P]
    (K : Type) [CommRing K] [Algebra P K] [Algebra (MvPolynomial (Fin n) R) K]
    [IsScalarTower (MvPolynomial (Fin n) R) P K] :
    ∃ e : K ⊗[P] Ω[P⁄R] ≃ₗ[K] (Fin n → K),
      ∀ a : MvPolynomial (Fin n) R,
        e ((1 : K) ⊗ₜ[P] KaehlerDifferential.D R P (algebraMap (MvPolynomial (Fin n) R) P a)) =
          fun i => algebraMap (MvPolynomial (Fin n) R) K (MvPolynomial.pderiv i a)
```

### `MvPolynomial.exists_tmul_one_sub_one_tmul_eq_sum_mul`

`Thm_MvPolynomial_exists_tmul_one_sub_one_tmul_eq_sum_mul` — g⊗1-1⊗ g lies in the diagonal ideal

```lean
theorem MvPolynomial.exists_tmul_one_sub_one_tmul_eq_sum_mul
    (R : Type*) [CommRing R] {m : ℕ} (g : MvPolynomial (Fin m) R) :
    ∃ a : Fin m → MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R,
      g ⊗ₜ[R] (1 : MvPolynomial (Fin m) R) - (1 : MvPolynomial (Fin m) R) ⊗ₜ[R] g =
        ∑ j, a j * (MvPolynomial.X j ⊗ₜ[R] 1 - 1 ⊗ₜ[R] MvPolynomial.X j)
```

### `MvPolynomial.finite_and_finrank_quotient_span_aeval_X_eq_pow_of_monic`

`Thm_MvPolynomial_finite_and_finrank_quotient_span_aeval_X_eq_pow_of_monic` — Dimension of k[Xᵢ]/(f(Xᵢ)) for monic f

```lean
theorem MvPolynomial.finite_and_finrank_quotient_span_aeval_X_eq_pow_of_monic
    (k : Type u) [Field k] (ι : Type v) [Finite ι] (f : Polynomial k) (hf : f.Monic) :
    Module.Finite k (MvPolynomial ι k ⧸
        Ideal.span (Set.range fun i : ι => Polynomial.aeval (MvPolynomial.X i : MvPolynomial ι k) f)) ∧
      Module.finrank k (MvPolynomial ι k ⧸
        Ideal.span (Set.range fun i : ι => Polynomial.aeval (MvPolynomial.X i : MvPolynomial ι k) f)) =
        f.natDegree ^ Nat.card ι
```

### `MvPolynomial.finite_and_flat_and_finrank_expand_eq_pow`

`Thm_MvPolynomial_finite_and_flat_and_finrank_expand_eq_pow` — expandₚ makes R[X_σ] finite flat of rank p^{|σ|}

```lean
theorem MvPolynomial.finite_and_flat_and_finrank_expand_eq_pow
    (R : Type u) [CommRing R] (σ : Type v) [Finite σ] (p : ℕ) (hp : 0 < p) :
    (MvPolynomial.expand p (σ := σ) (R := R)).toRingHom.Finite ∧
    (MvPolynomial.expand p (σ := σ) (R := R)).toRingHom.Flat ∧
    ∀ q : PrimeSpectrum (MvPolynomial σ R),
      (MvPolynomial.expand p (σ := σ) (R := R)).toRingHom.finrank q = p ^ Nat.card σ
```

### `MvPolynomial.finite_and_natCard_quotient_truncatedDieudonneRelations_le_pow`

`Thm_MvPolynomial_finite_and_natCard_quotient_truncatedDieudonneRelations_le_pow` — Finiteness of a truncated Dieudonné ring, with bound pⁿᵇ

```lean
theorem MvPolynomial.finite_and_natCard_quotient_truncatedDieudonneRelations_le_pow
    (p : ℕ) (hp : 0 < p) (n a b : ℕ) (hab : a < b) :
    Finite (MvPolynomial Bool ℤ ⧸ Ideal.span
        ({MvPolynomial.X true * MvPolynomial.X false - MvPolynomial.C (p : ℤ),
          MvPolynomial.X false ^ n, MvPolynomial.X true ^ b - MvPolynomial.X true ^ a} :
          Set (MvPolynomial Bool ℤ))) ∧
      Nat.card (MvPolynomial Bool ℤ ⧸ Ideal.span
        ({MvPolynomial.X true * MvPolynomial.X false - MvPolynomial.C (p : ℤ),
          MvPolynomial.X false ^ n, MvPolynomial.X true ^ b - MvPolynomial.X true ^ a} :
          Set (MvPolynomial Bool ℤ))) ≤ p ^ (n * b)
```

### `MvPolynomial.finrank_piece_add_two_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow`

`Thm_MvPolynomial_finrank_piece_add_two_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow` — One step of Gotzmann's persistence theorem

```lean
theorem MvPolynomial.finrank_piece_add_two_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow
    (n m : ℕ) (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
    (hmax : Module.finrank K (piece J (m + 1)) = Nat.macaulayPow m (Module.finrank K (piece J m))) :
    Module.finrank K (piece J (m + 2)) = Nat.macaulayPow (m + 1) (Module.finrank K (piece J (m + 1)))
```

### `MvPolynomial.finrank_piece_eq_of_maximal_growth`

`Thm_MvPolynomial_finrank_piece_eq_of_maximal_growth` — Gotzmann persistence for ideals of maximal Hilbert growth

```lean
theorem MvPolynomial.finrank_piece_eq_of_maximal_growth
    (n m : ℕ) (h : ℕ → ℕ)
    (h₂ : ∀ e, m ≤ e → ∀ (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) →
      Module.finrank K (piece J e) = h e → Module.finrank K (piece J (e + 1)) ≤ h (e + 1))
    (h₃ : ∀ e, m ≤ e → ∃ (K : Type) (_ : Field K) (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) ∧
      Module.finrank K (piece J e) = h e ∧ Module.finrank K (piece J (e + 1)) = h (e + 1))
    (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
    (hm : Module.finrank K (piece J m) = h m) (hm₁ : Module.finrank K (piece J (m + 1)) = h (m + 1)) :
    ∀ e, m ≤ e → Module.finrank K (piece J e) = h e
```

### `MvPolynomial.finrank_piece_span_sup_linearForm_eq_macaulayPow_and_lt`

`Thm_MvPolynomial_finrank_piece_span_sup_linearForm_eq_macaulayPow_and_lt` — Maximal growth passes to the degree-m part of J+(ℓ)

```lean
theorem MvPolynomial.finrank_piece_span_sup_linearForm_eq_macaulayPow_and_lt
    (n m : ℕ) (hm : 1 ≤ m) (k : Type) [Field k]
    (J : Ideal (MvPolynomial (Fin (n + 1)) k))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) k), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
    (a : Fin (n + 1) → k)
    (hgrowth : Module.finrank k (piece (J ⊔ Ideal.span {(∑ j : Fin (n + 1), MvPolynomial.C (a j) * MvPolynomial.X j)}) (m + 1)) =
      Nat.macaulayPow m (Module.finrank k (piece (J ⊔ Ideal.span {(∑ j : Fin (n + 1), MvPolynomial.C (a j) * MvPolynomial.X j)}) m)))
    (hsum : Nat.macaulayPow m (Module.finrank k (piece (J ⊔ Ideal.span {(∑ j : Fin (n + 1), MvPolynomial.C (a j) * MvPolynomial.X j)}) m)) +
        Module.finrank k (piece J m) = Nat.macaulayPow m (Module.finrank k (piece J m))) :
    let J' : Ideal (MvPolynomial (Fin (n + 1)) k) :=
      Ideal.span {f | f ∈ J ⊔ Ideal.span {(∑ j : Fin (n + 1), MvPolynomial.C (a j) * MvPolynomial.X j)} ∧ f.IsHomogeneous m}
    Module.finrank k (piece J' (m + 1)) = Nat.macaulayPow m (Module.finrank k (piece J' m)) ∧
    (0 < Module.finrank k (piece J m) → Module.finrank k (piece J' m) < Module.finrank k (piece J m))
```

### `MvPolynomial.finrank_piece_succ_le_macaulayPow`

`Thm_MvPolynomial_finrank_piece_succ_le_macaulayPow` — Macaulay's bound on Hilbert functions of graded quotients

```lean
theorem MvPolynomial.finrank_piece_succ_le_macaulayPow
    (n d : ℕ) (hd : 1 ≤ d) (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J) :
    Module.finrank K (piece J (d + 1)) ≤ Nat.macaulayPow d (Module.finrank K (piece J d))
```

### `MvPolynomial.finrank_piece_sup_span_singleton_succ_add_finrank_piece_eq_of_forall_mul_mem_imp`

`Thm_MvPolynomial_finrank_piece_sup_span_singleton_succ_add_finrank_piece_eq_of_forall_mul_mem_imp` — Hilbert function drop along a nonzerodivisor linear form

```lean
theorem MvPolynomial.finrank_piece_sup_span_singleton_succ_add_finrank_piece_eq_of_forall_mul_mem_imp
    (n : ℕ) (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J)
    (ℓ : MvPolynomial (Fin (n + 1)) K) (hℓ : ℓ.IsHomogeneous 1)
    (hcolon : ∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) K), F.IsHomogeneous d → ℓ * F ∈ J → F ∈ J)
    (d : ℕ) :
    Module.finrank K (piece (J ⊔ Ideal.span {ℓ}) (d + 1)) + Module.finrank K (piece J d) =
      Module.finrank K (piece J (d + 1))
```

### `MvPolynomial.finrank_quotient_span_range_X_pow_eq_prod`

`Thm_MvPolynomial_finrank_quotient_span_range_X_pow_eq_prod` — Rank of a truncated polynomial algebra over a finite index set

```lean
theorem MvPolynomial.finrank_quotient_span_range_X_pow_eq_prod
    (k : Type u) [CommRing k] [Nontrivial k] {ι : Type v} [Fintype ι] (N : ι → ℕ) :
    Module.finrank k (MvPolynomial ι k ⧸
      Ideal.span (Set.range fun i : ι => (MvPolynomial.X i : MvPolynomial ι k) ^ N i)) = ∏ i, N i
```

### `MvPolynomial.forall_apply_eq_apply_smul_of_forall_X_of_eq_act`

`Thm_MvPolynomial_forall_apply_eq_apply_smul_of_forall_X_of_eq_act` — From generators to all of ℤ[Xₙ]: additive intertwining

```lean
theorem MvPolynomial.forall_apply_eq_apply_smul_of_forall_X_of_eq_act
    {σ : Type*} {E : Type*} {M : Type*} {R : Type*}
    [AddCommGroup M] [Module (MvPolynomial σ ℤ) M] [AddCommGroup R]
    (K : E → Prop) (mul : E → E → E) (act : MvPolynomial σ ℤ → E → E)
    (hKact : ∀ (t : MvPolynomial σ ℤ) (x : E), K x → K (act t x))
    (hact_mul : ∀ (s t : MvPolynomial σ ℤ) (x : E), K x → act (s * t) x = act t (act s x))
    (hact_add : ∀ (s t : MvPolynomial σ ℤ) (x : E), K x → act (s + t) x = mul (act s x) (act t x))
    (hact_one : ∀ x : E, K x → act 1 x = x)
    (τ : {x : E // K x} → (M →+ R))
    (hτ : ∀ x y z : {x : E // K x}, z.1 = mul x.1 y.1 → τ z = τ x + τ y)
    (hX : ∀ (n : σ) (x y : {x : E // K x}), y.1 = act (X n) x.1 → ∀ g : M, τ y g = τ x ((X n : MvPolynomial σ ℤ) • g)) :
    ∀ (t : MvPolynomial σ ℤ) (x y : {x : E // K x}), y.1 = act t x.1 → ∀ g : M, τ y g = τ x (t • g)
```

### `MvPolynomial.forall_finrank_piece_succ_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow`

`Thm_MvPolynomial_forall_finrank_piece_succ_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow` — Gotzmann persistence for maximal Macaulay growth

```lean
theorem MvPolynomial.forall_finrank_piece_succ_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow
    (n m : ℕ) (hm : 1 ≤ m) (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
    (hmax : Module.finrank K (piece J (m + 1)) = Nat.macaulayPow m (Module.finrank K (piece J m))) :
    ∀ e : ℕ, m ≤ e → Module.finrank K (piece J (e + 1)) = Nat.macaulayPow e (Module.finrank K (piece J e))
```

### `MvPolynomial.formallySmooth_and_free_and_finite_kaehlerDifferential_of_isLocalization`

`Thm_MvPolynomial_formallySmooth_and_free_and_finite_kaehlerDifferential_of_isLocalization` — Localisations of polynomial rings are formally smooth over the base

```lean
theorem MvPolynomial.formallySmooth_and_free_and_finite_kaehlerDifferential_of_isLocalization
    (R : Type) [CommRing R] {n : ℕ} (M : Submonoid (MvPolynomial (Fin n) R))
    (P : Type) [CommRing P] [Algebra (MvPolynomial (Fin n) R) P] [IsLocalization M P]
    [Algebra R P] [IsScalarTower R (MvPolynomial (Fin n) R) P] :
    Algebra.FormallySmooth R P ∧ Module.Free P Ω[P⁄R] ∧ Module.Finite P Ω[P⁄R]
```

### `MvPolynomial.formallySmooth_localization_atPrime_quotient_of_forall_pderiv_mem`

`Thm_MvPolynomial_formallySmooth_localization_atPrime_quotient_of_forall_pderiv_mem` — Jacobian criterion for formal smoothness of a localised quotient

```lean
theorem MvPolynomial.formallySmooth_localization_atPrime_quotient_of_forall_pderiv_mem
    (R : Type) [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (I J : Ideal (MvPolynomial (Fin n) R)) (hIJ : I ≤ J) [hJ : J.IsMaximal]
    (hJac : ∀ v ∈ I, (∀ i : Fin n, MvPolynomial.pderiv i v ∈ J) → v ∈ J * I) :
    haveI : (J.map (Ideal.Quotient.mk I)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
        rw [Ideal.mk_ker]; exact hIJ)
    Algebra.FormallySmooth R (Localization.AtPrime (J.map (Ideal.Quotient.mk I)))
```

### `MvPolynomial.integrableOn_log_norm_eval_circleMap`

`Thm_MvPolynomial_integrableOn_log_norm_eval_circleMap` — Integrability of log‖P‖ on the torus

```lean
theorem MvPolynomial.integrableOn_log_norm_eval_circleMap {n : ℕ} (P : MvPolynomial (Fin n) ℂ) :
    MeasureTheory.IntegrableOn
      (fun θ : Fin n → ℝ ↦ Real.log ‖MvPolynomial.eval (fun i ↦ circleMap 0 1 (θ i)) P‖)
      (MvPolynomial.torusBox n)
```

### `MvPolynomial.isHomogeneous_of_forall_eval_intCast_mul_eq_pow_mul`

`Thm_MvPolynomial_isHomogeneous_of_forall_eval_intCast_mul_eq_pow_mul` — Integral scaling P(nc)=nᵈP(c) forces homogeneity of degree d

```lean
theorem MvPolynomial.isHomogeneous_of_forall_eval_intCast_mul_eq_pow_mul
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R] {ι : Type*} (P : MvPolynomial ι R) (d : ℕ)
    (h : ∀ (n : ℤ) (c : ι → ℤ), MvPolynomial.eval (fun i => ((n * c i : ℤ) : R)) P =
      (n : R) ^ d * MvPolynomial.eval (fun i => (c i : R)) P) :
    P.IsHomogeneous d
```

### `MvPolynomial.isSquare_or_isSquare_of_isHomogeneous_of_forall_eval_mul_eq`

`Thm_MvPolynomial_isSquare_or_isSquare_of_isHomogeneous_of_forall_eval_mul_eq` — Multiplicative homogeneous quartic on ℤ[X,Y]/(X²-D,Y²-c) forces a square

```lean
theorem MvPolynomial.isSquare_or_isSquare_of_isHomogeneous_of_forall_eval_mul_eq
    (D c : ℤ) (hD : 0 < D) (hc : 0 < c)
    (F : (Fin 4 → ℤ) → ℕ) (P : MvPolynomial (Fin 4) ℚ) (hP : P.IsHomogeneous 4)
    (hF : ∀ v : Fin 4 → ℤ, (F v : ℚ) = MvPolynomial.eval (fun i => (v i : ℚ)) P)
    (hone : F ![1, 0, 0, 0] = 1)
    (hmul : ∀ v w : Fin 4 → ℤ,
      F ![v 0 * w 0 + D * (v 1 * w 1) + c * (v 2 * w 2) + D * c * (v 3 * w 3),
          v 0 * w 1 + v 1 * w 0 + c * (v 2 * w 3 + v 3 * w 2),
          v 0 * w 2 + v 2 * w 0 + D * (v 1 * w 3 + v 3 * w 1),
          v 0 * w 3 + v 3 * w 0 + v 1 * w 2 + v 2 * w 1] = F v * F w)
    (hzd : ∀ r : ℤ, r ^ 2 = D * c → F ![r, 0, 0, 1] = 0) :
    IsSquare D ∨ IsSquare c
```

### `MvPolynomial.isStandardSmoothOfRelativeDimension_natCard`

`Thm_MvPolynomial_isStandardSmoothOfRelativeDimension_natCard` — Polynomial rings are standard smooth of relative dimension #ι

```lean
theorem MvPolynomial.isStandardSmoothOfRelativeDimension_natCard
    (S : Type u) [CommRing S] (ι : Type v) [Finite ι] :
    Algebra.IsStandardSmoothOfRelativeDimension (Nat.card ι) S (MvPolynomial ι S)
```

### `MvPolynomial.ker_aeval_eq_span_sub_one_of_squarefree_of_isWeightedHomogeneous`

`Thm_MvPolynomial_ker_aeval_eq_span_sub_one_of_squarefree_of_isWeightedHomogeneous` — Kernel of (Q,R)-evaluation is generated by A-1

```lean
theorem MvPolynomial.ker_aeval_eq_span_sub_one_of_squarefree_of_isWeightedHomogeneous
    {K : Type*} [Field K] {N : ℕ} (hN : 0 < N) {ζ : K} (hζ : IsPrimitiveRoot ζ N)
    {Q R : PowerSeries K} (hQ0 : PowerSeries.constantCoeff Q = 1)
    (hR0 : PowerSeries.constantCoeff R = 1) (hQR : Q ^ 3 ≠ R ^ 2)
    {A : MvPolynomial (Fin 2) K}
    (hA : A.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) N) (hsq : Squarefree A)
    (hA1 : MvPolynomial.aeval (![Q, R] : Fin 2 → PowerSeries K) A = 1) :
    RingHom.ker (MvPolynomial.aeval (![Q, R] : Fin 2 → PowerSeries K)).toRingHom =
      Ideal.span {A - 1}
```

### `MvPolynomial.le_finrank_piece_of_forall_succ_eq_macaulayPow_of_eventually_eq`

`Thm_MvPolynomial_le_finrank_piece_of_forall_succ_eq_macaulayPow_of_eventually_eq` — Macaulay lower bound for Hilbert functions of maximal growth

```lean
theorem MvPolynomial.le_finrank_piece_of_forall_succ_eq_macaulayPow_of_eventually_eq
    (n g : ℕ) (hg : 1 ≤ g) (H : ℕ → ℕ)
    (hH : ∀ e : ℕ, g ≤ e → H (e + 1) = Nat.macaulayPow e (H e))
    (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J)
    (hev : ∃ D : ℕ, ∀ e : ℕ, D ≤ e → Module.finrank K (piece J e) = H e) :
    ∀ d : ℕ, g ≤ d → H d ≤ Module.finrank K (piece J d)
```

### `MvPolynomial.lmul_eq_pderiv_of_tmul_one_sub_one_tmul_eq_sum_mul`

`Thm_MvPolynomial_lmul_eq_pderiv_of_tmul_one_sub_one_tmul_eq_sum_mul` — Bézout coefficients multiply down to partial derivatives

```lean
theorem MvPolynomial.lmul_eq_pderiv_of_tmul_one_sub_one_tmul_eq_sum_mul
    (R : Type*) [CommRing R] {m : ℕ} (g : MvPolynomial (Fin m) R)
    (a : Fin m → MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R)
    (ha : g ⊗ₜ[R] (1 : MvPolynomial (Fin m) R) - (1 : MvPolynomial (Fin m) R) ⊗ₜ[R] g =
        ∑ j, a j * (MvPolynomial.X j ⊗ₜ[R] 1 - 1 ⊗ₜ[R] MvPolynomial.X j)) (j : Fin m) :
    Algebra.TensorProduct.lmul' R (a j) = MvPolynomial.pderiv j g
```

### `MvPolynomial.logMahlerMeasure_eq_mul_integral_logMahlerMeasure_map_finSuccEquiv`

`Thm_MvPolynomial_logMahlerMeasure_eq_mul_integral_logMahlerMeasure_map_finSuccEquiv` — Mahler measure by integrating out one variable

```lean
theorem MvPolynomial.logMahlerMeasure_eq_mul_integral_logMahlerMeasure_map_finSuccEquiv {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℂ) :
    P.logMahlerMeasure = ((2 * Real.pi)⁻¹) ^ n *
      ∫ θ' in MvPolynomial.torusBox n,
        (Polynomial.map (MvPolynomial.eval (fun i ↦ circleMap 0 1 (θ' i)))
          (MvPolynomial.finSuccEquiv ℂ n P)).logMahlerMeasure
```

### `MvPolynomial.log_norm_coeff_le_logMahlerMeasure_add`

`Thm_MvPolynomial_log_norm_coeff_le_logMahlerMeasure_add` — Mahler's bound: coefficients versus logarithmic Mahler measure

```lean
theorem MvPolynomial.log_norm_coeff_le_logMahlerMeasure_add {n : ℕ} (P : MvPolynomial (Fin n) ℂ) {m : Fin n →₀ ℕ} (hm : m ∈ P.support) :
    Real.log ‖MvPolynomial.coeff m P‖ ≤
      P.logMahlerMeasure + (∑ i, (MvPolynomial.degreeOf i P : ℝ)) * Real.log 2
```

### `MvPolynomial.measure_setOf_eval_eq_zero_of_ne_zero`

`Thm_MvPolynomial_measure_setOf_eval_eq_zero_of_ne_zero` — Zero sets of non-zero polynomials are Haar-null

```lean
theorem MvPolynomial.measure_setOf_eval_eq_zero_of_ne_zero
    (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace F] [T2Space F]
    [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] (hF : ¬ DiscreteTopology F)
    (ι : Type) [Fintype ι] (p : MvPolynomial ι F) (hp : p ≠ 0)
    (μ : Measure (ι → F)) [μ.IsAddHaarMeasure] :
    μ {x : ι → F | MvPolynomial.eval x p = 0} = 0
```

### `MvPolynomial.mem_ideal_iff_forall_map_mem_map_localizationAway`

`Thm_MvPolynomial_mem_ideal_iff_forall_map_mem_map_localizationAway` — Ideal membership in A[σ] is Zariski-local on Spec A

```lean
theorem MvPolynomial.mem_ideal_iff_forall_map_mem_map_localizationAway
    {σ : Type} (A : Type) [CommRing A] {ι : Type} (r : ι → A) (hr : Ideal.span (Set.range r) = ⊤)
    (I : Ideal (MvPolynomial σ A)) (f : MvPolynomial σ A) :
    f ∈ I ↔ ∀ i : ι,
      MvPolynomial.map (algebraMap A (Localization.Away (r i))) f ∈
        Ideal.map (MvPolynomial.map (algebraMap A (Localization.Away (r i)))) I
```

### `MvPolynomial.mem_mul_of_forall_pderiv_mem_of_forall_exists_algHom_lift`

`Thm_MvPolynomial_mem_mul_of_forall_pderiv_mem_of_forall_exists_algHom_lift` — Jacobian criterion step: dv=0 forces v ∈ J I

```lean
theorem MvPolynomial.mem_mul_of_forall_pderiv_mem_of_forall_exists_algHom_lift
    (R : Type) [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (I J : Ideal (MvPolynomial (Fin n) R)) (hIJ : I ≤ J) (hJ : J.IsMaximal)

    (D : ℕ → Type) [∀ N, CommRing (D N)] [∀ N, Algebra R (D N)]
    [∀ N, Algebra (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N)]
    [∀ N, IsScalarTower R (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N)]
    [∀ N, Module.FaithfullyFlat (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N)]
    (σ : ∀ N, (MvPolynomial (Fin n) R ⧸ I) →ₐ[R] D N)
    (hσ : ∀ (N : ℕ) (f : MvPolynomial (Fin n) R),
      σ N (Ideal.Quotient.mk I f) -
          algebraMap (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N) (Ideal.Quotient.mk (J ^ N ⊔ J * I) f) ∈
        Ideal.map (algebraMap (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N))
          (Ideal.map (Ideal.Quotient.mk (J ^ N ⊔ J * I)) (J ^ N ⊔ I)))
    (v : MvPolynomial (Fin n) R) (hv : v ∈ I) (hdv : ∀ i : Fin n, MvPolynomial.pderiv i v ∈ J) :
    v ∈ J * I
```

### `MvPolynomial.mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow`

`Thm_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow` — Maximal Macaulay growth at m forces saturation in degrees ≥ m

```lean
theorem MvPolynomial.mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow
    (n m : ℕ) (hm : 1 ≤ m) (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
    (hmax : Module.finrank K (piece J (m + 1)) = Nat.macaulayPow m (Module.finrank K (piece J m)))
    (d : ℕ) (hd : m ≤ d) (F : MvPolynomial (Fin (n + 1)) K) (hF : F.IsHomogeneous d)
    (hsat : ∀ i : Fin (n + 1), ∃ N : ℕ, X i ^ N * F ∈ J) :
    F ∈ J
```

### `MvPolynomial.mem_span_map_of_aeval_X_pow_mem_span_map`

`Thm_MvPolynomial_mem_span_map_of_aeval_X_pow_mem_span_map` — Divisibility by a prime over 𝔽ₚ descends along Xᵢ ↦ Xᵢ^{p^n}

```lean
theorem MvPolynomial.mem_span_map_of_aeval_X_pow_mem_span_map
    {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [Algebra (ZMod p) K] {σ : Type*} (n : ℕ)
    (f : MvPolynomial σ (ZMod p)) (hf : Prime f) (g : MvPolynomial σ K)
    (hg : MvPolynomial.aeval (fun i => (MvPolynomial.X i : MvPolynomial σ K) ^ p ^ n) g ∈
      Ideal.span {MvPolynomial.map (algebraMap (ZMod p) K) f}) :
    g ∈ Ideal.span {MvPolynomial.map (algebraMap (ZMod p) K) f}
```

### `MvPolynomial.mem_span_of_linear_mul_mem_of_forall_relation_modulo_mem_span`

`Thm_MvPolynomial_mem_span_of_linear_mul_mem_of_forall_relation_modulo_mem_span` — Bayer–Stillman inductive step for colon ideals in degrees ≥ m

```lean
theorem MvPolynomial.mem_span_of_linear_mul_mem_of_forall_relation_modulo_mem_span
    (n m g : ℕ) (K : Type) [Field K] (F : Fin g → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous m) (ℓ : MvPolynomial (Fin (n + 1)) K) (hℓ : ℓ.IsHomogeneous 1)
    (hcol : ∀ f : MvPolynomial (Fin (n + 1)) K, f.IsHomogeneous m →
      ℓ * f ∈ Ideal.span (Set.range F) → f ∈ Ideal.span (Set.range F))
    (hrel : ∀ (d : ℕ) (c : Fin g → MvPolynomial (Fin (n + 1)) K), (∀ i, (c i).IsHomogeneous d) →
      ∑ i, c i * F i ∈ Ideal.span {ℓ} →
      c ∈ Submodule.span (MvPolynomial (Fin (n + 1)) K)
        {l : Fin g → MvPolynomial (Fin (n + 1)) K |
          (∃ d' ≤ 1, ∀ i, (l i).IsHomogeneous d') ∧ ∑ i, l i * F i ∈ Ideal.span {ℓ}})
    (k : ℕ) (hk : m ≤ k) (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous k)
    (h : ℓ * f ∈ Ideal.span (Set.range F)) : f ∈ Ideal.span (Set.range F)
```

### `MvPolynomial.nonempty_truncated_quotient_span_singleton_algEquiv_truncated_of_not_mem_sq`

`Thm_MvPolynomial_nonempty_truncated_quotient_span_singleton_algEquiv_truncated_of_not_mem_sq` — Killing an element of tsetminust² in a truncated polynomial algebra

```lean
theorem MvPolynomial.nonempty_truncated_quotient_span_singleton_algEquiv_truncated_of_not_mem_sq
    (k : Type*) [Field k] (N M : ℕ)
    (x : (MvPolynomial (Fin (N + 1)) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin (N + 1)) k →+* k)) ^ (M + 1)))
    (hx₁ : x ∈ Ideal.map (Ideal.Quotient.mk ((RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin (N + 1)) k →+* k)) ^ (M + 1)))
        (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin (N + 1)) k →+* k)))
    (hx₂ : x ∉ (Ideal.map (Ideal.Quotient.mk ((RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin (N + 1)) k →+* k)) ^ (M + 1)))
        (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin (N + 1)) k →+* k))) ^ 2) :
    Nonempty (((MvPolynomial (Fin (N + 1)) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin (N + 1)) k →+* k)) ^ (M + 1)) ⧸ Ideal.span ({x} : Set _)) ≃ₐ[k]
      (MvPolynomial (Fin N) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin N) k →+* k)) ^ (M + 1)))
```

### `MvPolynomial.relation_mem_span_of_forall_finrank_piece_succ_le`

`Thm_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le` — Maximal Hilbert growth forces relations in degrees ≤ 1

```lean
theorem MvPolynomial.relation_mem_span_of_forall_finrank_piece_succ_le
    (n m g : ℕ) (K : Type) [Field K] (F : Fin g → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous m)
    (hmax : ∀ J' : Ideal (MvPolynomial (Fin (n + 1)) K),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ J' = Ideal.span s) →
      Module.finrank K (piece J' m) = Module.finrank K (piece (Ideal.span (Set.range F)) m) →
      Module.finrank K (piece J' (m + 1)) ≤ Module.finrank K (piece (Ideal.span (Set.range F)) (m + 1)))
    (d : ℕ) (c : Fin g → MvPolynomial (Fin (n + 1)) K) (hc : ∀ i, (c i).IsHomogeneous d)
    (hcF : ∑ i, c i * F i = 0) :
    c ∈ Submodule.span (MvPolynomial (Fin (n + 1)) K)
      {l : Fin g → MvPolynomial (Fin (n + 1)) K |
        (∃ d' ≤ 1, ∀ i, (l i).IsHomogeneous d') ∧ ∑ i, l i * F i = 0}
```

### `MvPolynomial.relation_mem_span_of_forall_isHomogeneous_mem_span`

`Thm_MvPolynomial_relation_mem_span_of_forall_isHomogeneous_mem_span` — Relations among degree-m forms spanning S_m are generated in degrees ≤ 1

```lean
theorem MvPolynomial.relation_mem_span_of_forall_isHomogeneous_mem_span
    (n m g : ℕ) (K : Type) [Field K] (F : Fin g → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous m)
    (hspan : ∀ w : MvPolynomial (Fin (n + 1)) K, w.IsHomogeneous m → w ∈ Submodule.span K (Set.range F))
    (d : ℕ) (c : Fin g → MvPolynomial (Fin (n + 1)) K) (hc : ∀ i, (c i).IsHomogeneous d)
    (hcF : ∑ i, c i * F i = 0) :
    c ∈ Submodule.span (MvPolynomial (Fin (n + 1)) K)
      {l : Fin g → MvPolynomial (Fin (n + 1)) K |
        (∃ d' ≤ 1, ∀ i, (l i).IsHomogeneous d') ∧ ∑ i, l i * F i = 0}
```

### `MvPolynomial.relation_mem_span_of_linear_of_forall_relation_modulo_mem_span`

`Thm_MvPolynomial_relation_mem_span_of_linear_of_forall_relation_modulo_mem_span` — Relations generated in degree ≤ 1 from a hyperplane section

```lean
theorem MvPolynomial.relation_mem_span_of_linear_of_forall_relation_modulo_mem_span
    (n m g : ℕ) (K : Type) [Field K] (F : Fin g → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous m) (ℓ : MvPolynomial (Fin (n + 1)) K) (hℓ : ℓ.IsHomogeneous 1)
    (hcol : ∀ f : MvPolynomial (Fin (n + 1)) K, f.IsHomogeneous m →
      ℓ * f ∈ Ideal.span (Set.range F) → f ∈ Ideal.span (Set.range F))
    (hrel : ∀ (d : ℕ) (c : Fin g → MvPolynomial (Fin (n + 1)) K), (∀ i, (c i).IsHomogeneous d) →
      ∑ i, c i * F i ∈ Ideal.span {ℓ} →
      c ∈ Submodule.span (MvPolynomial (Fin (n + 1)) K)
        {l : Fin g → MvPolynomial (Fin (n + 1)) K |
          (∃ d' ≤ 1, ∀ i, (l i).IsHomogeneous d') ∧ ∑ i, l i * F i ∈ Ideal.span {ℓ}})
    (d : ℕ) (c : Fin g → MvPolynomial (Fin (n + 1)) K) (hc : ∀ i, (c i).IsHomogeneous d)
    (hcF : ∑ i, c i * F i = 0) :
    c ∈ Submodule.span (MvPolynomial (Fin (n + 1)) K)
      {l : Fin g → MvPolynomial (Fin (n + 1)) K |
        (∃ d' ≤ 1, ∀ i, (l i).IsHomogeneous d') ∧ ∑ i, l i * F i = 0}
```

### `MvPolynomial.squarefree_of_isWeightedHomogeneous_of_aeval_eq_one`

`Thm_MvPolynomial_squarefree_of_isWeightedHomogeneous_of_aeval_eq_one` — Squarefreeness of the isobaric relation A(Q,R)=1

```lean
theorem MvPolynomial.squarefree_of_isWeightedHomogeneous_of_aeval_eq_one
    {K : Type*} [Field K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (h5 : 5 ≤ ℓ)
    {P Q R : PowerSeries K}
    (hP0 : PowerSeries.constantCoeff P = 1) (hQ0 : PowerSeries.constantCoeff Q = 1)
    (hR0 : PowerSeries.constantCoeff R = 1) (hQR : Q ^ 3 ≠ R ^ 2)
    (hP : 12 * (PowerSeries.X * PowerSeries.derivative K P) = P ^ 2 - Q)
    (hQ : 3 * (PowerSeries.X * PowerSeries.derivative K Q) = P * Q - R)
    (hR : 2 * (PowerSeries.X * PowerSeries.derivative K R) = P * R - Q ^ 2)
    {A : MvPolynomial (Fin 2) K}
    (hA : A.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) (ℓ - 1))
    (hA1 : MvPolynomial.aeval (![Q, R] : Fin 2 → PowerSeries K) A = 1) :
    Squarefree A
```

## LinearMap (58)

### `LinearMap.BilinForm.forall_mem_of_forall_apply_eq_zero_and_exists_quotient_equiv_dual_of_isotropic_of_card_sq_eq`

`Thm_LinearMap_BilinForm_forall_mem_of_forall_apply_eq_zero_and_exists_quotient_equiv_dual_of_isotropic_of_card_sq_eq` — Maximal isotropic subspace equals its orthogonal; V/A ≅ A^∨

```lean
theorem LinearMap.BilinForm.forall_mem_of_forall_apply_eq_zero_and_exists_quotient_equiv_dual_of_isotropic_of_card_sq_eq
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (b : LinearMap.BilinForm (ZMod p) V)
    (hleft : ∀ x : V, (∀ y : V, b x y = 0) → x = 0) (hright : ∀ y : V, (∀ x : V, b x y = 0) → y = 0)
    (A : Submodule (ZMod p) V) (hiso : ∀ x ∈ A, ∀ y ∈ A, b x y = 0)
    (hcard : Nat.card A ^ 2 = Nat.card V) :
    (∀ y : V, (∀ a ∈ A, b a y = 0) → y ∈ A) ∧
    ∃ φ : (V ⧸ A) ≃ₗ[ZMod p] (A →ₗ[ZMod p] ZMod p),
      ∀ (y : V) (a : A), φ (Submodule.Quotient.mk y) a = b a y
```

### `LinearMap.BilinForm.orthogonal_le_of_similitude_of_forall_map_sub_mem`

`Thm_LinearMap_BilinForm_orthogonal_le_of_similitude_of_forall_map_sub_mem` — Orthogonal of a subspace moved onto by a similitude

```lean
theorem LinearMap.BilinForm.orthogonal_le_of_similitude_of_forall_map_sub_mem
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (hB : ∀ w : V, (∀ x : V, B x w = 0) → w = 0)
    (V₀ : Submodule K V) (g : V →ₗ[K] V) (hg : Function.Surjective g)
    (ε : K) (hε : ε ≠ 1)
    (hsim : ∀ x y : V, B (g x) (g y) = ε * B x y)
    (hmove : ∀ x : V, g x - x ∈ V₀) :
    B.orthogonal V₀ ≤ V₀
```

### `LinearMap.BilinForm.orthogonal_le_sup_of_restrict_nondegenerate_of_forall_sub_mem_sup`

`Thm_LinearMap_BilinForm_orthogonal_le_sup_of_restrict_nondegenerate_of_forall_sub_mem_sup` — Orthogonal of the toric part lies in toric + old

```lean
theorem LinearMap.BilinForm.orthogonal_le_sup_of_restrict_nondegenerate_of_forall_sub_mem_sup
    {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Γ : Type*} [Group Γ] (ρ : Representation K Γ V) (χ : Γ →* Kˣ)
    (I : Subgroup Γ)
    (e : LinearMap.BilinForm K V)
    (hrefl : ∀ a b : V, e a b = 0 → e b a = 0)
    (hnondeg : ∀ a : V, (∀ b : V, e a b = 0) → a = 0)
    (hequiv : ∀ (γ : Γ) (a b : V), e (ρ γ a) (ρ γ b) = ((χ γ : Kˣ) : K) * e a b)
    (Vt Vo : Submodule K V)
    (hVt : ∀ γ ∈ I, ∀ x ∈ Vt, ρ γ x ∈ Vt)
    (hVo : ∀ γ ∈ I, ∀ y ∈ Vo, ρ γ y ∈ Vo)
    (hISO : ∀ x ∈ Vt, ∀ y ∈ Vo, e x y = 0)
    (hCUT : ∀ τ ∈ I, ∀ v : V, ρ τ v - v ∈ Vt ⊔ Vo)
    (hOLD : ∀ y ∈ Vo, (∀ y' ∈ Vo, e y y' = 0) → y = 0)
    (hCYC : ∃ τ₀ ∈ I, χ τ₀ ≠ 1) :
    e.orthogonal Vt ≤ Vt ⊔ Vo
```

### `LinearMap.BilinForm.sup_iSup_range_ne_top_of_orthogonal_le_of_finrank_ker_aeval_eq_two_mul`

`Thm_LinearMap_BilinForm_sup_iSup_range_ne_top_of_orthogonal_le_of_finrank_ker_aeval_eq_two_mul` — A coisotropic stable subspace plus ideal image cannot exhaust V

```lean
theorem LinearMap.BilinForm.sup_iSup_range_ne_top_of_orthogonal_le_of_finrank_ker_aeval_eq_two_mul
    {K V R : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [CommRing R] [Algebra K R] (φ : R →ₐ[K] Module.End K V)
    (B : LinearMap.BilinForm K V)
    (hBl : ∀ v : V, (∀ w : V, B v w = 0) → v = 0) (hBr : ∀ w : V, (∀ v : V, B v w = 0) → w = 0)
    (hadj : ∀ (r : R) (v w : V), B (φ r v) w = B v (φ r w))
    (V₀ : Submodule K V) (hst : ∀ (r : R), ∀ v ∈ V₀, φ r v ∈ V₀)
    (hco : ∀ w : V, (∀ v ∈ V₀, B v w = 0) → w ∈ V₀)
    (t : R) (Pu Pn : Polynomial K) (hcop : IsCoprime Pu Pn)
    (hann : Polynomial.aeval (φ t) (Pu * Pn) = 0)
    (hn : LinearMap.ker (Polynomial.aeval (φ t) Pn) ≤ V₀)
    (hu : Module.finrank K ↥(LinearMap.ker (Polynomial.aeval (φ t) Pu)) =
      2 * (Module.finrank K V - Module.finrank K V₀))
    (𝔪 : Ideal R) (h𝔪 : 𝔪 ≠ ⊤) (hker : ∀ r : R, φ r = 0 → r ∈ 𝔪)
    (c : K) (htc : t - algebraMap K R c ∈ 𝔪) (hc : Pn.eval c ≠ 0) :
    V₀ ⊔ (⨆ r ∈ 𝔪, LinearMap.range (φ r)) ≠ ⊤
```

### `LinearMap.baseChange_free_finrank_two_and_span_eq_top_and_trace_eq`

`Thm_LinearMap_baseChange_free_finrank_two_and_span_eq_top_and_trace_eq` — Burnside spanning and traces under base change

```lean
theorem LinearMap.baseChange_free_finrank_two_and_span_eq_top_and_trace_eq
    {R : Type} [CommRing R] {k : Type} [CommRing k] [Algebra R k] [Nontrivial k]
    {G : Type} [Group G]
    {V : Type} [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V] (hV : Module.finrank R V = 2)
    (ρV : G →* Module.End R V) (hspan : Submodule.span R (Set.range ⇑ρV) = ⊤) :
    Module.finrank k (k ⊗[R] V) = 2 ∧
    Submodule.span k (Set.range (fun g : G => (ρV g).baseChange k)) = ⊤ ∧
    (∀ g : G, LinearMap.trace k (k ⊗[R] V) ((ρV g).baseChange k) = algebraMap R k (LinearMap.trace R V (ρV g))) ∧
    (∀ (g : G) (v : V), ((ρV g).baseChange k) ((1 : k) ⊗ₜ[R] v) = (1 : k) ⊗ₜ[R] (ρV g v)) ∧
    (Function.Injective (algebraMap R k) → Function.Injective (fun v : V => (1 : k) ⊗ₜ[R] v))
```

### `LinearMap.bijective_and_flip_bijective_of_baseChange_residueField`

`Thm_LinearMap_bijective_and_flip_bijective_of_baseChange_residueField` — Perfectness of a pairing descends from the residue field

```lean
theorem LinearMap.bijective_and_flip_bijective_of_baseChange_residueField
    {R : Type u} [CommRing R] [IsLocalRing R] {k : Type v} [Field k] [Algebra R k]
    {M : Type w₁} {N : Type w₂} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {Mk : Type w₁'} {Nk : Type w₂'} [AddCommGroup Mk] [Module k Mk] [AddCommGroup Nk] [Module k Nk]
    [Module.Free R M] [Module.Finite R M] [Module.Free R N] [Module.Finite R N]
    (hπ : Function.Surjective (algebraMap R k))
    (B : M →ₗ[R] N →ₗ[R] R) (Bk : Mk →ₗ[k] Nk →ₗ[k] k)
    (eM : k ⊗[R] M ≃ₗ[k] Mk) (eN : k ⊗[R] N ≃ₗ[k] Nk)
    (hcomp : ∀ m n, Bk (eM (1 ⊗ₜ[R] m)) (eN (1 ⊗ₜ[R] n)) = algebraMap R k (B m n))
    (hBk : Function.Bijective Bk ∧ Function.Bijective Bk.flip) :
    Function.Bijective B ∧ Function.Bijective B.flip
```

### `LinearMap.bijective_baseChange_baseChange_of_bijective_baseChange_fractionRing`

`Thm_LinearMap_bijective_baseChange_baseChange_of_bijective_baseChange_fractionRing` — Generic bijectivity persists under extension of the domain

```lean
theorem LinearMap.bijective_baseChange_baseChange_of_bijective_baseChange_fractionRing
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (hf : Function.Bijective (f.baseChange K))
    (R₂ : Type u) [CommRing R₂] [IsDomain R₂] [Algebra R R₂] (hinj : Function.Injective (algebraMap R R₂))
    (K₂ : Type u) [Field K₂] [Algebra R₂ K₂] [IsFractionRing R₂ K₂] :
    Function.Bijective ((f.baseChange R₂).baseChange K₂)
```

### `LinearMap.bijective_of_forall_bijective_baseChange_quotient_maximal`

`Thm_LinearMap_bijective_of_forall_bijective_baseChange_quotient_maximal` — Bijectivity from bijectivity of all residue base changes

```lean
theorem LinearMap.bijective_of_forall_bijective_baseChange_quotient_maximal
    {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Free R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Free R N] (f : M →ₗ[R] N)
    (h : ∀ (𝔪 : Ideal R) [𝔪.IsMaximal], Function.Bijective (f.baseChange (R ⧸ 𝔪))) :
    Function.Bijective f
```

### `LinearMap.charpoly_eq_X_sub_one_sq_of_sub_one_mul_self_eq_zero`

`Thm_LinearMap_charpoly_eq_X_sub_one_sq_of_sub_one_mul_self_eq_zero` — Rank-two unipotent endomorphism has charpoly (X-1)²

```lean
theorem LinearMap.charpoly_eq_X_sub_one_sq_of_sub_one_mul_self_eq_zero {A : Type u} [CommRing A]
    [IsDomain A] {V : Type v} [AddCommGroup V] [Module A V] [Module.Free A V] [Module.Finite A V]
    (hV : Module.finrank A V = 2) (f : Module.End A V) (hf : (f - 1) * (f - 1) = 0) :
    LinearMap.charpoly f = (Polynomial.X - 1) ^ 2
```

### `LinearMap.charpoly_eq_iff_of_finrank_eq_two`

`Thm_LinearMap_charpoly_eq_iff_of_finrank_eq_two` — Characteristic polynomial of a rank-two endomorphism: coefficient criterion

```lean
theorem LinearMap.charpoly_eq_iff_of_finrank_eq_two {R : Type*} {M : Type*} [CommRing R] [Nontrivial R] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] (h : Module.finrank R M = 2) (f : M →ₗ[R] M) (a b : R) : f.charpoly = X ^ 2 - C a * X + C b ↔ LinearMap.trace R M f = a ∧ LinearMap.det f = b
```

### `LinearMap.charpoly_of_finrank_eq_two`

`Thm_LinearMap_charpoly_of_finrank_eq_two` — Characteristic polynomial of a rank-two endomorphism

```lean
theorem LinearMap.charpoly_of_finrank_eq_two {R : Type*} {M : Type*} [CommRing R] [Nontrivial R] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] (h : Module.finrank R M = 2) (f : M →ₗ[R] M) : f.charpoly = X ^ 2 - C (LinearMap.trace R M f) * X + C (LinearMap.det f)
```

### `LinearMap.exact_dualMap_of_exact`

`Thm_LinearMap_exact_dualMap_of_exact` — Duality preserves exactness of linear maps over a field

```lean
theorem LinearMap.exact_dualMap_of_exact {K V₁ V₂ V₃ : Type*} [Field K]
    [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂] [AddCommGroup V₃] [Module K V₃]
    (f : V₁ →ₗ[K] V₂) (g : V₂ →ₗ[K] V₃) (h : Function.Exact f g) :
    Function.Exact g.dualMap f.dualMap
```

### `LinearMap.existsUnique_baseChange_eq_of_isFractionRing_of_forall_rTensor_apply_eq`

`Thm_LinearMap_existsUnique_baseChange_eq_of_isFractionRing_of_forall_rTensor_apply_eq` — Descent of linear maps along K ∩ ̂ O = O

```lean
theorem LinearMap.existsUnique_baseChange_eq_of_isFractionRing_of_forall_rTensor_apply_eq
    (O : Type u) [CommRing O] [IsDomain O] (K : Type u) [Field K] [Algebra O K] [IsFractionRing O K]
    (Oh : Type u) [CommRing Oh] [Algebra O Oh]
    (Kh : Type u) [CommRing Kh] [Algebra O Kh] [Algebra K Kh] [Algebra Oh Kh] [IsScalarTower O K Kh] [IsScalarTower O Oh Kh]
    (hinj : Function.Injective (algebraMap Oh Kh))
    (hcap : ∀ (x : K) (y : Oh), algebraMap K Kh x = algebraMap Oh Kh y → ∃ z : O, algebraMap O K z = x)
    (M : Type u) [AddCommGroup M] [Module O M] [Module.Free O M] [Module.Finite O M]
    (N : Type u) [AddCommGroup N] [Module O N] [Module.Free O N] [Module.Finite O N]
    (fK : K ⊗[O] M →ₗ[K] K ⊗[O] N) (fOh : Oh ⊗[O] M →ₗ[Oh] Oh ⊗[O] N)
    (hagree : ∀ m : M,
      ((IsScalarTower.toAlgHom O K Kh).toLinearMap.rTensor N) (fK ((1 : K) ⊗ₜ m)) =
        ((IsScalarTower.toAlgHom O Oh Kh).toLinearMap.rTensor N) (fOh ((1 : Oh) ⊗ₜ m))) :
    ∃! f : M →ₗ[O] N, f.baseChange K = fK ∧ f.baseChange Oh = fOh
```

### `LinearMap.existsUnique_sub_eq_comp_comp_of_extension`

`Thm_LinearMap_existsUnique_sub_eq_comp_comp_of_extension` — Two maps of extensions agreeing on the ends differ uniquely

```lean
theorem LinearMap.existsUnique_sub_eq_comp_comp_of_extension
    {R : Type u} [CommRing R]
    {K : Type v} {M : Type w} {M' : Type w'} {E : Type x}
    [AddCommGroup K] [Module R K] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup E] [Module R E]
    (ϑ : K →ₗ[R] M) (θ : M →ₗ[R] E) (ϑ' : K →ₗ[R] M') (θ' : M' →ₗ[R] E)
    (hθ : Function.Surjective θ) (hex : LinearMap.range ϑ = LinearMap.ker θ)
    (hϑ' : Function.Injective ϑ') (hex' : LinearMap.range ϑ' = LinearMap.ker θ')
    (α β : M →ₗ[R] M') (hK : α ∘ₗ ϑ = β ∘ₗ ϑ) (hE : θ' ∘ₗ α = θ' ∘ₗ β) :
    ∃! γ : E →ₗ[R] K, α - β = ϑ' ∘ₗ γ ∘ₗ θ
```

### `LinearMap.exists_apply_basis_eq_smul_of_mul_eq_pow_mul_of_toMatrix_sub_one_mem`

`Thm_LinearMap_exists_apply_basis_eq_smul_of_mul_eq_pow_mul_of_toMatrix_sub_one_mem` — Diagonality of a tame inertia operator in a Frobenius eigenbasis

```lean
theorem LinearMap.exists_apply_basis_eq_smul_of_mul_eq_pow_mul_of_toMatrix_sub_one_mem {R : Type u} [CommRing R] [IsLocalRing R]
    (hH : ∀ x : R, (∀ n : ℕ, x ∈ IsLocalRing.maximalIdeal R ^ n) → x = 0)
    {V : Type v} [AddCommGroup V] [Module R V] (b : Module.Basis (Fin 2) R V) (Φ N : Module.End R V)
    {a d : R} {q : ℕ} (hΦ0 : Φ (b 0) = a • b 0) (hΦ1 : Φ (b 1) = d • b 1)
    (had : IsUnit (a - (q : R) * d)) (hda : IsUnit (d - (q : R) * a))
    (hN : ∀ i j, LinearMap.toMatrix b b N i j - (1 : Matrix (Fin 2) (Fin 2) R) i j ∈ IsLocalRing.maximalIdeal R)
    (hrel : Φ * N = N ^ q * Φ) :
    ∃ x y : R, IsUnit x ∧ IsUnit y ∧ N (b 0) = x • b 0 ∧ N (b 1) = y • b 1
```

### `LinearMap.exists_basis_apply_eq_smul_and_isUnit_and_card_le_of_finrank_ker_baseChange_le`

`Thm_LinearMap_exists_basis_apply_eq_smul_and_isUnit_and_card_le_of_finrank_ker_baseChange_le` — Smith normal form with at most r non-unit factors

```lean
theorem LinearMap.exists_basis_apply_eq_smul_and_isUnit_and_card_le_of_finrank_ker_baseChange_le
    (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]
    (M : Type) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (f : M →ₗ[R] M) (hf : Function.Injective f) (r : ℕ)
    (hker : Module.finrank (IsLocalRing.ResidueField R)
        (LinearMap.ker (f.baseChange (IsLocalRing.ResidueField R))) ≤ r) :
    ∃ (n : ℕ) (b b' : Module.Basis (Fin n) R M) (a : Fin n → R) (s : Finset (Fin n)),
      (∀ i, f (b i) = a i • b' i) ∧ (∀ i ∉ s, IsUnit (a i)) ∧ s.card ≤ r
```

### `LinearMap.exists_basis_apply_eq_smul_of_charpoly_map_residue_eq`

`Thm_LinearMap_exists_basis_apply_eq_smul_of_charpoly_map_residue_eq` — Hensel eigenbasis for a rank-2 endomorphism with distinct residual eigenvalues

```lean
theorem LinearMap.exists_basis_apply_eq_smul_of_charpoly_map_residue_eq {R : Type u} [CommRing R] [IsLocalRing R] [HenselianLocalRing R]
    {V : Type v} [AddCommGroup V] [Module R V] (b₀ : Module.Basis (Fin 2) R V) (Φ : Module.End R V)
    {α β : IsLocalRing.ResidueField R} (hαβ : α ≠ β)
    (hchar : ((LinearMap.toMatrix b₀ b₀ Φ).charpoly).map (IsLocalRing.residue R)
      = (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β)) :
    ∃ (b : Module.Basis (Fin 2) R V) (a d : R), IsUnit (a - d) ∧
      IsLocalRing.residue R a = α ∧ IsLocalRing.residue R d = β ∧
      Φ (b 0) = a • b 0 ∧ Φ (b 1) = d • b 1
```

### `LinearMap.exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range`

`Thm_LinearMap_exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range` — Coherent lifts with prescribed restriction to the relation module

```lean
theorem LinearMap.exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range
    {B : Type u} [CommRing B] [IsNoetherianRing B] (J : Ideal B)
    {GE GK : Type u} [AddCommGroup GE] [Module B GE] [AddCommGroup GK] [Module B GK] [Module.Finite B GK]
    {r : ℕ} (p : (Fin r → B) →ₗ[B] GE) (hp : Function.Surjective p)
    (F E : ℕ → Type u) [∀ k, AddCommGroup (F k)] [∀ k, Module B (F k)] [∀ k, AddCommGroup (E k)] [∀ k, Module B (E k)]
    (φ : ∀ k, F (k + 1) →ₗ[B] F k) (hφs : ∀ k, Function.Surjective (φ k))
    (hφk : ∀ k, LinearMap.ker (φ k) = J ^ (k + 1) • (⊤ : Submodule B (F (k + 1))))
    (ε : ∀ k, F k →ₗ[B] E k) (ψE : ∀ k, GE →ₗ[B] E k) (lam : ∀ k, GK →ₗ[B] F k)
    (hlamc : ∀ k, φ k ∘ₗ lam (k + 1) = lam k) (hlamr : ∀ k, LinearMap.range (lam k) = LinearMap.ker (ε k))

    (ℓ : ∀ n, (Fin r → B) →ₗ[B] F n) (hℓε : ∀ n, ε n ∘ₗ ℓ n = ψE n ∘ₗ p) (hℓφ : ∀ n, φ n ∘ₗ ℓ (n + 1) = ℓ n)
    (δs : ∀ n, ↥(LinearMap.ker p) →ₗ[B] GK) (hδs : ∀ n, lam n ∘ₗ δs n = ℓ n ∘ₗ (LinearMap.ker p).subtype)
    (hδsc : ∀ n, δs (n + 1) - δs n ∈ J ^ (n + 1) • (⊤ : Submodule B (↥(LinearMap.ker p) →ₗ[B] GK)))

    (δ : ↥(LinearMap.ker p) →ₗ[B] GK)
    (hδ : ∀ n, δ - δs n ∈ J ^ (n + 1) • (⊤ : Submodule B (↥(LinearMap.ker p) →ₗ[B] GK)) ⊔
      LinearMap.range (LinearMap.lcomp B GK (LinearMap.ker p).subtype)) :
    ∃ ℓ' : ∀ k, (Fin r → B) →ₗ[B] F k,
      (∀ k, φ k ∘ₗ ℓ' (k + 1) = ℓ' k) ∧
      (∀ k, ε k ∘ₗ ℓ' k = ψE k ∘ₗ p) ∧
      (∀ k, ℓ' k ∘ₗ (LinearMap.ker p).subtype = lam k ∘ₗ δ)
```

### `LinearMap.exists_forall_eq_zero_of_tendsto_apply_of_finiteDimensional`

`Thm_LinearMap_exists_forall_eq_zero_of_tendsto_apply_of_finiteDimensional` — Pointwise limits of linear maps on a finite-dimensional function space are eventually injective

```lean
theorem LinearMap.exists_forall_eq_zero_of_tendsto_apply_of_finiteDimensional
    {X : Type*} (Y : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ ↥Y]
    (T : ℕ → (↥Y →ₗ[ℂ] (X → ℂ)))
    (hT : ∀ (y : ↥Y) (x : X), Filter.Tendsto (fun n => T n y x) Filter.atTop (nhds ((y : X → ℂ) x))) :
    ∃ n, ∀ y : ↥Y, T n y = 0 → y = 0
```

### `LinearMap.exists_forall_exists_finAppend_mkQ_sub_mkQ_mem_pow_smul_top`

`Thm_LinearMap_exists_forall_exists_finAppend_mkQ_sub_mkQ_mem_pow_smul_top` — Two presentations give Jⁿ⁺¹-congruent classes after a uniform shift

```lean
theorem LinearMap.exists_forall_exists_finAppend_mkQ_sub_mkQ_mem_pow_smul_top
    {B : Type u} [CommRing B] [IsNoetherianRing B] (J : Ideal B)
    {GE GK : Type v} [AddCommGroup GE] [Module B GE] [AddCommGroup GK] [Module B GK] [Module.Finite B GK]
    (F E : ℕ → Type w) [∀ k, AddCommGroup (F k)] [∀ k, Module B (F k)] [∀ k, AddCommGroup (E k)] [∀ k, Module B (E k)]
    (ε : ∀ k, F k →ₗ[B] E k) (ψE : ∀ k, GE →ₗ[B] E k) (lam : ∀ k, GK →ₗ[B] F k)
    (hlamr : ∀ k, LinearMap.range (lam k) = LinearMap.ker (ε k))
    (hlami : ∃ c : ℕ, ∀ k : ℕ, LinearMap.ker (lam (k + c)) ≤ J ^ (k + 1) • (⊤ : Submodule B GK))
    {r₁ r₂ : ℕ} (p₁ : (Fin r₁ → B) →ₗ[B] GE) (hp₁ : Function.Surjective p₁)
    (p₂ : (Fin r₂ → B) →ₗ[B] GE) (hp₂ : Function.Surjective p₂)
    (P : (Fin (r₁ + r₂) → B) →ₗ[B] GE) (hP : ∀ (v : Fin r₁ → B) (w : Fin r₂ → B), P (Fin.append v w) = p₁ v + p₂ w) :
    ∃ c : ℕ, ∀ (n : ℕ)
      (ℓ₁ : (Fin r₁ → B) →ₗ[B] F (n + c)) (_ : ε (n + c) ∘ₗ ℓ₁ = ψE (n + c) ∘ₗ p₁)
      (ℓ₂ : (Fin r₂ → B) →ₗ[B] F (n + c)) (_ : ε (n + c) ∘ₗ ℓ₂ = ψE (n + c) ∘ₗ p₂)
      (δ₁ : ↥(LinearMap.ker p₁) →ₗ[B] GK) (_ : lam (n + c) ∘ₗ δ₁ = ℓ₁ ∘ₗ (LinearMap.ker p₁).subtype)
      (δ₂ : ↥(LinearMap.ker p₂) →ₗ[B] GK) (_ : lam (n + c) ∘ₗ δ₂ = ℓ₂ ∘ₗ (LinearMap.ker p₂).subtype),
      ∃ δ₁' δ₂' : ↥(LinearMap.ker P) →ₗ[B] GK,
        (∀ (s : ↥(LinearMap.ker p₁)) (hs : Fin.append (s : Fin r₁ → B) (0 : Fin r₂ → B) ∈ LinearMap.ker P),
          δ₁' ⟨Fin.append (s : Fin r₁ → B) 0, hs⟩ = δ₁ s) ∧
        (∀ (s : ↥(LinearMap.ker p₂)) (hs : Fin.append (0 : Fin r₁ → B) (s : Fin r₂ → B) ∈ LinearMap.ker P),
          δ₂' ⟨Fin.append 0 (s : Fin r₂ → B), hs⟩ = δ₂ s) ∧
        Submodule.Quotient.mk δ₁' - Submodule.Quotient.mk δ₂' ∈
          J ^ (n + 1) • (⊤ : Submodule B ((↥(LinearMap.ker P) →ₗ[B] GK) ⧸
            LinearMap.range (LinearMap.lcomp B GK (LinearMap.ker P).subtype)))
```

### `LinearMap.exists_forall_exists_mkQ_comp_eq_factor_comp`

`Thm_LinearMap_exists_forall_exists_mkQ_comp_eq_factor_comp` — Uniform Artin–Rees lifting of maps into N/IⁿN

```lean
theorem LinearMap.exists_forall_exists_mkQ_comp_eq_factor_comp
    {B : Type u} [CommRing B] [IsNoetherianRing B] (I : Ideal B)
    {M : Type v} [AddCommGroup M] [Module B M] [Module.Finite B M]
    {N : Type w} [AddCommGroup N] [Module B N] [Module.Finite B N] :
    ∃ c : ℕ, ∀ (n : ℕ) (f : M →ₗ[B] N ⧸ (I ^ (n + c) • (⊤ : Submodule B N))),
      ∃ g : M →ₗ[B] N,
        (I ^ n • (⊤ : Submodule B N)).mkQ ∘ₗ g =
          Submodule.factor (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_add_right n c))) ∘ₗ f
```

### `LinearMap.exists_forall_localizedModule_mk_eq_of_forall_exists_chart`

`Thm_LinearMap_exists_forall_localizedModule_mk_eq_of_forall_exists_chart` — Gluing a linear map from locally representable stalk maps

```lean
theorem LinearMap.exists_forall_localizedModule_mk_eq_of_forall_exists_chart
    {B : Type u} [CommRing B] {T T' : Type u} [AddCommGroup T] [Module B T] [AddCommGroup T'] [Module B T']
    (φ : ∀ x : PrimeSpectrum B,
      LocalizedModule x.asIdeal.primeCompl T' →ₗ[B] LocalizedModule x.asIdeal.primeCompl T)
    (hφ : ∀ x : PrimeSpectrum B, ∃ (f : B) (_ : f ∉ x.asIdeal)
        (Φ : T' →ₗ[B] LocalizedModule (Submonoid.powers f) T),
        ∀ (y : PrimeSpectrum B), f ∉ y.asIdeal → ∀ (a : T') (t : T) (n : ℕ),
          Φ a = LocalizedModule.mk t ⟨f ^ n, Submonoid.mem_powers_iff _ _ |>.mpr ⟨n, rfl⟩⟩ →
            ∀ s : y.asIdeal.primeCompl, (s : B) = f ^ n →
              φ y (LocalizedModule.mk a 1) = LocalizedModule.mk t s) :
    ∃ τ : T' →ₗ[B] T, ∀ (x : PrimeSpectrum B) (a : T'),
      LocalizedModule.mk (τ a) 1 = φ x (LocalizedModule.mk a 1)
```

### `LinearMap.exists_forall_mem_pow_smul_top_of_range_le_pow_smul`

`Thm_LinearMap_exists_forall_mem_pow_smul_top_of_range_le_pow_smul` — Artin–Rees for Hom modules

```lean
theorem LinearMap.exists_forall_mem_pow_smul_top_of_range_le_pow_smul
    {B : Type u} [CommRing B] [IsNoetherianRing B] (I : Ideal B)
    {M : Type v} [AddCommGroup M] [Module B M] [Module.Finite B M]
    {N : Type w} [AddCommGroup N] [Module B N] [Module.Finite B N] :
    ∃ c : ℕ, ∀ (n : ℕ) (g : M →ₗ[B] N),
      LinearMap.range g ≤ I ^ (n + c) • (⊤ : Submodule B N) →
      g ∈ I ^ n • (⊤ : Submodule B (M →ₗ[B] N))
```

### `LinearMap.exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq`

`Thm_LinearMap_exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq` — Defect of two compatible comparison maps is I-adically Cauchy

```lean
theorem LinearMap.exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq
    {B : Type u} [CommRing B] [IsNoetherianRing B] (I : Ideal B)
    {GK : Type v} [AddCommGroup GK] [Module B GK] [Module.Finite B GK]
    {GE : Type v} [AddCommGroup GE] [Module B GE] [Module.Finite B GE]
    {M : Type v} [AddCommGroup M] [Module B M]
    (ϑ : GK →ₗ[B] M) (θE : M →ₗ[B] GE) (hex : LinearMap.range ϑ = LinearMap.ker θE) (hθE : Function.Surjective θE)
    (F : ℕ → Type w) [∀ k, AddCommGroup (F k)] [∀ k, Module B (F k)]
    (φ : ∀ k, F (k + 1) →ₗ[B] F k) (hF : ∀ k, I ^ (k + 1) • (⊤ : Submodule B (F k)) = ⊥)
    (lam : ∀ k, GK →ₗ[B] F k) (hlamc : ∀ k, φ k ∘ₗ lam (k + 1) = lam k)
    (c : ℕ) (hlami : ∀ k, LinearMap.ker (lam (k + c)) ≤ I ^ (k + 1) • (⊤ : Submodule B GK))
    (E : ℕ → Type w) [∀ k, AddCommGroup (E k)] [∀ k, Module B (E k)]
    (ε : ∀ k, F k →ₗ[B] E k) (hlamr : ∀ k, LinearMap.range (lam k) = LinearMap.ker (ε k))
    (θ θ' : ∀ k, M →ₗ[B] F k)
    (hθc : ∀ k, φ k ∘ₗ θ (k + 1) = θ k) (hθ'c : ∀ k, φ k ∘ₗ θ' (k + 1) = θ' k)
    (hθϑ : ∀ k, θ k ∘ₗ ϑ = lam k) (hθ'ϑ : ∀ k, θ' k ∘ₗ ϑ = lam k)
    (hθε : ∀ k, ε k ∘ₗ θ k = ε k ∘ₗ θ' k) :
    ∃ g : ℕ → (GE →ₗ[B] GK),
      (∀ k, g (k + 1) - g k ∈ I ^ (k + 1) • (⊤ : Submodule B (GE →ₗ[B] GK))) ∧
      (∀ k, θ' k - θ k = lam k ∘ₗ g k ∘ₗ θE)
```

### `LinearMap.exists_forall_sub_mem_pow_smul_top_and_mkQ_comp_eq_of_compatible`

`Thm_LinearMap_exists_forall_sub_mem_pow_smul_top_and_mkQ_comp_eq_of_compatible` — Compatible maps into Artin–Rees quotients lift Cauchy-wise

```lean
theorem LinearMap.exists_forall_sub_mem_pow_smul_top_and_mkQ_comp_eq_of_compatible
    {B : Type u} [CommRing B] [IsNoetherianRing B] (I : Ideal B)
    {M : Type v} [AddCommGroup M] [Module B M] [Module.Finite B M]
    {N : Type w} [AddCommGroup N] [Module B N] [Module.Finite B N]
    (J : ℕ → Submodule B N) (hJ : ∀ k, J (k + 1) ≤ J k)
    (hIJ : ∀ k, I ^ (k + 1) • (⊤ : Submodule B N) ≤ J k)
    (c : ℕ) (hJI : ∀ k, J (k + c) ≤ I ^ (k + 1) • (⊤ : Submodule B N))
    (f : ∀ k, M →ₗ[B] N ⧸ J k)
    (hf : ∀ k, Submodule.factor (hJ k) ∘ₗ f (k + 1) = f k) :
    ∃ g : ℕ → (M →ₗ[B] N),
      (∀ k, g (k + 1) - g k ∈ I ^ (k + 1) • (⊤ : Submodule B (M →ₗ[B] N))) ∧
      (∀ k, (J k).mkQ ∘ₗ g k = f k)
```

### `LinearMap.exists_injective_comp_eq_smul_of_forall_exists_smul_mem_range`

`Thm_LinearMap_exists_injective_comp_eq_smul_of_forall_exists_smul_mem_range` — Clearing denominators: ι ∘ j = a J with j injective

```lean
theorem LinearMap.exists_injective_comp_eq_smul_of_forall_exists_smul_mem_range
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪]
    {R : Type} [CommRing R] [Algebra 𝒪 R]
    {V : Type} [AddCommGroup V] [Module R V] [Module 𝒪 V] [IsScalarTower 𝒪 R V] [Module.Finite 𝒪 V]
    {Y : Type} [AddCommGroup Y] [Module R Y] [Module 𝒪 Y] [IsScalarTower 𝒪 R Y]
    {M : Type} [AddCommGroup M] [Module R M] [Module 𝒪 M] [IsScalarTower 𝒪 R M]
    (htf : ∀ (a : 𝒪) (m : M), a ≠ 0 → a • m = 0 → m = 0)
    (ι : Y →ₗ[R] M) (hι : Function.Injective ι)
    (hloc : ∀ m : M, ∃ a : 𝒪, a ≠ 0 ∧ a • m ∈ LinearMap.range ι)
    (J : V →ₗ[R] M) (hJ : Function.Injective J) :
    ∃ (a : 𝒪) (_ : a ≠ 0) (j : V →ₗ[R] Y), Function.Injective j ∧ ∀ v : V, ι (j v) = a • J v
```

### `LinearMap.exists_injective_range_eq_ker_of_isTorsion`

`Thm_LinearMap_exists_injective_range_eq_ker_of_isTorsion` — Kernel of a map A^r → torsion module is free of rank r

```lean
theorem LinearMap.exists_injective_range_eq_ker_of_isTorsion
    {A : Type u} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    {D : Type v} [AddCommGroup D] [Module A D] (hD : Module.IsTorsion A D)
    {r : ℕ} (π : (Fin r → A) →ₗ[A] D) :
    ∃ φ : (Fin r → A) →ₗ[A] (Fin r → A),
      Function.Injective φ ∧ LinearMap.range φ = LinearMap.ker π
```

### `LinearMap.exists_int_forall_apply_ne`

`Thm_LinearMap_exists_int_forall_apply_ne` — Integer points avoiding finitely many affine hyperplanes

```lean
theorem LinearMap.exists_int_forall_apply_ne {K : Type*} [Field K] [CharZero K] {r : ℕ} {ι : Type*}
    (S : Finset ι) (f : ι → (Fin r → K) →ₗ[K] K) (a : ι → K) (hf : ∀ j ∈ S, f j ≠ 0) :
    ∃ c : Fin r → ℤ, ∀ j ∈ S, f j (fun i => (c i : K)) ≠ a j
```

### `LinearMap.exists_int_forall_apply_notMem`

`Thm_LinearMap_exists_int_forall_apply_notMem` — Integer points avoiding finitely many linear conditions

```lean
theorem LinearMap.exists_int_forall_apply_notMem
    {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} {ι : Type*}
    (S : Finset ι) (f : ι → (Fin r → K) →ₗ[K] V) (W : ι → Submodule K V)
    (h : ∀ t ∈ S, ∃ c : Fin r → K, f t c ∉ W t) :
    ∃ c : Fin r → ℤ, ∀ t ∈ S, f t (fun i => (c i : K)) ∉ W t
```

### `LinearMap.exists_isBaseChange_extQuot_of_flat_of_surjective`

`Thm_LinearMap_exists_isBaseChange_extQuot_of_flat_of_surjective` — Flat base change of the Ext¹-quotient of a presentation

```lean
theorem LinearMap.exists_isBaseChange_extQuot_of_flat_of_surjective
    {B : Type u} [CommRing B] [IsNoetherianRing B] {B' : Type u} [CommRing B'] [Algebra B B'] [Module.Flat B B']
    {M : Type v} [AddCommGroup M] [Module B M] {N : Type v} [AddCommGroup N] [Module B N]
    {M' : Type v} [AddCommGroup M'] [Module B M'] [Module B' M'] [IsScalarTower B B' M']
    {N' : Type v} [AddCommGroup N'] [Module B N'] [Module B' N'] [IsScalarTower B B' N']
    (μ : M →ₗ[B] M') (hμ : IsBaseChange B' μ) (ν : N →ₗ[B] N') (hν : IsBaseChange B' ν)
    {r : ℕ} (p : (Fin r → B) →ₗ[B] M) (hp : Function.Surjective p)
    (p' : (Fin r → B') →ₗ[B'] M') (hp' : ∀ v : Fin r → B, p' (fun i => algebraMap B B' (v i)) = μ (p v)) :
    Function.Surjective p' ∧
    ∃ (g : ↥(LinearMap.ker p) →ₗ[B] ↥(LinearMap.ker p'))
      (T : ((↥(LinearMap.ker p) →ₗ[B] N) ⧸ LinearMap.range (LinearMap.lcomp B N (LinearMap.ker p).subtype)) →ₗ[B]
           ((↥(LinearMap.ker p') →ₗ[B'] N') ⧸ LinearMap.range (LinearMap.lcomp B' N' (LinearMap.ker p').subtype))),
      (∀ (s : ↥(LinearMap.ker p)) (i : Fin r), ((g s : ↥(LinearMap.ker p')) : Fin r → B') i = algebraMap B B' ((s : Fin r → B) i)) ∧
      IsBaseChange B' T ∧
      (∀ δ : ↥(LinearMap.ker p) →ₗ[B] N, ∃ δ' : ↥(LinearMap.ker p') →ₗ[B'] N', ∀ s : ↥(LinearMap.ker p), δ' (g s) = ν (δ s)) ∧
      (∀ (δ : ↥(LinearMap.ker p) →ₗ[B] N) (δ' : ↥(LinearMap.ker p') →ₗ[B'] N'),
        (∀ s : ↥(LinearMap.ker p), δ' (g s) = ν (δ s)) →
        T (Submodule.Quotient.mk δ) = Submodule.Quotient.mk δ')
```

### `LinearMap.exists_isBaseChange_ker_span_range_eq_top_of_flat`

`Thm_LinearMap_exists_isBaseChange_ker_span_range_eq_top_of_flat` — Flat base change of the relation module of a finite free presentation

```lean
theorem LinearMap.exists_isBaseChange_ker_span_range_eq_top_of_flat
    {B : Type u} [CommRing B] {B' : Type u} [CommRing B'] [Algebra B B'] [Module.Flat B B']
    {M : Type v} [AddCommGroup M] [Module B M]
    {M' : Type v} [AddCommGroup M'] [Module B M'] [Module B' M'] [IsScalarTower B B' M']
    (μ : M →ₗ[B] M') (hμ : IsBaseChange B' μ)
    {r : ℕ} (p : (Fin r → B) →ₗ[B] M)
    (p' : (Fin r → B') →ₗ[B'] M') (hp' : ∀ v : Fin r → B, p' (fun i => algebraMap B B' (v i)) = μ (p v)) :
    ∃ g : ↥(LinearMap.ker p) →ₗ[B] ↥(LinearMap.ker p'),
      (∀ (s : ↥(LinearMap.ker p)) (i : Fin r), ((g s : ↥(LinearMap.ker p')) : Fin r → B') i = algebraMap B B' ((s : Fin r → B) i)) ∧
      IsBaseChange B' g ∧
      Submodule.span B' (Set.range g) = ⊤
```

### `LinearMap.exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact`

`Thm_LinearMap_exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact` — Surjection with acyclic kernel induces isomorphisms on cohomology

```lean
theorem LinearMap.exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact
    {R : Type u} [CommRing R] {C D : ℕ → Type v}
    [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)] [∀ n, AddCommGroup (D n)] [∀ n, Module R (D n)]
    (dC : ∀ n, C n →ₗ[R] C (n + 1)) (dD : ∀ n, D n →ₗ[R] D (n + 1)) (f : ∀ n, C n →ₗ[R] D n)
    (hf : ∀ (n : ℕ) (x : C n), f (n + 1) (dC n x) = dD n (f n x))
    (hdC : ∀ (n : ℕ) (x : C n), dC (n + 1) (dC n x) = 0)
    (hsurj : ∀ n, Function.Surjective (f n))
    (hex0 : ∀ x : C 0, f 0 x = 0 → dC 0 x = 0 → x = 0)
    (hexS : ∀ (n : ℕ) (x : C (n + 1)), f (n + 1) x = 0 → dC (n + 1) x = 0 →
      ∃ y : C n, f n y = 0 ∧ dC n y = x) :
    (∃ e : LinearMap.ker (dC 0) ≃ₗ[R] LinearMap.ker (dD 0), ∀ x : LinearMap.ker (dC 0), (e x : D 0) = f 0 x) ∧
    ∀ n : ℕ, ∃ e : (LinearMap.ker (dC (n + 1)) ⧸
        (LinearMap.range (dC n)).comap (LinearMap.ker (dC (n + 1))).subtype) ≃ₗ[R]
      (LinearMap.ker (dD (n + 1)) ⧸ (LinearMap.range (dD n)).comap (LinearMap.ker (dD (n + 1))).subtype),
      ∀ (x : LinearMap.ker (dC (n + 1))) (y : LinearMap.ker (dD (n + 1))), (y : D (n + 1)) = f (n + 1) x →
        e (Submodule.Quotient.mk x) = Submodule.Quotient.mk y
```

### `LinearMap.exists_lifts_comp_eq_forall_comp_eq_comp_subtype_sub_mem_pow_smul_top`

`Thm_LinearMap_exists_lifts_comp_eq_forall_comp_eq_comp_subtype_sub_mem_pow_smul_top` — Compatible lifts of a presentation along a J-adic tower

```lean
theorem LinearMap.exists_lifts_comp_eq_forall_comp_eq_comp_subtype_sub_mem_pow_smul_top
    {B : Type u} [CommRing B] [IsNoetherianRing B] (J : Ideal B)
    {GE GK : Type v} [AddCommGroup GE] [Module B GE] [AddCommGroup GK] [Module B GK] [Module.Finite B GK]
    {r : ℕ} (p : (Fin r → B) →ₗ[B] GE)
    (F E : ℕ → Type w) [∀ k, AddCommGroup (F k)] [∀ k, Module B (F k)] [∀ k, AddCommGroup (E k)] [∀ k, Module B (E k)]
    (φ : ∀ k, F (k + 1) →ₗ[B] F k) (hφs : ∀ k, Function.Surjective (φ k))
    (hφk : ∀ k, LinearMap.ker (φ k) = J ^ (k + 1) • (⊤ : Submodule B (F (k + 1))))
    (τ : ∀ k, E (k + 1) →ₗ[B] E k)
    (hτk : ∀ k, LinearMap.ker (τ k) = J ^ (k + 1) • (⊤ : Submodule B (E (k + 1))))
    (ε : ∀ k, F k →ₗ[B] E k) (hεs : ∀ k, Function.Surjective (ε k))
    (hεc : ∀ k, τ k ∘ₗ ε (k + 1) = ε k ∘ₗ φ k)
    (ψE : ∀ k, GE →ₗ[B] E k) (hψEc : ∀ k, τ k ∘ₗ ψE (k + 1) = ψE k)
    (lam : ∀ k, GK →ₗ[B] F k) (hlamc : ∀ k, φ k ∘ₗ lam (k + 1) = lam k)
    (hlamr : ∀ k, LinearMap.range (lam k) = LinearMap.ker (ε k))
    (hlami : ∃ c : ℕ, ∀ k : ℕ, LinearMap.ker (lam (k + c)) ≤ J ^ (k + 1) • (⊤ : Submodule B GK)) :
    ∃ (ℓ : ∀ n : ℕ, (Fin r → B) →ₗ[B] F n) (δs : ∀ n : ℕ, ↥(LinearMap.ker p) →ₗ[B] GK),
      (∀ n, ε n ∘ₗ ℓ n = ψE n ∘ₗ p) ∧
      (∀ n, φ n ∘ₗ ℓ (n + 1) = ℓ n) ∧
      (∀ n, lam n ∘ₗ δs n = ℓ n ∘ₗ (LinearMap.ker p).subtype) ∧
      (∀ n, δs (n + 1) - δs n ∈ J ^ (n + 1) • (⊤ : Submodule B (↥(LinearMap.ker p) →ₗ[B] GK)))
```

### `LinearMap.exists_linearEquiv_extQuot_forall_comp_eq_of_surjective`

`Thm_LinearMap_exists_linearEquiv_extQuot_forall_comp_eq_of_surjective` — Presentation-independence of the Ext¹-quotient

```lean
theorem LinearMap.exists_linearEquiv_extQuot_forall_comp_eq_of_surjective
    {B : Type u} [CommRing B] {M N : Type v} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    {r₁ r₂ : ℕ} (p₁ : (Fin r₁ → B) →ₗ[B] M) (p₂ : (Fin r₂ → B) →ₗ[B] M)
    (hp₁ : Function.Surjective p₁) (hp₂ : Function.Surjective p₂) :
    ∃ Φ : ((↥(LinearMap.ker p₂) →ₗ[B] N) ⧸ LinearMap.range (LinearMap.lcomp B N (LinearMap.ker p₂).subtype)) ≃ₗ[B]
        ((↥(LinearMap.ker p₁) →ₗ[B] N) ⧸ LinearMap.range (LinearMap.lcomp B N (LinearMap.ker p₁).subtype)),
      ∀ (g : (Fin r₁ → B) →ₗ[B] (Fin r₂ → B)), p₂ ∘ₗ g = p₁ →
        ∀ (g' : ↥(LinearMap.ker p₁) →ₗ[B] ↥(LinearMap.ker p₂)),
          (∀ s : ↥(LinearMap.ker p₁), ((g' s : ↥(LinearMap.ker p₂)) : Fin r₂ → B) = g (s : Fin r₁ → B)) →
          ∀ δ : ↥(LinearMap.ker p₂) →ₗ[B] N,
            Φ (Submodule.Quotient.mk δ) = Submodule.Quotient.mk (δ ∘ₗ g')
```

### `LinearMap.exists_linearEquiv_quotient_smul_top_and_finrank_eq_of_injective_of_smul_top_eq_top`

`Thm_LinearMap_exists_linearEquiv_quotient_smul_top_and_finrank_eq_of_injective_of_smul_top_eq_top` — Nakayama: injective map with 𝔪-divisible cokernel is an isomorphism on coinvariants

```lean
theorem LinearMap.exists_linearEquiv_quotient_smul_top_and_finrank_eq_of_injective_of_smul_top_eq_top
    {R : Type*} [CommRing R] (𝔪 : Ideal R)
    {Y L : Type*} [AddCommGroup Y] [Module R Y] [AddCommGroup L] [Module R L]
    (f : Y →ₗ[R] L) (hf : Function.Injective f)
    [Module.Finite R (L ⧸ LinearMap.range f)]
    (hC : (𝔪 • ⊤ : Submodule R (L ⧸ LinearMap.range f)) = ⊤) :
    (∃ e : (Y ⧸ (𝔪 • ⊤ : Submodule R Y)) ≃ₗ[R] (L ⧸ (𝔪 • ⊤ : Submodule R L)),
        ∀ y : Y, e (Submodule.Quotient.mk y) = Submodule.Quotient.mk (f y)) ∧
    Module.finrank (R ⧸ 𝔪) (Y ⧸ (𝔪 • ⊤ : Submodule R Y)) = Module.finrank (R ⧸ 𝔪) (L ⧸ (𝔪 • ⊤ : Submodule R L))
```

### `LinearMap.exists_span_eq_top_forall_exists_bijective_and_apply_eq_of_comp_eq_smul_comp`

`Thm_LinearMap_exists_span_eq_top_forall_exists_bijective_and_apply_eq_of_comp_eq_smul_comp` — Stone–von Neumann–Mackey over a ring, Zariski-locally

```lean
theorem LinearMap.exists_span_eq_top_forall_exists_bijective_and_apply_eq_of_comp_eq_smul_comp
    {R : Type u} [CommRing R]
    {H : Type v} [AddCommGroup H] [Fintype H]
    {H' : Type w} [AddCommGroup H'] [Fintype H']
    (hcard : Fintype.card H' = Fintype.card H) (hd : IsUnit ((Fintype.card H : ℕ) : R))
    (e : H → H' → Rˣ)
    (he₁ : ∀ (h₁ h₂ : H) (χ : H'), e (h₁ + h₂) χ = e h₁ χ * e h₂ χ)
    (he₂ : ∀ (h : H) (χ₁ χ₂ : H'), e h (χ₁ + χ₂) = e h χ₁ * e h χ₂)
    (hsep : ∀ h : H, h ≠ 0 → ∃ χ : H', IsUnit ((e h χ : R) - 1))
    (hsep' : ∀ χ : H', χ ≠ 0 → ∃ h : H, IsUnit ((e h χ : R) - 1))
    {M : Type u} [AddCommGroup M] [Module R M]
    {ι : Type u} [Fintype ι] (b : Module.Basis ι R M) (hrank : Fintype.card ι = Fintype.card H)
    (U : H → M →ₗ[R] M) (hU0 : U 0 = LinearMap.id) (hU : ∀ h₁ h₂ : H, U (h₁ + h₂) = U h₁ ∘ₗ U h₂)
    (V : H' → M →ₗ[R] M) (hV0 : V 0 = LinearMap.id) (hV : ∀ χ₁ χ₂ : H', V (χ₁ + χ₂) = V χ₁ ∘ₗ V χ₂)
    (hHeis : ∀ (h : H) (χ : H'), V χ ∘ₗ U h = (e h χ : R) • (U h ∘ₗ V χ)) :
    ∃ (n : ℕ) (r : Fin n → R), Ideal.span (Set.range r) = ⊤ ∧
      ∀ (j : Fin n) (Rj : Type u) [CommRing Rj] [Algebra R Rj] [IsLocalization.Away (r j) Rj]
        (Mj : Type u) [AddCommGroup Mj] [Module R Mj] [Module Rj Mj] [IsScalarTower R Rj Mj]
        (ℓ : M →ₗ[R] Mj) [IsLocalizedModule (Submonoid.powers (r j)) ℓ]
        (U' : H → Mj →ₗ[Rj] Mj) (_hU' : ∀ (h : H) (m : M), U' h (ℓ m) = ℓ (U h m))
        (V' : H' → Mj →ₗ[Rj] Mj) (_hV' : ∀ (χ : H') (m : M), V' χ (ℓ m) = ℓ (V χ m)),
        ∃ σ : H → Mj,
          Function.Bijective (fun c : H → Rj => ∑ h, c h • σ h) ∧
          (∀ k h : H, U' k (σ h) = σ (k + h)) ∧
          (∀ (χ : H') (h : H), V' χ (σ h) = algebraMap R Rj (e h χ : R) • σ h)
```

### `LinearMap.exists_submodule_mem_iff_forall_apply_eq_zero_of_forall_comp_eq_of_normal`

`Thm_LinearMap_exists_submodule_mem_iff_forall_apply_eq_zero_of_forall_comp_eq_of_normal` — Common kernel of translates of an I-invariant linear form

```lean
theorem LinearMap.exists_submodule_mem_iff_forall_apply_eq_zero_of_forall_comp_eq_of_normal
    {R : Type*} [CommRing R] [IsDomain R]
    {Γ : Type*} [Group Γ] {T : Type*} [AddCommGroup T] [Module R T]
    (ρ : Γ →* Module.End R T) (I : Subgroup Γ) (hI : I.Normal)
    (f : T →ₗ[R] R) (hf : ∀ τ ∈ I, f ∘ₗ ρ τ = f) :
    ∃ M : Submodule R T,
      (∀ x : T, x ∈ M ↔ ∀ γ : Γ, f (ρ γ x) = 0) ∧
      (∀ (γ : Γ) (x : T), x ∈ M → ρ γ x ∈ M) ∧
      (∀ τ ∈ I, ∀ x : T, ρ τ x - x ∈ M) ∧
      (∀ (r : R) (x : T), r ≠ 0 → r • x ∈ M → x ∈ M) ∧
      (∀ x ∈ M, f x = 0)
```

### `LinearMap.finiteDimensional_ker_and_quotient_range_of_exact_of_finiteDimensional`

`Thm_LinearMap_finiteDimensional_ker_and_quotient_range_of_exact_of_finiteDimensional` — Finiteness of ker d₁ and coker d₁ in a ladder of two-term complexes

```lean
theorem LinearMap.finiteDimensional_ker_and_quotient_range_of_exact_of_finiteDimensional
    {k : Type u} [Field k]
    {A₁ A₂ A₃ B₁ B₂ B₃ : Type v}
    [AddCommGroup A₁] [Module k A₁] [AddCommGroup A₂] [Module k A₂] [AddCommGroup A₃] [Module k A₃]
    [AddCommGroup B₁] [Module k B₁] [AddCommGroup B₂] [Module k B₂] [AddCommGroup B₃] [Module k B₃]
    (d₁ : A₁ →ₗ[k] B₁) (d₂ : A₂ →ₗ[k] B₂) (d₃ : A₃ →ₗ[k] B₃)
    (f₁ : A₁ →ₗ[k] A₂) (f₂ : A₂ →ₗ[k] A₃) (g₁ : B₁ →ₗ[k] B₂) (g₂ : B₂ →ₗ[k] B₃)
    (hf₁ : Function.Injective f₁) (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg₁ : Function.Injective g₁) (hg : Function.Exact g₁ g₂) (hg₂ : Function.Surjective g₂)
    (h₁ : g₁ ∘ₗ d₁ = d₂ ∘ₗ f₁) (h₂ : g₂ ∘ₗ d₂ = d₃ ∘ₗ f₂)
    [FiniteDimensional k (LinearMap.ker d₂)] [FiniteDimensional k (B₂ ⧸ LinearMap.range d₂)]
    [FiniteDimensional k (LinearMap.ker d₃)] :
    FiniteDimensional k (LinearMap.ker d₁) ∧ FiniteDimensional k (B₁ ⧸ LinearMap.range d₁)
```

### `LinearMap.finite_and_sum_finrank_eq_of_exact_of_exact_of_exact`

`Thm_LinearMap_finite_and_sum_finrank_eq_of_exact_of_exact_of_exact` — Additivity of Euler characteristic along a long exact sequence

```lean
theorem LinearMap.finite_and_sum_finrank_eq_of_exact_of_exact_of_exact
    {k : Type u} [Field k] (A B Q : ℕ → Type u)
    [∀ n, AddCommGroup (A n)] [∀ n, Module k (A n)] [∀ n, AddCommGroup (B n)] [∀ n, Module k (B n)]
    [∀ n, AddCommGroup (Q n)] [∀ n, Module k (Q n)]
    (f : ∀ n, A n →ₗ[k] B n) (g : ∀ n, B n →ₗ[k] Q n) (δ : ∀ n, Q n →ₗ[k] A (n + 1))
    (hfg : ∀ n, LinearMap.range (f n) = LinearMap.ker (g n))
    (hgδ : ∀ n, LinearMap.range (g n) = LinearMap.ker (δ n))
    (hδf : ∀ n, LinearMap.range (δ n) = LinearMap.ker (f (n + 1)))
    (hA : ∀ n, Module.Finite k (A n)) (hQ : ∀ n, Module.Finite k (Q n))
    (M : ℕ) (hf0 : Function.Injective (f 0)) (hfM : Function.Injective (f M)) :
    (∀ n, Module.Finite k (B n)) ∧
      ∑ n ∈ Finset.range M, (-1 : ℤ) ^ n * (Module.finrank k (B n) : ℤ) =
        ∑ n ∈ Finset.range M, (-1 : ℤ) ^ n * (Module.finrank k (A n) : ℤ) +
          ∑ n ∈ Finset.range M, (-1 : ℤ) ^ n * (Module.finrank k (Q n) : ℤ)
```

### `LinearMap.finrank_even_eq_finrank_odd_of_nineTerm_exact`

`Thm_LinearMap_finrank_even_eq_finrank_odd_of_nineTerm_exact` — Euler characteristic of a nine-term exact sequence of k-vector spaces

```lean
theorem LinearMap.finrank_even_eq_finrank_odd_of_nineTerm_exact {k : Type u} [Field k]
    {V₀ V₁ V₂ V₃ V₄ V₅ V₆ V₇ V₈ : Type u}
    [AddCommGroup V₀] [Module k V₀] [AddCommGroup V₁] [Module k V₁]
    [AddCommGroup V₂] [Module k V₂] [AddCommGroup V₃] [Module k V₃]
    [AddCommGroup V₄] [Module k V₄] [AddCommGroup V₅] [Module k V₅]
    [AddCommGroup V₆] [Module k V₆] [AddCommGroup V₇] [Module k V₇]
    [AddCommGroup V₈] [Module k V₈]
    [FiniteDimensional k V₀] [FiniteDimensional k V₁] [FiniteDimensional k V₂]
    [FiniteDimensional k V₃] [FiniteDimensional k V₄] [FiniteDimensional k V₅]
    [FiniteDimensional k V₆] [FiniteDimensional k V₇]
    (d₀ : V₀ →ₗ[k] V₁) (d₁ : V₁ →ₗ[k] V₂) (d₂ : V₂ →ₗ[k] V₃) (d₃ : V₃ →ₗ[k] V₄)
    (d₄ : V₄ →ₗ[k] V₅) (d₅ : V₅ →ₗ[k] V₆) (d₆ : V₆ →ₗ[k] V₇) (d₇ : V₇ →ₗ[k] V₈)
    (e₀ : LinearMap.ker d₀ = ⊥)
    (e₁ : LinearMap.range d₀ = LinearMap.ker d₁) (e₂ : LinearMap.range d₁ = LinearMap.ker d₂)
    (e₃ : LinearMap.range d₂ = LinearMap.ker d₃) (e₄ : LinearMap.range d₃ = LinearMap.ker d₄)
    (e₅ : LinearMap.range d₄ = LinearMap.ker d₅) (e₆ : LinearMap.range d₅ = LinearMap.ker d₆)
    (e₇ : LinearMap.range d₆ = LinearMap.ker d₇) (e₈ : LinearMap.range d₇ = ⊤) :
    Module.finrank k V₀ + Module.finrank k V₂ + Module.finrank k V₄ + Module.finrank k V₆ + Module.finrank k V₈
      = Module.finrank k V₁ + Module.finrank k V₃ + Module.finrank k V₅ + Module.finrank k V₇
```

### `LinearMap.finrank_iInf_eigenspace_le_one_of_coeff_hecke_law`

`Thm_LinearMap_finrank_iInf_eigenspace_le_one_of_coeff_hecke_law` — At most one dimension for a simultaneous Hecke eigenspace

```lean
theorem LinearMap.finrank_iInf_eigenspace_le_one_of_coeff_hecke_law
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (a : ℕ → V →ₗ[K] K)
    (hinj : ∀ v : V, (∀ n : ℕ, 1 ≤ n → a n v = 0) → v = 0)
    (T : ℕ → V →ₗ[K] V) (c : ℕ → K)
    (hlaw : ∀ ℓ : ℕ, ℓ.Prime → ∀ n : ℕ, 1 ≤ n → ∀ v : V,
      a n (T ℓ v) = a (n * ℓ) v + (if ℓ ∣ n then c ℓ * a (n / ℓ) v else 0))
    (μ : ℕ → K) :
    (∀ v ∈ ⨅ (ℓ : ℕ) (_ : ℓ.Prime), Module.End.eigenspace (T ℓ) (μ ℓ), a 1 v = 0 → v = 0) ∧
    Module.finrank K ↥(⨅ (ℓ : ℕ) (_ : ℓ.Prime), Module.End.eigenspace (T ℓ) (μ ℓ)) ≤ 1
```

### `LinearMap.finrank_ker_baseChange_le_padicValInt_det`

`Thm_LinearMap_finrank_ker_baseChange_le_padicValInt_det` — Kernel of a base-changed integral endomorphism and vₚ(det)

```lean
theorem LinearMap.finrank_ker_baseChange_le_padicValInt_det
    {L : Type} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (A : L →ₗ[ℤ] L) (hA : LinearMap.det A ≠ 0) (p : ℕ) [Fact p.Prime]
    (F : Type) [Field F] [CharP F p] :
    Module.finrank F ↥(LinearMap.ker (A.baseChange F)) ≤ padicValInt p (LinearMap.det A)
```

### `LinearMap.finrank_ker_dualMap_eq_finrank_ker`

`Thm_LinearMap_finrank_ker_dualMap_eq_finrank_ker` — Kernel of the dual map has the same dimension

```lean
theorem LinearMap.finrank_ker_dualMap_eq_finrank_ker
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : V →ₗ[K] V) :
    finrank K (LinearMap.ker f.dualMap) = finrank K (LinearMap.ker f)
```

### `LinearMap.finrank_ker_eq_and_finrank_add_finrank_eq_of_quasiIso`

`Thm_LinearMap_finrank_ker_eq_and_finrank_add_finrank_eq_of_quasiIso` — Quasi-isomorphism transfers cohomology dimensions to a finite complex

```lean
theorem LinearMap.finrank_ker_eq_and_finrank_add_finrank_eq_of_quasiIso
    {A : Type u} [Field A]
    (K : ℕ → Type v) [∀ i, AddCommGroup (K i)] [∀ i, Module A (K i)] [∀ i, Module.Finite A (K i)]
    (δ : ∀ i, K i →ₗ[A] K (i + 1))
    (C : ℕ → Type v) [∀ i, AddCommGroup (C i)] [∀ i, Module A (C i)] (d : ∀ i, C i →ₗ[A] C (i + 1))
    (φ : ∀ i, K i →ₗ[A] C i) (hφ : ∀ i, d i ∘ₗ φ i = φ (i + 1) ∘ₗ δ i)
    (h0inj : ∀ x : K 0, δ 0 x = 0 → φ 0 x = 0 → x = 0)
    (h0surj : ∀ y : C 0, d 0 y = 0 → ∃ x : K 0, δ 0 x = 0 ∧ φ 0 x = y)
    (hinj : ∀ (i : ℕ) (x : K (i + 1)), δ (i + 1) x = 0 → φ (i + 1) x ∈ LinearMap.range (d i) →
      x ∈ LinearMap.range (δ i))
    (hsurj : ∀ (i : ℕ) (y : C (i + 1)), d (i + 1) y = 0 →
      ∃ x : K (i + 1), δ (i + 1) x = 0 ∧ φ (i + 1) x - y ∈ LinearMap.range (d i)) :
    Module.finrank A ↥(LinearMap.ker (d 0)) = Module.finrank A ↥(LinearMap.ker (δ 0)) ∧
      ∀ (i : ℕ) (H : Type v) [AddCommGroup H] [Module A H] (ψ : ↥(LinearMap.ker (d (i + 1))) →ₗ[A] H),
        Function.Surjective ψ →
        LinearMap.ker ψ = (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype →
        Module.finrank A H +
            Module.finrank A ↥((LinearMap.range (δ i)).comap (LinearMap.ker (δ (i + 1))).subtype) =
          Module.finrank A ↥(LinearMap.ker (δ (i + 1)))
```

### `LinearMap.finrank_ker_sub_finrank_quotient_range_eq_add_of_exact`

`Thm_LinearMap_finrank_ker_sub_finrank_quotient_range_eq_add_of_exact` — Additivity of dimker-dimcoker in short exact sequences

```lean
theorem LinearMap.finrank_ker_sub_finrank_quotient_range_eq_add_of_exact
    {k : Type u} [Field k]
    {A₁ A₂ A₃ B₁ B₂ B₃ : Type v}
    [AddCommGroup A₁] [Module k A₁] [AddCommGroup A₂] [Module k A₂] [AddCommGroup A₃] [Module k A₃]
    [AddCommGroup B₁] [Module k B₁] [AddCommGroup B₂] [Module k B₂] [AddCommGroup B₃] [Module k B₃]
    (d₁ : A₁ →ₗ[k] B₁) (d₂ : A₂ →ₗ[k] B₂) (d₃ : A₃ →ₗ[k] B₃)
    (f₁ : A₁ →ₗ[k] A₂) (f₂ : A₂ →ₗ[k] A₃) (g₁ : B₁ →ₗ[k] B₂) (g₂ : B₂ →ₗ[k] B₃)
    (hf₁ : Function.Injective f₁) (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg₁ : Function.Injective g₁) (hg : Function.Exact g₁ g₂) (hg₂ : Function.Surjective g₂)
    (h₁ : g₁ ∘ₗ d₁ = d₂ ∘ₗ f₁) (h₂ : g₂ ∘ₗ d₂ = d₃ ∘ₗ f₂)
    [FiniteDimensional k (LinearMap.ker d₁)] [FiniteDimensional k (B₁ ⧸ LinearMap.range d₁)]
    [FiniteDimensional k (LinearMap.ker d₃)] [FiniteDimensional k (B₃ ⧸ LinearMap.range d₃)] :
    FiniteDimensional k (LinearMap.ker d₂) ∧ FiniteDimensional k (B₂ ⧸ LinearMap.range d₂) ∧
    (Module.finrank k (LinearMap.ker d₂) : ℤ) - Module.finrank k (B₂ ⧸ LinearMap.range d₂)
      = ((Module.finrank k (LinearMap.ker d₁) : ℤ) - Module.finrank k (B₁ ⧸ LinearMap.range d₁))
        + ((Module.finrank k (LinearMap.ker d₃) : ℤ) - Module.finrank k (B₃ ⧸ LinearMap.range d₃))
```

### `LinearMap.forall_smul_eq_zero_and_forall_exists_eq_smul_of_ker_of_equiv_baseChange_of_flat`

`Thm_LinearMap_forall_smul_eq_zero_and_forall_exists_eq_smul_of_ker_of_equiv_baseChange_of_flat` — Flat base change of torsion bounds for a two-term complex

```lean
theorem LinearMap.forall_smul_eq_zero_and_forall_exists_eq_smul_of_ker_of_equiv_baseChange_of_flat
    {R₀ : Type u} [CommRing R₀] {R : Type v} [CommRing R] [Algebra R₀ R] [Module.Flat R₀ R]
    {L₀ : Type w} [AddCommGroup L₀] [Module R₀ L₀] {C₀ : Type w} [AddCommGroup C₀] [Module R₀ C₀]
    {D₀ : Type w} [AddCommGroup D₀] [Module R₀ D₀]
    (u₀ : L₀ →ₗ[R₀] C₀) (d₀ : C₀ →ₗ[R₀] D₀) (hdu₀ : ∀ x : L₀, d₀ (u₀ x) = 0) (J : Ideal R₀)
    (hk : ∀ x : L₀, u₀ x = 0 → ∀ a ∈ J, a • x = 0)
    (hc : ∀ y : C₀, d₀ y = 0 → ∀ a ∈ J, ∃ x : L₀, u₀ x = a • y)
    {L : Type w'} [AddCommGroup L] [Module R L] {C : Type w'} [AddCommGroup C] [Module R C]
    {D : Type w'} [AddCommGroup D] [Module R D]
    (u : L →ₗ[R] C) (d : C →ₗ[R] D)
    (eL : R ⊗[R₀] L₀ ≃ₗ[R] L) (eC : R ⊗[R₀] C₀ ≃ₗ[R] C) (eD : R ⊗[R₀] D₀ ≃ₗ[R] D)
    (hu : ∀ x : L₀, u (eL ((1 : R) ⊗ₜ x)) = eC ((1 : R) ⊗ₜ u₀ x))
    (hd : ∀ y : C₀, d (eC ((1 : R) ⊗ₜ y)) = eD ((1 : R) ⊗ₜ d₀ y)) :
    (∀ x : L, u x = 0 → ∀ a ∈ J.map (algebraMap R₀ R), a • x = 0) ∧
    (∀ y : C, d y = 0 → ∀ a ∈ J.map (algebraMap R₀ R), ∃ x : L, u x = a • y)
```

### `LinearMap.forall_smul_eq_zero_of_baseChange_eq_zero_and_forall_exists_baseChange_eq_smul_of_flat`

`Thm_LinearMap_forall_smul_eq_zero_of_baseChange_eq_zero_and_forall_exists_baseChange_eq_smul_of_flat` — Kernel and cokernel torsion bounds under flat base change

```lean
theorem LinearMap.forall_smul_eq_zero_of_baseChange_eq_zero_and_forall_exists_baseChange_eq_smul_of_flat
    {R₀ : Type u} [CommRing R₀] {R : Type v} [CommRing R] [Algebra R₀ R] [Module.Flat R₀ R]
    {M : Type w} [AddCommGroup M] [Module R₀ M] {N : Type w'} [AddCommGroup N] [Module R₀ N]
    (u : M →ₗ[R₀] N) (J : Ideal R₀)
    (hk : ∀ x : M, u x = 0 → ∀ a ∈ J, a • x = 0)
    (hc : ∀ (y : N), ∀ a ∈ J, ∃ x : M, u x = a • y) :
    (∀ x : R ⊗[R₀] M, u.baseChange R x = 0 → ∀ a ∈ J.map (algebraMap R₀ R), a • x = 0) ∧
    (∀ (y : R ⊗[R₀] N), ∀ a ∈ J.map (algebraMap R₀ R), ∃ x : R ⊗[R₀] M, u.baseChange R x = a • y)
```

### `LinearMap.index_range_eq_card_residueField_pow_of_associated_det_pow`

`Thm_LinearMap_index_range_eq_card_residueField_pow_of_associated_det_pow` — Index of the image equals q^{ ord(det f)}

```lean
theorem LinearMap.index_range_eq_card_residueField_pow_of_associated_det_pow
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)]
    (M : Type) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (f : M →ₗ[R] M) (hf : Function.Injective f)
    (ϖ : R) (hϖ : Irreducible ϖ) (m : ℕ) (hdet : Associated (LinearMap.det f) (ϖ ^ m)) :
    (LinearMap.range f).toAddSubgroup.index = Nat.card (IsLocalRing.ResidueField R) ^ m
```

### `LinearMap.isOpen_setOf_bijective_baseChange_residueField_and_forall_bijective_baseChange_iff`

`Thm_LinearMap_isOpen_setOf_bijective_baseChange_residueField_and_forall_bijective_baseChange_iff` — Openness of the isomorphism locus of u : A^m → M

```lean
theorem LinearMap.isOpen_setOf_bijective_baseChange_residueField_and_forall_bijective_baseChange_iff
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Projective A M]
    {m : ℕ} (u : (Fin m → A) →ₗ[A] M) :
    IsOpen {𝔭 : PrimeSpectrum A | Function.Bijective (u.baseChange 𝔭.asIdeal.ResidueField)} ∧
    ∀ (B : Type u) [CommRing B] [Algebra A B],
      Function.Bijective (u.baseChange B) ↔
        Set.range (PrimeSpectrum.comap (algebraMap A B)) ⊆
          {𝔭 : PrimeSpectrum A | Function.Bijective (u.baseChange 𝔭.asIdeal.ResidueField)}
```

### `LinearMap.isOpen_setOf_surjective_baseChange_residueField`

`Thm_LinearMap_isOpen_setOf_surjective_baseChange_residueField` — Fibrewise surjectivity is open when the cokernel is finitely generated

```lean
theorem LinearMap.isOpen_setOf_surjective_baseChange_residueField
    {A : Type u} [CommRing A] {P : Type v} {Q : Type w} [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    (d : P →ₗ[A] Q) [Module.Finite A (Q ⧸ LinearMap.range d)] :
    IsOpen {𝔭 : PrimeSpectrum A | Function.Surjective (d.baseChange 𝔭.asIdeal.ResidueField)}
```

### `LinearMap.length_quotient_range_eq_of_injective_of_comp_eq_comp`

`Thm_LinearMap_length_quotient_range_eq_of_injective_of_comp_eq_comp` — Isogeny invariance of cokernel length over a DVR

```lean
theorem LinearMap.length_quotient_range_eq_of_injective_of_comp_eq_comp
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {r : ℕ}
    (F₁ F₂ φ : (Fin r → A) →ₗ[A] (Fin r → A))
    (hF₁ : Function.Injective F₁) (hφ : Function.Injective φ)
    (hcomm : φ ∘ₗ F₂ = F₁ ∘ₗ φ) :
    Module.length A ((Fin r → A) ⧸ LinearMap.range F₁) =
      Module.length A ((Fin r → A) ⧸ LinearMap.range F₂)
```

### `LinearMap.nonempty_kerModRange_equiv_of_equiv_comm`

`Thm_LinearMap_nonempty_kerModRange_equiv_of_equiv_comm` — Transfer of ker d⁰ and ker dⁱ⁺¹/im dⁱ along a degreewise isomorphism

```lean
theorem LinearMap.nonempty_kerModRange_equiv_of_equiv_comm
    {R : Type u} [CommRing R] {C C' : ℕ → Type u}
    [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, AddCommGroup (C' i)] [∀ i, Module R (C' i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (d' : ∀ i, C' i →ₗ[R] C' (i + 1))
    (e : ∀ i, C i ≃ₗ[R] C' i) (he : ∀ i x, e (i + 1) (d i x) = d' i (e i x)) :
    Nonempty (LinearMap.ker (d 0) ≃ₗ[R] LinearMap.ker (d' 0)) ∧
    ∀ i, Nonempty
      ((LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype) ≃ₗ[R]
       (LinearMap.ker (d' (i + 1)) ⧸ (LinearMap.range (d' i)).comap (LinearMap.ker (d' (i + 1))).subtype))
```

### `LinearMap.relIndex_pow_smul_top_comap_eq_card_pow_min_of_finrank_ker_baseChange_le_one`

`Thm_LinearMap_relIndex_pow_smul_top_comap_eq_card_pow_min_of_finrank_ker_baseChange_le_one` — Index of varpi^s M in f⁻¹(varpi^s M) equals q^{min(s,m)}

```lean
theorem LinearMap.relIndex_pow_smul_top_comap_eq_card_pow_min_of_finrank_ker_baseChange_le_one
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)]
    (M : Type) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (f : M →ₗ[R] M) (hf : Function.Injective f)
    (hker : Module.finrank (IsLocalRing.ResidueField R)
        (LinearMap.ker (f.baseChange (IsLocalRing.ResidueField R))) ≤ 1)
    (ϖ : R) (hϖ : Irreducible ϖ) (m : ℕ) (hdet : Associated (LinearMap.det f) (ϖ ^ m)) (s : ℕ) :
    ((Ideal.span {ϖ ^ s} • ⊤ : Submodule R M).toAddSubgroup).relIndex
        (((Ideal.span {ϖ ^ s} • ⊤ : Submodule R M).comap f).toAddSubgroup) =
      Nat.card (IsLocalRing.ResidueField R) ^ min s m
```

### `LinearMap.sum_neg_one_pow_mul_finrank_eq_zero_of_exact`

`Thm_LinearMap_sum_neg_one_pow_mul_finrank_eq_zero_of_exact` — Alternating sum of dimensions along a long exact sequence

```lean
theorem LinearMap.sum_neg_one_pow_mul_finrank_eq_zero_of_exact
    {k : Type u} [DivisionRing k] (A B C : ℕ → Type v)
    [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)] [∀ i, Module.Finite k (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module k (B i)] [∀ i, Module.Finite k (B i)]
    [∀ i, AddCommGroup (C i)] [∀ i, Module k (C i)] [∀ i, Module.Finite k (C i)]
    (f : ∀ i, A i →ₗ[k] B i) (g : ∀ i, B i →ₗ[k] C i) (δ : ∀ i, C i →ₗ[k] A (i + 1))
    (hf0 : Function.Injective (f 0))
    (hfg : ∀ i, Function.Exact (f i) (g i))
    (hgδ : ∀ i, Function.Exact (g i) (δ i))
    (hδf : ∀ i, Function.Exact (δ i) (f (i + 1)))
    (N : ℕ) (hN : Subsingleton (A N)) :
    ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i *
        ((Module.finrank k (A i) : ℤ) - Module.finrank k (B i) + Module.finrank k (C i)) = 0
```

### `LinearMap.sum_roots_charpoly_map_pow_eq_trace_pow`

`Thm_LinearMap_sum_roots_charpoly_map_pow_eq_trace_pow` — Power sums of charpoly roots equal traces of powers

```lean
theorem LinearMap.sum_roots_charpoly_map_pow_eq_trace_pow {L : Type*} [Field L] {V : Type*}
    [AddCommGroup V] [Module L V] [FiniteDimensional L V] (E : Type*) [Field E] [Algebra L E]
    [IsAlgClosed E] (T : V →ₗ[L] V) (n : ℕ) :
    (((T.charpoly).map (algebraMap L E)).roots.map (fun z => z ^ n)).sum =
      algebraMap L E (LinearMap.trace L V (T ^ n))
```

### `LinearMap.trace_eq_and_det_eq_of_semiconj`

`Thm_LinearMap_trace_eq_and_det_eq_of_semiconj` — Trace and determinant are invariant under semiconjugation

```lean
theorem LinearMap.trace_eq_and_det_eq_of_semiconj {R : Type*} {M : Type*} {N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (f : Module.End R M) (g : Module.End R N) (h : ∀ x : M, e (f x) = g (e x)) : LinearMap.trace R M f = LinearMap.trace R N g ∧ LinearMap.det f = LinearMap.det g
```

### `LinearMap.trace_eq_of_sq_sub_smul_add_eq_zero_of_det_eq`

`Thm_LinearMap_trace_eq_of_sq_sub_smul_add_eq_zero_of_det_eq` — Trace from a quadratic relation and the determinant in rank two

```lean
theorem LinearMap.trace_eq_of_sq_sub_smul_add_eq_zero_of_det_eq
    {R : Type*} {M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (h : Module.finrank R M = 2)
    (f : M →ₗ[R] M) (a d : R) (hf : f * f - a • f + d • (1 : M →ₗ[R] M) = 0)
    (hdet : LinearMap.det f = d) (hd : d ≠ 0) :
    LinearMap.trace R M f = a
```

### `LinearMap.trace_sub_mul_sq_sub_eq_zero_of_finrank_eq_two`

`Thm_LinearMap_trace_sub_mul_sq_sub_eq_zero_of_finrank_eq_two` — Trace defect of a quadratic endomorphism in dimension two

```lean
theorem LinearMap.trace_sub_mul_sq_sub_eq_zero_of_finrank_eq_two
    {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hV : Module.finrank k V = 2) (Φ : V →ₗ[k] V) (t n : k) (hΦ : Φ * Φ - t • Φ + n • (1 : V →ₗ[k] V) = 0) :
    (LinearMap.trace k V Φ - t) * ((LinearMap.trace k V Φ - t) ^ 2 - (t ^ 2 - 4 * n)) = 0
```

## Representation (47)

### `Representation.centralizer_eq_adjoin_and_isField_of_isSimple_of_forall_commute`

`Thm_Representation_centralizer_eq_adjoin_and_isField_of_isSimple_of_forall_commute` — Commutant of a simple commuting representation is a field acting simply transitively

```lean
theorem Representation.centralizer_eq_adjoin_and_isField_of_isSimple_of_forall_commute
    {k : Type*} [Field k] {Γ : Type*} [Group Γ] {V : Type*} [AddCommGroup V] [Module k V]
    [Nontrivial V] (ρ : Representation k Γ V)
    (hsimple : ∀ W : Submodule k V, (∀ (g : Γ) (v : V), v ∈ W → ρ g v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hcomm : ∀ a b : Γ, ρ a * ρ b = ρ b * ρ a) :
    Subalgebra.centralizer k (Set.range (ρ : Γ → Module.End k V))
        = Algebra.adjoin k (Set.range (ρ : Γ → Module.End k V)) ∧
    IsField (Subalgebra.centralizer k (Set.range (ρ : Γ → Module.End k V))) ∧
    ∀ v : V, v ≠ 0 → Function.Bijective
      (fun φ : Subalgebra.centralizer k (Set.range (ρ : Γ → Module.End k V)) =>
        (φ : Module.End k V) v)
```

### `Representation.det_eq_of_sq_sub_trace_smul_add_smul_one_eq_zero`

`Thm_Representation_det_eq_of_sq_sub_trace_smul_add_smul_one_eq_zero` — Quadratic relation forces d=detρ_V in characteristic ≠ 2

```lean
theorem Representation.det_eq_of_sq_sub_trace_smul_add_smul_one_eq_zero
    {k : Type} [Field k] (h2 : (2 : k) ≠ 0) {G : Type} [Group G]
    {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (hV : Module.finrank k V = 2)
    (ρV : G →* Module.End k V)
    {M : Type} [AddCommGroup M] [Module k M] [Nontrivial M]
    (ρM : G →* Module.End k M) (d : G →* kˣ)
    (hrel : ∀ g : G,
      ρM g * ρM g - (LinearMap.trace k V (ρV g)) • ρM g + ((d g : kˣ) : k) • (1 : Module.End k M) = 0) :
    ∀ g : G, LinearMap.det (ρV g) = d g
```

### `Representation.existsUnique_mem_centralizer_apply_eq_of_forall_commute`

`Thm_Representation_existsUnique_mem_centralizer_apply_eq_of_forall_commute` — Schur's lemma for irreducible representations with commuting operators

```lean
theorem Representation.existsUnique_mem_centralizer_apply_eq_of_forall_commute
    {k : Type*} [Field k] {Δ : Type*} [Group Δ] {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k Δ V)
    (hsimple : ∀ W : Submodule k V, (∀ (d : Δ) (v : V), v ∈ W → ρ d v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hcomm : ∀ a b : Δ, ρ a * ρ b = ρ b * ρ a)
    (v : V) (hv : v ≠ 0) (w : V) :
    ∃! φ : Module.End k V, (∀ d : Δ, φ * ρ d = ρ d * φ) ∧ φ v = w
```

### `Representation.exists_basis_toMatrix_mem_subfield_of_trace_det_mem_of_hasEigenvalue`

`Thm_Representation_exists_basis_toMatrix_mem_subfield_of_trace_det_mem_of_hasEigenvalue` — Descent of an irreducible 2-dimensional representation to a subfield

```lean
theorem Representation.exists_basis_toMatrix_mem_subfield_of_trace_det_mem_of_hasEigenvalue
    {Ω : Type*} [Field Ω] {V : Type*} [AddCommGroup V] [Module Ω V] {G : Type*} [Group G]
    (F : Subfield Ω) (ρ : G →* (V ≃ₗ[Ω] V)) (hV : Module.finrank Ω V = 2)
    (hirr : ∀ W : Submodule Ω V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤)
    (htr : ∀ g, LinearMap.trace Ω V (ρ g).toLinearMap ∈ F)
    (hdet : ∀ g, LinearMap.det (ρ g).toLinearMap ∈ F)
    (g₀ : G) (a : Ω) (haF : a ∈ F) (hev : Module.End.HasEigenvalue (ρ g₀).toLinearMap a)
    (hns : (ρ g₀).toLinearMap ≠ a • LinearMap.id) :
    ∃ b : Module.Basis (Fin 2) Ω V,
      ∀ g (i j : Fin 2), LinearMap.toMatrix b b (ρ g).toLinearMap i j ∈ F
```

### `Representation.exists_blrDecomposition_of_spanTop_of_quadraticAnnihilation`

`Thm_Representation_exists_blrDecomposition_of_spanTop_of_quadraticAnnihilation` — Boston–Lenstra–Ribet: quadratic annihilation forces W≅ρ^{⊕ n}

```lean
theorem Representation.exists_blrDecomposition_of_spanTop_of_quadraticAnnihilation
    {k : Type} [Field k] {G : Type} [Group G]
    (ρ : G →* Matrix (Fin 2) (Fin 2) k)
    {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (σW : Representation k G W)
    (h2 : (2 : k) ≠ 0)
    (hirr : Submodule.span k (Set.range (fun g : G => ρ g)) = ⊤)
    (hann : ∀ g : G,
      σW g ^ 2 - Matrix.trace (ρ g) • σW g + (ρ g).det • (1 : W →ₗ[k] W) = 0) :
    ∃ (n : ℕ) (e : W ≃ₗ[k] (Fin n → (Fin 2 → k))),
      ∀ (g : G) (w : W) (i : Fin n), e (σW g w) i = (ρ g).mulVec (e w i)
```

### `Representation.exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top`

`Thm_Representation_exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top` — Descent of an absolutely irreducible representation over a finite field

```lean
theorem Representation.exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top
    {K : Type v} [Field K] {L : Type u} [Field L] [Algebra K L] [Finite L]
    {n : Type} [DecidableEq n] [Fintype n] [Nonempty n] {G : Type u} [Group G]
    (φ : G →* GL n L)
    (hspan : Submodule.span L (Set.range fun g => (φ g : Matrix n n L)) = ⊤)
    (hcoeff : ∀ g i, (φ g : Matrix n n L).charpoly.coeff i ∈ (algebraMap K L).range) :
    ∃ ρ : G →* GL n ((algebraMap K L).range), ∃ Q : GL n L,
      ∀ g, (Q⁻¹ * φ g * Q : Matrix n n L)
        = (ρ g : Matrix n n ((algebraMap K L).range)).map ((algebraMap K L).range.subtype)
```

### `Representation.exists_conj_eq_of_charpoly_eq_of_finite_range`

`Thm_Representation_exists_conj_eq_of_charpoly_eq_of_finite_range` — Finite-image GL₂(ℂ) representations with equal characteristic polynomials are conjugate

```lean
theorem Representation.exists_conj_eq_of_charpoly_eq_of_finite_range
    {G : Type*} [Group G] (ρ ρ' : G →* GL (Fin 2) ℂ)
    (hρ : Finite (MonoidHom.range ρ)) (hρ' : Finite (MonoidHom.range ρ'))
    (h : ∀ g : G, ((ρ g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).charpoly =
      ((ρ' g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).charpoly) :
    ∃ P : GL (Fin 2) ℂ, ∀ g : G, ρ' g = P * ρ g * P⁻¹
```

### `Representation.exists_const_apply_central_mul_eq_of_countable_translates_of_irreducible`

`Thm_Representation_exists_const_apply_central_mul_eq_of_countable_translates_of_irreducible` — Schur's lemma: central translation acts by a scalar

```lean
theorem Representation.exists_const_apply_central_mul_eq_of_countable_translates_of_irreducible
    {G : Type*} [Group G] (f : G → ℂ)
    (hcount : (Set.range fun h : G => fun g : G => f (g * h)).Countable)
    (hf : f ≠ 0)
    (hirr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => f (g * h)),
      w ≠ 0 → f ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h)))
    (z : G) (hz : ∀ g : G, z * g = g * z) :
    ∃ c : ℂ, ∀ g : G, f (z * g) = c * f g
```

### `Representation.exists_extend_forall_apply_mul_of_injective`

`Thm_Representation_exists_extend_forall_apply_mul_of_injective` — Extension of right-translation-equivariant maps into ℂ^G

```lean
theorem Representation.exists_extend_forall_apply_mul_of_injective
    {H : Type u} {G : Type v} [Group H] [Group G] {W : Type w} [AddCommGroup W] [Module ℂ W]
    (ι : H →* G) (hι : Function.Injective ι)
    (ρ : Representation ℂ H W) (P : Submodule ℂ W) (hP : ∀ k : H, ∀ v ∈ P, ρ k v ∈ P)
    (T : P →ₗ[ℂ] (G → ℂ))
    (hT : ∀ (k : H) (v : P) (x : G), T ⟨ρ k v, hP k v v.2⟩ x = T v (x * ι k)) :
    ∃ T' : W →ₗ[ℂ] (G → ℂ),
      (∀ (k : H) (v : W) (x : G), T' (ρ k v) x = T' v (x * ι k)) ∧ ∀ v : P, T' v = T v
```

### `Representation.exists_injective_equivariant_of_quadraticRelation_of_faithful_of_isReduced`

`Thm_Representation_exists_injective_equivariant_of_quadraticRelation_of_faithful_of_isReduced` — Boston–Lenstra–Ribet equivariant embedding lemma over a reduced algebra

```lean
theorem Representation.exists_injective_equivariant_of_quadraticRelation_of_faithful_of_isReduced
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪]
    {R : Type} [CommRing R] [Algebra 𝒪 R] [Module.Finite 𝒪 R] [IsReduced R]
    {G : Type} [Group G]
    {V : Type} [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    (hV : Module.finrank R V = 2)
    (ρV : G →* Module.End R V) (hspan : Submodule.span R (Set.range ⇑ρV) = ⊤)
    {Y : Type} [AddCommGroup Y] [Module R Y] [Module 𝒪 Y] [IsScalarTower 𝒪 R Y]
    [Module.Finite 𝒪 Y] [Module.IsTorsionFree 𝒪 Y]
    (hfaith : ∀ x : R, (∀ y : Y, x • y = 0) → x = 0)
    (ρY : G →* Module.End R Y)
    {Δ : Type} [CommGroup Δ] [Finite Δ] (D : Δ →* Module.End R Y)
    (hD : ∀ (d : Δ) (g : G), D d * ρY g = ρY g * D d)
    (δ : G →* Δ) (c : G →* Rˣ)
    (hrel : ∀ g : G,
      ρY g * ρY g - (LinearMap.trace R V (ρV g)) • ρY g + ((c g : Rˣ) : R) • D (δ g) = 0) :
    ∃ j : V →ₗ[R] Y, Function.Injective j ∧ ∀ (g : G) (v : V), j (ρV g v) = ρY g (j v)
```

### `Representation.exists_injective_equivariant_of_quadraticRelation_of_isArtinianRing_of_isReduced`

`Thm_Representation_exists_injective_equivariant_of_quadraticRelation_of_isArtinianRing_of_isReduced` — Boston–Lenstra–Ribet embedding over a reduced Artinian ℚ-algebra

```lean
theorem Representation.exists_injective_equivariant_of_quadraticRelation_of_isArtinianRing_of_isReduced
    {k : Type} [CommRing k] [IsArtinianRing k] [IsReduced k] [Algebra ℚ k]
    {G : Type} [Group G]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Free k V] [Module.Finite k V] (hV : Module.finrank k V = 2)
    (ρV : G →* Module.End k V) (hspan : Submodule.span k (Set.range ⇑ρV) = ⊤)
    {M : Type} [AddCommGroup M] [Module k M] [Module.Finite k M]
    (hfaith : ∀ x : k, (∀ m : M, x • m = 0) → x = 0)
    (ρM : G →* Module.End k M) (d : G →* kˣ)
    (hrel : ∀ g : G,
      ρM g * ρM g - (LinearMap.trace k V (ρV g)) • ρM g + ((d g : kˣ) : k) • (1 : Module.End k M) = 0) :
    ∃ j : V →ₗ[k] M, Function.Injective j ∧ ∀ (g : G) (v : V), j (ρV g v) = ρM g (j v)
```

### `Representation.exists_isCompl_forall_mem_of_compactSpace_of_continuous`

`Thm_Representation_exists_isCompl_forall_mem_of_compactSpace_of_continuous` — Stable complements for continuous representations of compact groups

```lean
theorem Representation.exists_isCompl_forall_mem_of_compactSpace_of_continuous
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    {E : Type v} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (π : Representation ℂ H E) (hπ : ∀ (ℓ : Module.Dual ℂ E) (v : E), Continuous fun k => ℓ (π k v))
    (P : Submodule ℂ E) (hP : ∀ k : H, ∀ v ∈ P, π k v ∈ P) :
    ∃ Pc : Submodule ℂ E, IsCompl P Pc ∧ ∀ k : H, ∀ v ∈ Pc, π k v ∈ Pc
```

### `Representation.exists_linearEquiv_of_finrank_invariants_eq`

`Thm_Representation_exists_linearEquiv_of_finrank_invariants_eq` — Rational representations of a cyclic group determined by invariant dimensions

```lean
theorem Representation.exists_linearEquiv_of_finrank_invariants_eq {G V W : Type*} [Group G] [Fintype G] [IsCyclic G]
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ G V) (τ : Representation ℚ G W)
    (h : ∀ H : Subgroup G, Module.finrank ℚ (Representation.invariants (ρ.comp H.subtype)) =
      Module.finrank ℚ (Representation.invariants (τ.comp H.subtype))) :
    ∃ e : V ≃ₗ[ℚ] W, ∀ (g : G) (v : V), e (ρ g v) = τ g (e v)
```

### `Representation.exists_linearEquiv_of_span_range_eq_top_of_trace_eq_of_isLocalRing`

`Thm_Representation_exists_linearEquiv_of_span_range_eq_top_of_trace_eq_of_isLocalRing` — Trace determines representations spanning the endomorphism algebra

```lean
theorem Representation.exists_linearEquiv_of_span_range_eq_top_of_trace_eq_of_isLocalRing
    {A : Type} [CommRing A] [IsLocalRing A] {G : Type} [Monoid G]
    {V₁ V₂ : Type} [AddCommGroup V₁] [Module A V₁] [Module.Free A V₁] [Module.Finite A V₁]
    [AddCommGroup V₂] [Module A V₂] [Module.Free A V₂] [Module.Finite A V₂]
    (ρ₁ : G →* Module.End A V₁) (ρ₂ : G →* Module.End A V₂)
    (hrank : Module.finrank A V₁ = Module.finrank A V₂)
    (hspan₁ : Submodule.span A (Set.range ⇑ρ₁) = ⊤)
    (hspan₂ : Submodule.span A (Set.range ⇑ρ₂) = ⊤)
    (htr : ∀ g : G, LinearMap.trace A V₁ (ρ₁ g) = LinearMap.trace A V₂ (ρ₂ g)) :
    ∃ e : V₁ ≃ₗ[A] V₂, ∀ (g : G) (v : V₁), e (ρ₁ g v) = ρ₂ g (e v)
```

### `Representation.exists_map_eq_conj_and_span_range_eq_top_of_charpoly_coeff_mem_range_of_finite_fin_two`

`Thm_Representation_exists_map_eq_conj_and_span_range_eq_top_of_charpoly_coeff_mem_range_of_finite_fin_two` — Descent of an absolutely irreducible two-dimensional representation to a finite field

```lean
theorem Representation.exists_map_eq_conj_and_span_range_eq_top_of_charpoly_coeff_mem_range_of_finite_fin_two
    {G : Type} [Group G] {k₀ : Type} [Field k₀] [Finite k₀] {F : Type} [Field F] (e₀ : k₀ →+* F)
    (ρ : G →* GL (Fin 2) F)
    (hcoeff : ∀ (x : G) (i : ℕ), ((ρ x).val.charpoly).coeff i ∈ e₀.range)
    (habs : ∀ {F' : Type} [Field F'] (e : F →+* F') (u : Fin 2 → F'), u ≠ 0 →
      ∃ x : G, Matrix.mulVec ((ρ x).val.map e) u ∉ F' ∙ u) :
    ∃ (ρ₀ : G →* GL (Fin 2) k₀) (g : GL (Fin 2) F),
      (∀ x : G, (ρ₀ x).val.map e₀ = g.val * (ρ x).val * (g⁻¹).val) ∧
      Submodule.span k₀ (Set.range (fun x : G => (ρ₀ x).val)) = ⊤
```

### `Representation.exists_monoidHom_complex_charpoly_map_eq_of_not_dvd_natCard`

`Thm_Representation_exists_monoidHom_complex_charpoly_map_eq_of_not_dvd_natCard` — Lifting mod-ℓ representations of ℓ'-order groups

```lean
theorem Representation.exists_monoidHom_complex_charpoly_map_eq_of_not_dvd_natCard
    (G : Type) [Group G] [Finite G]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ Nat.card G)
    (k : Type) [Field k] [Finite k] [CharP k ℓ]
    (n m : ℕ) (hm : 0 < m) (hℓm : ¬ ℓ ∣ m) (hGm : ∀ g : G, g ^ m = 1)
    (S : Subalgebra ℤ ℂ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) (hζS : ζ ∈ S) (φ : S →+* k)
    (ρbar : G →* GL (Fin n) k) :
    ∃ ρ : G →* GL (Fin n) ℂ, ∀ g : G, ∃ P : Polynomial S,
      P.map (algebraMap S ℂ) = ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).charpoly ∧
      P.map φ = ((ρbar g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly
```

### `Representation.exists_multiplicity_of_isCyclic`

`Thm_Representation_exists_multiplicity_of_isCyclic` — Decomposition of a cyclic-group representation into characters

```lean
theorem Representation.exists_multiplicity_of_isCyclic {C K V : Type*} [CommGroup C] [Fintype C] [IsCyclic C]
    [Field K] [IsAlgClosed K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (τ : Representation K C V) :
    ∃ m : (C →* Kˣ) →₀ ℕ,
      (∀ c, LinearMap.trace K V (τ c) = m.sum fun μ n => (n : K) * ((μ c : Kˣ) : K)) ∧
      (∀ c, (τ c).charpoly = m.prod fun μ n => (X - Polynomial.C ((μ c : Kˣ) : K)) ^ n) ∧
      (m.sum fun _ n => n) = Module.finrank K V ∧
      (∀ μ ∈ m.support, ∀ c, τ c = LinearMap.id → μ c = 1)
```

### `Representation.exists_ne_zero_forall_apply_eq_of_isPGroup`

`Thm_Representation_exists_ne_zero_forall_apply_eq_of_isPGroup` — Nonzero fixed vector for p-groups in characteristic p

```lean
theorem Representation.exists_ne_zero_forall_apply_eq_of_isPGroup
    {k : Type*} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]
    {G : Type*} [Group G] [Finite G] (hG : IsPGroup p G)
    {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V) {v : V} (hv : v ≠ 0) :
    ∃ w : V, w ≠ 0 ∧ ∀ g : G, ρ g w = w
```

### `Representation.exists_ne_zero_forall_apply_eq_self_or_eq_char_smul`

`Thm_Representation_exists_ne_zero_forall_apply_eq_self_or_eq_char_smul` — Common eigenvector with eigencharacter 1 or χ

```lean
theorem Representation.exists_ne_zero_forall_apply_eq_self_or_eq_char_smul
    {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V] [Finite V] [Nontrivial V]
    (ρ : Representation k G V) (χ : G →* kˣ)
    (h : ∀ (g : G) (v : V), ρ g (ρ g v - (χ g : k) • v) = ρ g v - (χ g : k) • v) :
    ∃ v : V, v ≠ 0 ∧ ((∀ g : G, ρ g v = v) ∨ (∀ g : G, ρ g v = (χ g : k) • v))
```

### `Representation.exists_submodule_quotient_line_of_commutator_le_of_isPGroup`

`Thm_Representation_exists_submodule_quotient_line_of_commutator_le_of_isPGroup` — Simple quotient of an mathbb Fₚ[Γ]-module is an F-line

```lean
theorem Representation.exists_submodule_quotient_line_of_commutator_le_of_isPGroup
    (p : ℕ) [Fact p.Prime]
    {Γ : Type u} [Group Γ] [Finite Γ] (P : Subgroup Γ) [P.Normal] (hP : IsPGroup p ↥P)
    (hcomm : ∀ a b : Γ, a⁻¹ * b⁻¹ * a * b ∈ P)
    {V : Type v} [AddCommGroup V] [Module (ZMod p) V] [Finite V] [Nontrivial V]
    (ρ : Representation (ZMod p) Γ V) :
    ∃ W : Submodule (ZMod p) V, (∀ (g : Γ) (v : V), v ∈ W → ρ g v ∈ W) ∧ W ≠ ⊤ ∧
      ∃ (F : Type) (_ : Field F) (_ : Fintype F) (_ : Module F (V ⧸ W)) (r : ℕ),
        0 < r ∧ Fintype.card F = p ^ r ∧
        (∀ (m : ℕ) (q : V ⧸ W), (m : F) • q = m • q) ∧
        Module.finrank F (V ⧸ W) = 1 ∧
        (∀ g : Γ, ∃ a : F, ∀ v : V, W.mkQ (ρ g v) = a • W.mkQ v)
```

### `Representation.exists_trace_ne_one_add_det_of_irreducible`

`Thm_Representation_exists_trace_ne_one_add_det_of_irreducible` — Irreducible two-dimensional ρ fails tr = 1 + det

```lean
theorem Representation.exists_trace_ne_one_add_det_of_irreducible {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) (hfr : Module.finrank k V = 2)
    (hirr : ∀ W : Submodule k V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ g, LinearMap.trace k V (ρ g) ≠ 1 + LinearMap.det (ρ g)
```

### `Representation.false_of_span_eq_top_of_trace_eq_of_commute`

`Thm_Representation_false_of_span_eq_top_of_trace_eq_of_commute` — No commuting representation shares the character of a 2-dimensional Burnside representation

```lean
theorem Representation.false_of_span_eq_top_of_trace_eq_of_commute
    {k G V V' : Type*} [Field k] [Monoid G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
    (h2 : Module.finrank k V = 2)
    (ρ : G →* Module.End k V) (hspan : Submodule.span k (Set.range ρ) = ⊤)
    (τ : G →* Module.End k V') (hcomm : ∀ g h : G, Commute (τ g) (τ h))
    (htr : ∀ g : G, LinearMap.trace k V (ρ g) = LinearMap.trace k V' (τ g)) : False
```

### `Representation.finrank_eq_card_mul_finrank_coinvariants_of_isPGroup`

`Thm_Representation_finrank_eq_card_mul_finrank_coinvariants_of_isPGroup` — Rank of a cohomologically trivial lattice over a p-group

```lean
theorem Representation.finrank_eq_card_mul_finrank_coinvariants_of_isPGroup
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪] [IsLocalRing 𝒪]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField 𝒪) p]
    {G : Type} [Group G] [Fintype G] (hG : IsPGroup p G)
    {P : Type} [AddCommGroup P] [Module 𝒪 P] [Module.Finite 𝒪 P] [Module.IsTorsionFree 𝒪 P]
    (ρ : Representation 𝒪 G P)
    (h0 : ∀ w : P, (∀ g : G, ρ g w = w) → ∃ m : P, ρ.norm m = w)
    (h1 : ∀ v : P, ρ.norm v = 0 → v ∈ Representation.Coinvariants.ker ρ) :
    Module.finrank 𝒪 P = Fintype.card G * Module.finrank 𝒪 (Representation.Coinvariants ρ)
```

### `Representation.finrank_invariants_dual_of_isUnit_card`

`Thm_Representation_finrank_invariants_dual_of_isUnit_card` — Dual representation has invariants of equal dimension

```lean
theorem Representation.finrank_invariants_dual_of_isUnit_card
    {k : Type*} [Field k] {Δ : Type*} [Group Δ] [Fintype Δ] (hΔ : IsUnit ((Fintype.card Δ : k)))
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k Δ V) :
    finrank k ρ.dual.invariants = finrank k ρ.invariants
```

### `Representation.finrank_invariants_eq_one_of_natCard_map_eq_two`

`Thm_Representation_finrank_invariants_eq_one_of_natCard_map_eq_two` — Non-central order-two image in GL₂ fixes a line

```lean
theorem Representation.finrank_invariants_eq_one_of_natCard_map_eq_two
    {Γ : Type u} [Group Γ] {k : Type u} [Field k]
    (ρ : Γ →* GL (Fin 2) k) (I : Subgroup Γ)
    (hcard : Nat.card (I.map ρ) = 2)
    (hcent : ¬ I.map ρ ≤ Subgroup.center (GL (Fin 2) k)) :
    Module.finrank k
        (Representation.invariants
          ((Deformation.matrixRepresentation ρ).comp I.subtype)) = 1
```

### `Representation.finrank_invariants_linHom_dual_twist_ofChar`

`Thm_Representation_finrank_invariants_linHom_dual_twist_ofChar` — Dimension of Hom_Δ(V^∨(χ),k(χ)) equals dim V^Δ

```lean
theorem Representation.finrank_invariants_linHom_dual_twist_ofChar
    {k : Type*} [Field k] {Δ : Type*} [Group Δ]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k Δ V) (χ : Δ →* kˣ) :
    finrank k ((ρ.dual.twist χ).linHom ((Representation.trivial k Δ k).twist χ)).invariants = finrank k ρ.invariants
```

### `Representation.finrank_invariants_linHom_eq_add_of_exact_of_isUnit_card`

`Thm_Representation_finrank_invariants_linHom_eq_add_of_exact_of_isUnit_card` — Additivity of dim_k Hom_Δ(N,-) on short exact sequences

```lean
theorem Representation.finrank_invariants_linHom_eq_add_of_exact_of_isUnit_card
    {k : Type*} [Field k] {Δ : Type*} [Group Δ] [Fintype Δ] (hΔ : IsUnit ((Fintype.card Δ : k)))
    {VN VA VB VC : Type*} [AddCommGroup VN] [Module k VN] [AddCommGroup VA] [Module k VA]
    [AddCommGroup VB] [Module k VB] [AddCommGroup VC] [Module k VC]
    [FiniteDimensional k VN] [FiniteDimensional k VB]
    (N : Representation k Δ VN) (A : Representation k Δ VA) (B : Representation k Δ VB) (C : Representation k Δ VC)
    (f : VA →ₗ[k] VB) (g : VB →ₗ[k] VC) (hf : ∀ d, f ∘ₗ A d = B d ∘ₗ f) (hg : ∀ d, g ∘ₗ B d = C d ∘ₗ g)
    (hinj : Function.Injective f) (hsurj : Function.Surjective g) (hexact : Function.Exact f g) :
    finrank k (N.linHom B).invariants = finrank k (N.linHom A).invariants + finrank k (N.linHom C).invariants
```

### `Representation.finrank_invariants_linHom_eq_of_finiteIndex_of_torsionFree`

`Thm_Representation_finrank_invariants_linHom_eq_of_finiteIndex_of_torsionFree` — Mod p Hom-invariants unchanged by a finite-index Δ-stable subgroup

```lean
theorem Representation.finrank_invariants_linHom_eq_of_finiteIndex_of_torsionFree
    {p : ℕ} [Fact p.Prime] {Δ : Type*} [Group Δ] [Fintype Δ] (hΔ : ¬ p ∣ Fintype.card Δ)
    {A : Type*} [AddCommGroup A] (act : Δ →* AddAut A) (htf : ∀ a : A, p • a = 0 → a = 0)
    (B : AddSubgroup A) [B.FiniteIndex] (hB : ∀ (d : Δ) (a : A), a ∈ B → act d a ∈ B)
    {VN : Type*} [AddCommGroup VN] [Module (ZMod p) VN] [FiniteDimensional (ZMod p) VN]
    (N : Representation (ZMod p) Δ VN)
    {VA : Type*} [AddCommGroup VA] [Module (ZMod p) VA] [FiniteDimensional (ZMod p) VA]
    (PA : Representation (ZMod p) Δ VA)
    (πA : A →+ VA) (hπA : Function.Surjective πA) (hkerA : ∀ a : A, πA a = 0 ↔ ∃ a' : A, p • a' = a)
    (hπAΔ : ∀ (d : Δ) (a : A), πA (act d a) = PA d (πA a))
    {VB : Type*} [AddCommGroup VB] [Module (ZMod p) VB] [FiniteDimensional (ZMod p) VB]
    (PB : Representation (ZMod p) Δ VB)
    (πB : B →+ VB) (hπB : Function.Surjective πB) (hkerB : ∀ b : B, πB b = 0 ↔ ∃ b' : B, p • b' = b)
    (hπBΔ : ∀ (d : Δ) (b : B), πB ⟨act d b, hB d b b.2⟩ = PB d (πB b)) :
    finrank (ZMod p) (N.linHom PA).invariants = finrank (ZMod p) (N.linHom PB).invariants
```

### `Representation.finrank_invariants_linHom_modP_add_torsion_eq_of_finiteIndex`

`Thm_Representation_finrank_invariants_linHom_modP_add_torsion_eq_of_finiteIndex` — Invariance of h_N under passage to a finite-index Δ-stable subgroup

```lean
theorem Representation.finrank_invariants_linHom_modP_add_torsion_eq_of_finiteIndex
    {p : ℕ} [Fact p.Prime] {Δ : Type*} [Group Δ] [Fintype Δ] (hΔ : ¬ p ∣ Fintype.card Δ)
    {A : Type*} [AddCommGroup A] (act : Δ →* AddAut A)
    (B : AddSubgroup A) [B.FiniteIndex] (hB : ∀ (d : Δ) (a : A), a ∈ B → act d a ∈ B)
    {VN : Type*} [AddCommGroup VN] [Module (ZMod p) VN] [FiniteDimensional (ZMod p) VN]
    (N : Representation (ZMod p) Δ VN)
    {VA : Type*} [AddCommGroup VA] [Module (ZMod p) VA] [FiniteDimensional (ZMod p) VA]
    (PA : Representation (ZMod p) Δ VA)
    (πA : A →+ VA) (hπA : Function.Surjective πA) (hkerA : ∀ a : A, πA a = 0 ↔ ∃ a' : A, p • a' = a)
    (hπAΔ : ∀ (d : Δ) (a : A), πA (act d a) = PA d (πA a))
    {WA : Type*} [AddCommGroup WA] [Module (ZMod p) WA] [FiniteDimensional (ZMod p) WA]
    (TA : Representation (ZMod p) Δ WA)
    (ιA : WA →+ A) (hιA : Function.Injective ιA) (hranA : ∀ a : A, a ∈ Set.range ιA ↔ p • a = 0)
    (hιAΔ : ∀ (d : Δ) (w : WA), ιA (TA d w) = act d (ιA w))
    {VB : Type*} [AddCommGroup VB] [Module (ZMod p) VB] [FiniteDimensional (ZMod p) VB]
    (PB : Representation (ZMod p) Δ VB)
    (πB : B →+ VB) (hπB : Function.Surjective πB) (hkerB : ∀ b : B, πB b = 0 ↔ ∃ b' : B, p • b' = b)
    (hπBΔ : ∀ (d : Δ) (b : B), πB ⟨act d b, hB d b b.2⟩ = PB d (πB b))
    {WB : Type*} [AddCommGroup WB] [Module (ZMod p) WB] [FiniteDimensional (ZMod p) WB]
    (TB : Representation (ZMod p) Δ WB)
    (ιB : WB →+ B) (hιB : Function.Injective ιB) (hranB : ∀ b : B, b ∈ Set.range ιB ↔ p • b = 0)
    (hιBΔ : ∀ (d : Δ) (w : WB), (ιB (TB d w) : A) = act d (ιB w)) :
    finrank (ZMod p) (N.linHom PA).invariants + finrank (ZMod p) (N.linHom TB).invariants
      = finrank (ZMod p) (N.linHom PB).invariants + finrank (ZMod p) (N.linHom TA).invariants
```

### `Representation.finrank_invariants_linHom_of_basis_regular`

`Thm_Representation_finrank_invariants_linHom_of_basis_regular` — Equivariant maps into a free k[Δ]-module: the dimension count

```lean
theorem Representation.finrank_invariants_linHom_of_basis_regular
    {k : Type*} [Field k] {Δ : Type*} [Group Δ] [Fintype Δ]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (N : Representation k Δ V)
    {VR : Type*} [AddCommGroup VR] [Module k VR] (R : Representation k Δ VR)
    {ι : Type*} [Fintype ι] (b : Module.Basis (Δ × ι) k VR)
    (hb : ∀ (d e : Δ) (i : ι), R d (b (e, i)) = b (d * e, i)) :
    finrank k (N.linHom R).invariants = Fintype.card ι * finrank k V
```

### `Representation.finrank_ker_sub_one_eq_finrank_ker_add_one_of_spanTop_of_quadraticAnnihilation`

`Thm_Representation_finrank_ker_sub_one_eq_finrank_ker_add_one_of_spanTop_of_quadraticAnnihilation` — Equal eigenspace dimensions of an involution with ψ(c)=-1

```lean
theorem Representation.finrank_ker_sub_one_eq_finrank_ker_add_one_of_spanTop_of_quadraticAnnihilation
    {k : Type} [Field k] {G : Type} [Group G]
    (ρ : G →* Matrix (Fin 2) (Fin 2) k)
    {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (σW : Representation k G W)
    (h2 : (2 : k) ≠ 0)
    (hirr : Submodule.span k (Set.range (fun g : G => ρ g)) = ⊤)
    (ψ : G →* kˣ)
    (hann : ∀ g : G,
      σW g ^ 2 - Matrix.trace (ρ g) • σW g + ((ψ g : kˣ) : k) • (1 : W →ₗ[k] W) = 0)
    (c : G) (hc : c * c = 1) (hψc : ψ c = -1) :
    Module.finrank k ↥(LinearMap.ker (σW c - 1)) =
      Module.finrank k ↥(LinearMap.ker (σW c + 1))
```

### `Representation.forall_apply_eq_one_of_normal_isPGroup_of_isSimple`

`Thm_Representation_forall_apply_eq_one_of_normal_isPGroup_of_isSimple` — Normal p-subgroups act trivially on simple mod-p representations

```lean
theorem Representation.forall_apply_eq_one_of_normal_isPGroup_of_isSimple
    {p : ℕ} [Fact p.Prime] {k : Type*} [Field k] [Finite k] [CharP k p]
    {Δ : Type*} [Group Δ] [Finite Δ] {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k Δ V) (hV : Module.finrank k V ≠ 0)
    (hsimple : ∀ W : Submodule k V, (∀ (d : Δ) (v : V), v ∈ W → ρ d v ∈ W) → W = ⊥ ∨ W = ⊤)
    (P : Subgroup Δ) [P.Normal] (hP : IsPGroup p P) :
    ∀ x ∈ P, ρ x = 1
```

### `Representation.injective_liftBaseChange_of_isAbsolutelyIrreducible`

`Thm_Representation_injective_liftBaseChange_of_isAbsolutelyIrreducible` — Injectivity after base change for absolutely irreducible ρ

```lean
theorem Representation.injective_liftBaseChange_of_isAbsolutelyIrreducible
    {F k G V W : Type} [Field F] [Field k] [Algebra F k] [Group G]
    [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module k W] [Module F W] [IsScalarTower F k W]
    (ρ : Representation F G V) [Representation.IsAbsolutelyIrreducible.{0} ρ]
    (τ : Representation k G W)
    (ι : V →ₗ[F] W) (hι : Function.Injective ι)
    (hιG : ∀ (g : G) (v : V), ι (ρ g v) = τ g (ι v)) :
    Function.Injective (ι.liftBaseChange k)
```

### `Representation.isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end`

`Thm_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end` — Commutant criterion for absolute irreducibility of a representation

```lean
theorem Representation.isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end {k G V : Type u} [Field k]
  [Group G] [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k G V) :
  Representation.IsAbsolutelyIrreducible.{u} ρ ↔
    ρ.IsIrreducible ∧ Function.Surjective (algebraMap k (Module.End (MonoidAlgebra k G) ρ.asModule))
```

### `Representation.isAbsolutelyIrreducible_matrix_iff_span_range_eq_top`

`Thm_Representation_isAbsolutelyIrreducible_matrix_iff_span_range_eq_top` — Burnside's criterion for absolute irreducibility

```lean
theorem Representation.isAbsolutelyIrreducible_matrix_iff_span_range_eq_top {n : Type} [Fintype n] [DecidableEq n] {G : Type u}
    [Group G] {k : Type u} [Field k] [Nonempty n] (φ : G →* GL n k) :
    Representation.IsAbsolutelyIrreducible.{u} (Deformation.matrixRepresentation φ) ↔
      Submodule.span k (Set.range fun g => (φ g).val) = ⊤
```

### `Representation.isIrreducible_of_span_range_eq_top`

`Thm_Representation_isIrreducible_of_span_range_eq_top` — Representations spanning the endomorphism algebra are irreducible

```lean
theorem Representation.isIrreducible_of_span_range_eq_top
    {k : Type*} [Field k] {G : Type*} [Monoid G]
    {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) [Nontrivial V]
    (hspan : Submodule.span k (Set.range ⇑ρ) = ⊤) : ρ.IsIrreducible
```

### `Representation.nonempty_equiv_torsionBy_quotient_of_coprime`

`Thm_Representation_nonempty_equiv_torsionBy_quotient_of_coprime` — A[p] ≅ A/pA as G-modules when p ∤ #G

```lean
theorem Representation.nonempty_equiv_torsionBy_quotient_of_coprime
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hG : (Nat.card G).Coprime p)
    {A : Type} [AddCommGroup A] [Finite A] (ρ : Representation ℤ G A)
    (h1 : ∀ g, Submodule.torsionBy ℤ A (p : ℤ) ≤ (Submodule.torsionBy ℤ A (p : ℤ)).comap (ρ g))
    (h2 : ∀ g, (p : ℤ) • (⊤ : Submodule ℤ A) ≤ ((p : ℤ) • (⊤ : Submodule ℤ A)).comap (ρ g)) :
    Nonempty ((ρ.subrepresentation _ h1).Equiv (ρ.quotient _ h2))
```

### `Representation.norm_eq_zero_of_dvd_card`

`Thm_Representation_norm_eq_zero_of_dvd_card` — Vanishing of the norm of a cyclic group in characteristic p

```lean
theorem Representation.norm_eq_zero_of_dvd_card {k Q V : Type*} [Field k] [Group Q] [Fintype Q] [AddCommGroup V] [Module k V] (ρ : Representation k Q V)
    (p : ℕ) [CharP k p] {g : Q} (hg : ∀ x : Q, x ∈ Subgroup.zpowers g) {d : ℕ} (hd : ρ g ^ d = 1) (hpd : p * d ∣ Fintype.card Q) :
    ρ.norm = 0
```

### `Representation.pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero`

`Thm_Representation_pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero` — Invariant pairing with an irreducible representation vanishes

```lean
theorem Representation.pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero
    {k : Type*} [CommSemiring k] {K : Type*} [Group K]
    {S : Type*} [AddCommMonoid S] [Module k S] {S' : Type*} [AddCommMonoid S'] [Module k S']
    {X : Type*} [AddCommMonoid X] [Module k X]
    (ρ : Representation k K S) (ρ' : Representation k K S') [IsSimpleOrder (Subrepresentation ρ')]
    (β : S →ₗ[k] S' →ₗ[k] X) (hβ : ∀ (g : K) (s : S) (s' : S'), β (ρ g s) (ρ' g s') = β s s')
    (h0 : ∃ s' : S', s' ≠ 0 ∧ ∀ s : S, β s s' = 0) :
    β = 0
```

### `Representation.quadraticRelation_apply_mem_of_conj_mul_of_eq_zero`

`Thm_Representation_quadraticRelation_apply_mem_of_conj_mul_of_eq_zero` — Quadratic relation propagates to conjugates times H, modulo N

```lean
theorem Representation.quadraticRelation_apply_mem_of_conj_mul_of_eq_zero
    {R : Type} [CommRing R] {Y : Type} [AddCommGroup Y] [Module R Y]
    {G : Type} [Group G] {U : Type} [CommGroup U]
    (ρ : G →* Module.End R Y) (t : G → R) (c : G →* Rˣ) (χ : G →* U) (D : U →* Module.End R Y)
    (ht : ∀ g h : G, t (g * h * g⁻¹) = t h)
    (hD : ∀ (u : U) (g : G), D u * ρ g = ρ g * D u)
    (N : Submodule R Y) (hNρ : ∀ (g : G), ∀ y ∈ N, ρ g y ∈ N) (hND : ∀ (u : U), ∀ y ∈ N, D u y ∈ N)
    (H : Subgroup G)
    (hρH : ∀ (g : G), ∀ h ∈ H, ∀ y : Y, ρ (g * h) y - ρ g y ∈ N)
    (htH : ∀ (g : G), ∀ h ∈ H, ∀ y : Y, (t (g * h) - t g) • y ∈ N)
    (hcH : ∀ (g : G), ∀ h ∈ H, ∀ y : Y, (((c (g * h) : Rˣ) : R) - ((c g : Rˣ) : R)) • y ∈ N)
    (hχH : ∀ (g : G), ∀ h ∈ H, χ (g * h) = χ g)
    (τ : G) (hτ : ρ τ * ρ τ - t τ • ρ τ + ((c τ : Rˣ) : R) • D (χ τ) = 0)
    (g : G) (h : G) (hh : h ∈ H) (y : Y) :
    (ρ (g * τ * g⁻¹ * h) * ρ (g * τ * g⁻¹ * h) - t (g * τ * g⁻¹ * h) • ρ (g * τ * g⁻¹ * h)
      + ((c (g * τ * g⁻¹ * h) : Rˣ) : R) • D (χ (g * τ * g⁻¹ * h))) y ∈ N
```

### `Representation.span_range_baseChange_eq_top_iff`

`Thm_Representation_span_range_baseChange_eq_top_iff` — Spanning of an endomorphism algebra is insensitive to base change

```lean
theorem Representation.span_range_baseChange_eq_top_iff
    {k K G V : Type*} [Field k] [Field K] [Algebra k K] [Monoid G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : Representation k G V) :
    Submodule.span K (Set.range fun g => (ρ g).baseChange K) = ⊤ ↔
      Submodule.span k (Set.range ⇑ρ) = ⊤
```

### `Representation.span_range_eq_top_of_isAbsolutelyIrreducible`

`Thm_Representation_span_range_eq_top_of_isAbsolutelyIrreducible` — Burnside spanning for absolutely irreducible representations

```lean
theorem Representation.span_range_eq_top_of_isAbsolutelyIrreducible {k G V : Type u} [Field k] [Group G] [AddCommGroup V]
  [Module k V] [FiniteDimensional k V] (ρ : Representation k G V) [Representation.IsAbsolutelyIrreducible.{u} ρ] :
  Submodule.span k (Set.range ρ) = ⊤
```

### `Representation.span_range_eq_top_of_isAbsolutelyIrreducible_matrix`

`Thm_Representation_span_range_eq_top_of_isAbsolutelyIrreducible_matrix` — Burnside spanning theorem for absolutely irreducible matrix representations

```lean
theorem Representation.span_range_eq_top_of_isAbsolutelyIrreducible_matrix
    {n : Type} [Fintype n] [DecidableEq n] {G : Type u} [Group G] {k : Type u} [Field k]
    (ρ : G →* GL n k) [Representation.IsAbsolutelyIrreducible.{u} (Deformation.matrixRepresentation ρ)] :
    Submodule.span k (Set.range fun g => (ρ g).val) = ⊤
```

### `Representation.span_range_eq_top_of_isIrreducible`

`Thm_Representation_span_range_eq_top_of_isIrreducible` — Burnside's theorem for irreducible representations

```lean
theorem Representation.span_range_eq_top_of_isIrreducible
    {k G V : Type*} [Field k] [IsAlgClosed k] [Monoid G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : Representation k G V) [ρ.IsIrreducible] :
    Submodule.span k (Set.range ⇑ρ) = ⊤
```

### `Representation.span_range_eq_top_of_span_range_eq_top_of_trace_eq`

`Thm_Representation_span_range_eq_top_of_span_range_eq_top_of_trace_eq` — Equal traces and dimension propagate End-spanning

```lean
theorem Representation.span_range_eq_top_of_span_range_eq_top_of_trace_eq
    {k : Type} [Field k] {G : Type} [Monoid G]
    {V₁ V₂ : Type} [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
    [AddCommGroup V₂] [Module k V₂] [FiniteDimensional k V₂]
    (ρ₁ : G →* Module.End k V₁) (ρ₂ : G →* Module.End k V₂)
    (hrank : Module.finrank k V₁ = Module.finrank k V₂)
    (hspan₁ : Submodule.span k (Set.range ⇑ρ₁) = ⊤)
    (htr : ∀ g : G, LinearMap.trace k V₁ (ρ₁ g) = LinearMap.trace k V₂ (ρ₂ g)) :
    Submodule.span k (Set.range ⇑ρ₂) = ⊤
```

### `Representation.stable_eq_bot_or_top_of_trace_eq_of_det_eq_of_irreducible`

`Thm_Representation_stable_eq_bot_or_top_of_trace_eq_of_det_eq_of_irreducible` — Irreducibility transfers along equal traces and determinants

```lean
theorem Representation.stable_eq_bot_or_top_of_trace_eq_of_det_eq_of_irreducible {k G V V₂ : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [AddCommGroup V₂] [Module k V₂]
    (ρ₁ : Representation k G V) (ρ₂ : Representation k G V₂)
    (hfr₁ : Module.finrank k V = 2) (hfr₂ : Module.finrank k V₂ = 2)
    (hirr : ∀ W : Submodule k V, (∀ g, ∀ v ∈ W, ρ₁ g v ∈ W) → W = ⊥ ∨ W = ⊤)
    (htr : ∀ g, LinearMap.trace k V (ρ₁ g) = LinearMap.trace k V₂ (ρ₂ g))
    (hdet : ∀ g, LinearMap.det (ρ₁ g) = LinearMap.det (ρ₂ g)) :
    ∀ W : Submodule k V₂, (∀ g, ∀ v ∈ W, ρ₂ g v ∈ W) → W = ⊥ ∨ W = ⊤
```

### `Representation.trace_mul_eq_trace_of_commute_of_pow_prime_pow_eq_one`

`Thm_Representation_trace_mul_eq_trace_of_commute_of_pow_prime_pow_eq_one` — Trace is unchanged by a commuting p-power-order factor

```lean
theorem Representation.trace_mul_eq_trace_of_commute_of_pow_prime_pow_eq_one
    {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] {G : Type} [Group G]
    {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) (g u : G) (hgu : Commute g u) (a : ℕ) (hu : u ^ p ^ a = 1) :
    LinearMap.trace k V (ρ (g * u)) = LinearMap.trace k V (ρ g)
```

## Rep (32)

### `Rep.IsTateCupProduct.cup_assoc`

`Thm_Rep_IsTateCupProduct_cup_assoc` — Associativity of the Tate cup product in all degrees

```lean
theorem Rep.IsTateCupProduct.cup_assoc {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {cup : Rep.TateCupFamily k G} (hcup : Rep.IsTateCupProduct cup) (A B C : Rep.{u} k G)
    (p q r r₁₂ r₂₃ r₁₂₃ : ℤ) (h₁₂ : p + q = r₁₂) (h₂₃ : q + r = r₂₃) (h : r₁₂ + r = r₁₂₃)
    (x : A.tateCohomology p) (y : B.tateCohomology q) (z : C.tateCohomology r) :
    cup (A ⊗ B) C r₁₂ r r₁₂₃ h (cup A B p q r₁₂ h₁₂ x y) z
      = (Rep.tateMap (α_ A B C).inv r₁₂₃).hom (cup A (B ⊗ C) p r₂₃ r₁₂₃ (by omega) x (cup B C q r r₂₃ h₂₃ y z))
```

### `Rep.IsTateCupProduct.cup_comm`

`Thm_Rep_IsTateCupProduct_cup_comm` — Graded commutativity of the Tate cup product

```lean
theorem Rep.IsTateCupProduct.cup_comm {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {cup : Rep.TateCupFamily k G} (hcup : Rep.IsTateCupProduct cup) (A B : Rep.{u} k G)
    (p q r : ℤ) (h : p + q = r) (x : A.tateCohomology p) (y : B.tateCohomology q) :
    cup B A q p r (by omega) y x
      = (((p * q).negOnePow : ℤ) : k) • (Rep.tateMap (β_ A B).hom r).hom (cup A B p q r h x y)
```

### `Rep.IsTateCupProduct.cup_mk_left_eq_tateMap`

`Thm_Rep_IsTateCupProduct_cup_mk_left_eq_tateMap` — Cup product with a degree-0 Tate class is an induced map

```lean
theorem Rep.IsTateCupProduct.cup_mk_left_eq_tateMap {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {cup : Rep.TateCupFamily k G} (hcup : Rep.IsTateCupProduct cup) (A B : Rep.{u} k G)
    (a : A.ρ.invariants) (φ : B ⟶ A ⊗ B) (hφ : ∀ b : B, φ.hom b = (a : A) ⊗ₜ[k] b)
    (q : ℤ) (y : B.tateCohomology q) :
    cup A B 0 q q (zero_add q) (Submodule.Quotient.mk a : A.tateH0) y = (Rep.tateMap φ q).hom y
```

### `Rep.IsTateCupProduct.cup_mk_mk`

`Thm_Rep_IsTateCupProduct_cup_mk_mk` — Cup product of invariant classes in degree (0,0)

```lean
theorem Rep.IsTateCupProduct.cup_mk_mk {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {cup : Rep.TateCupFamily k G} (hcup : Rep.IsTateCupProduct cup) (A B : Rep.{u} k G)
    (a : A.ρ.invariants) (b : B.ρ.invariants) (c : (A ⊗ B).ρ.invariants)
    (hc : (c : (A ⊗ B : Rep.{u} k G)) = (a : A) ⊗ₜ[k] (b : B)) :
    cup A B 0 0 0 (add_zero 0) (Submodule.Quotient.mk a : A.tateH0) (Submodule.Quotient.mk b : B.tateH0)
      = (Submodule.Quotient.mk c : (A ⊗ B).tateH0)
```

### `Rep.bijective_tateDelta_dimShiftUp`

`Thm_Rep_bijective_tateDelta_dimShiftUp` — Dimension shifting: δ is bijective for 0→ A→ Ind Res A→ A'→ 0

```lean
theorem Rep.bijective_tateDelta_dimShiftUp {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (A : Rep.{u} k G) (hA : A.dimShiftUp.ShortExact) (n : ℤ) :
    Function.Bijective (Rep.tateδ hA n).hom
```

### `Rep.bijective_tateDelta_of_isZero`

`Thm_Rep_bijective_tateDelta_of_isZero` — Bijectivity of the Tate connecting map when the middle term vanishes

```lean
theorem Rep.bijective_tateDelta_of_isZero {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (n : ℤ)
    (h₀ : CategoryTheory.Limits.IsZero (X.X₂.tateCohomology n))
    (h₁ : CategoryTheory.Limits.IsZero (X.X₂.tateCohomology (n + 1))) :
    Function.Bijective (Rep.tateδ hX n).hom
```

### `Rep.dimShiftDown_shortExact`

`Thm_Rep_dimShiftDown_shortExact` — The dimension-shifting-down sequence is short exact

```lean
theorem Rep.dimShiftDown_shortExact {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) :
    (A.dimShiftDown).ShortExact
```

### `Rep.dimShiftUp_shortExact`

`Thm_Rep_dimShiftUp_shortExact` — The dimension-shift sequence 0 → A → Ind₁^G A → A_* → 0 is short exact

```lean
theorem Rep.dimShiftUp_shortExact {k G : Type u} [CommRing k] [Group G] [Fintype G] (A : Rep.{u} k G) :
    (A.dimShiftUp).ShortExact
```

### `Rep.exact_map_tateDeltaNeg2`

`Thm_Rep_exact_map_tateDeltaNeg2` — Exactness of H₁(B)→ H₁(C)→ ̂ H⁻¹(A) at H₁(C)

```lean
theorem Rep.exact_map_tateDeltaNeg2 {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) :
    Function.Exact ((groupHomology.functor k G 1).map X.g).hom (Rep.tateδneg2 hX)
```

### `Rep.exact_tateDelta0_map`

`Thm_Rep_exact_tateDelta0_map` — Exactness of ̂ H⁰(C) → H¹(A) → H¹(B)

```lean
theorem Rep.exact_tateDelta0_map {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) :
    Function.Exact (Rep.tateδ₀ hX) ((groupCohomology.functor k G 1).map X.f).hom
```

### `Rep.exact_tateDeltaNeg1_tateH0Map`

`Thm_Rep_exact_tateDeltaNeg1_tateH0Map` — Exactness at ̂ H⁰(A) of the Tate sequence

```lean
theorem Rep.exact_tateDeltaNeg1_tateH0Map {k : Type u} {G : Type v} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{w} k G)} (hX : X.ShortExact) :
    Function.Exact (Rep.tateδneg1 hX) (Rep.tateH0Map X.f)
```

### `Rep.exact_tateDeltaNeg2_tateHneg1Map`

`Thm_Rep_exact_tateDeltaNeg2_tateHneg1Map` — Exactness at ̂ H⁻¹ of the Tate sequence

```lean
theorem Rep.exact_tateDeltaNeg2_tateHneg1Map {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) :
    Function.Exact (Rep.tateδneg2 hX) (Rep.tateHneg1Map X.f)
```

### `Rep.exact_tateDelta_tateMap`

`Thm_Rep_exact_tateDelta_tateMap` — Exactness of the Tate long exact sequence at ̂ Hⁿ⁺¹(X₁)

```lean
theorem Rep.exact_tateDelta_tateMap {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (n : ℤ) :
    Function.Exact (Rep.tateδ hX n).hom (Rep.tateMap X.f (n + 1)).hom
```

### `Rep.exact_tateH0Map_tateDelta0`

`Thm_Rep_exact_tateH0Map_tateDelta0` — Exactness of Tate ̂ H⁰ at the third term

```lean
theorem Rep.exact_tateH0Map_tateDelta0 {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) :
    Function.Exact (Rep.tateH0Map X.g) (Rep.tateδ₀ hX)
```

### `Rep.exact_tateHneg1Map_tateDeltaNeg1`

`Thm_Rep_exact_tateHneg1Map_tateDeltaNeg1` — Exactness of the Tate sequence at ̂ H⁻¹ of the quotient

```lean
theorem Rep.exact_tateHneg1Map_tateDeltaNeg1 {k : Type u} {G : Type v} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{w} k G)} (hX : X.ShortExact) :
    Function.Exact (Rep.tateHneg1Map X.g) (Rep.tateδneg1 hX)
```

### `Rep.exact_tateMap_tateDelta`

`Thm_Rep_exact_tateMap_tateDelta` — Exactness of the Tate sequence at ̂ Hⁿ(X₃)

```lean
theorem Rep.exact_tateMap_tateDelta {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (n : ℤ) :
    Function.Exact (Rep.tateMap X.g n).hom (Rep.tateδ hX n).hom
```

### `Rep.indBotIota_apply`

`Thm_Rep_indBotIota_apply` — The unit A → Ind₁^GRes₁^G A as a sum over G

```lean
theorem Rep.indBotIota_apply {k G : Type u} [CommRing k] [Group G] [Fintype G] (A : Rep.{u} k G) (a : A) :
    (Rep.indBotι A).hom a = ∑ g : G, A.indBotMk g (A.ρ g a)
```

### `Rep.indBotPi_indBotSigma`

`Thm_Rep_indBotPi_indBotSigma` — The augmentation Ind₁^G Res A → A admits a k-linear section

```lean
theorem Rep.indBotPi_indBotSigma {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) (a : A) :
    (Rep.indBotπ A).hom (A.indBotσ a) = a
```

### `Rep.indBot_rho_indBotMk`

`Thm_Rep_indBot_rho_indBotMk` — Action on Ind₁^G Res₁^G A on elementary tensors

```lean
theorem Rep.indBot_rho_indBotMk {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) (g h : G) (a : A) :
    A.indBot.ρ g (A.indBotMk h a) = A.indBotMk (h * g⁻¹) a
```

### `Rep.indBotr_indBotIota`

`Thm_Rep_indBotr_indBotIota` — The unit A → Ind_{mathbf 1}^GResA admits a k-linear retraction

```lean
theorem Rep.indBotr_indBotIota {k G : Type u} [CommRing k] [Group G] [Fintype G] (A : Rep.{u} k G) (a : A) :
    A.indBotr ((Rep.indBotι A).hom a) = a
```

### `Rep.indBotr_indBotMk`

`Thm_Rep_indBotr_indBotMk` — Value of the retraction Ind₁^GRes A → A on generators

```lean
theorem Rep.indBotr_indBotMk {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) (g : G) (a : A) :
    A.indBotr (A.indBotMk g a) = (Finsupp.single g (1 : k)) 1 • a
```

### `Rep.isZero_tateCohomology_indBot`

`Thm_Rep_isZero_tateCohomology_indBot` — Tate cohomology of a module induced from the trivial subgroup vanishes

```lean
theorem Rep.isZero_tateCohomology_indBot {k G : Type u} [CommRing k] [Group G] [Fintype G] (A : Rep.{u} k G) (q : ℤ) :
    CategoryTheory.Limits.IsZero (A.indBot.tateCohomology q)
```

### `Rep.isZero_tateCohomology_indBot_tensor`

`Thm_Rep_isZero_tateCohomology_indBot_tensor` — Vanishing of Tate cohomology of Ind₁^GRes₁ A ⊗ B

```lean
theorem Rep.isZero_tateCohomology_indBot_tensor {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (A B : Rep.{u} k G) (q : ℤ) :
    CategoryTheory.Limits.IsZero ((A.indBot ⊗ B).tateCohomology q)
```

### `Rep.isZero_tateCohomology_tensor_indBot`

`Thm_Rep_isZero_tateCohomology_tensor_indBot` — Tate cohomology of A ⊗ Ind₁^G B vanishes

```lean
theorem Rep.isZero_tateCohomology_tensor_indBot {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (A B : Rep.{u} k G) (q : ℤ) :
    CategoryTheory.Limits.IsZero ((A ⊗ B.indBot).tateCohomology q)
```

### `Rep.nonempty_tateCohomology_iso_of_iso`

`Thm_Rep_nonempty_tateCohomology_iso_of_iso` — Tate cohomology is invariant under isomorphism of representations

```lean
theorem Rep.nonempty_tateCohomology_iso_of_iso {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {A B : Rep.{u} k G} (e : A ≅ B) (q : ℤ) : Nonempty (A.tateCohomology q ≅ B.tateCohomology q)
```

### `Rep.shortExact_dimShiftDown_map_tensorLeft`

`Thm_Rep_shortExact_dimShiftDown_map_tensorLeft` — Tensoring the dimension-shift sequence with A preserves exactness

```lean
theorem Rep.shortExact_dimShiftDown_map_tensorLeft {k G : Type u} [CommRing k] [Group G] (A B : Rep.{u} k G) :
    (B.dimShiftDown.map (MonoidalCategory.tensorLeft A)).ShortExact
```

### `Rep.shortExact_dimShiftDown_map_tensorRight`

`Thm_Rep_shortExact_dimShiftDown_map_tensorRight` — Dimension-shifting sequence remains short exact after -⊗ B

```lean
theorem Rep.shortExact_dimShiftDown_map_tensorRight {k G : Type u} [CommRing k] [Group G] (A B : Rep.{u} k G) :
    (A.dimShiftDown.map (MonoidalCategory.tensorRight B)).ShortExact
```

### `Rep.shortExact_map_tensorLeft_of_splitting`

`Thm_Rep_shortExact_map_tensorLeft_of_splitting` — Left tensoring preserves k-linearly split short exact sequences

```lean
theorem Rep.shortExact_map_tensorLeft_of_splitting {k G : Type u} [CommRing k] [Group G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact)
    (s : X.X₃ →ₗ[k] X.X₂) (hs : ∀ x : X.X₃, X.g.hom (s x) = x) (A : Rep.{u} k G) :
    (X.map (MonoidalCategory.tensorLeft A)).ShortExact
```

### `Rep.shortExact_map_tensorRight_of_splitting`

`Thm_Rep_shortExact_map_tensorRight_of_splitting` — Right tensoring preserves k-split short exact sequences of G-representations

```lean
theorem Rep.shortExact_map_tensorRight_of_splitting {k G : Type u} [CommRing k] [Group G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact)
    (s : X.X₃ →ₗ[k] X.X₂) (hs : ∀ x : X.X₃, X.g.hom (s x) = x) (B : Rep.{u} k G) :
    (X.map (MonoidalCategory.tensorRight B)).ShortExact
```

### `Rep.subsingleton_tateH0_ind_bot`

`Thm_Rep_subsingleton_tateH0_ind_bot` — Tate ̂ H⁰ vanishes for modules induced from bot

```lean
theorem Rep.subsingleton_tateH0_ind_bot {k G : Type*} [CommRing k] [Group G] [Fintype G]
    (A : Rep k (⊥ : Subgroup G)) : Subsingleton (Rep.ind (⊥ : Subgroup G).subtype A).tateH0
```

### `Rep.subsingleton_tateHneg1_ind_bot`

`Thm_Rep_subsingleton_tateHneg1_ind_bot` — Vanishing of ̂ H⁻¹ for modules induced from the trivial subgroup

```lean
theorem Rep.subsingleton_tateHneg1_ind_bot {k G : Type*} [CommRing k] [Group G] [Fintype G]
    (A : Rep k (⊥ : Subgroup G)) : Subsingleton (Rep.ind (⊥ : Subgroup G).subtype A).tateHneg1
```

### `Rep.tateDelta_naturality`

`Thm_Rep_tateDelta_naturality` — Naturality of the Tate connecting maps in all degrees

```lean
theorem Rep.tateDelta_naturality {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X Y : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (hY : Y.ShortExact) (τ : X ⟶ Y) (n : ℤ) :
    Rep.tateδ hX n ≫ Rep.tateMap τ.τ₁ (n + 1) = Rep.tateMap τ.τ₃ n ≫ Rep.tateδ hY n
```

## Submodule (31)

### `Submodule.Quotient.isOfFinAddOrder_of_forall_isMaximal_of_subalgebra_fg`

`Thm_Submodule_Quotient_isOfFinAddOrder_of_forall_isMaximal_of_subalgebra_fg` — Local torsion above I forces torsion in J/γ J

```lean
theorem Submodule.Quotient.isOfFinAddOrder_of_forall_isMaximal_of_subalgebra_fg
    {R J : Type*} [CommRing R] [AddCommGroup J] [Module R J]
    (ρ : R →+* Module.End ℤ J) (hρ : ∀ (t : R) (x : J), t • x = ρ t x)
    (S : Subalgebra ℤ (Module.End ℤ J)) (hS : (Subalgebra.toSubmodule S).FG)
    (hρS : ∀ t, ρ t ∈ S)
    (I γ : Ideal R) (hγ : ∀ t : R, (∃ i ∈ I, ∀ x : J, ((1 + i) * t) • x = 0) → t ∈ γ)
    (z : J ⧸ (γ • (⊤ : Submodule R J)))
    (hz : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → I ≤ 𝔪 → ∃ s ∉ 𝔪, IsOfFinAddOrder (s • z)) :
    IsOfFinAddOrder z
```

### `Submodule.baseChange_inf`

`Thm_Submodule_baseChange_inf` — Base change of subspaces over a field commutes with intersection

```lean
theorem Submodule.baseChange_inf
    {R : Type*} [Field R] (A : Type*) [CommRing A] [Algebra R A]
    {M : Type*} [AddCommGroup M] [Module R M] (p q : Submodule R M) :
    (p ⊓ q).baseChange A = p.baseChange A ⊓ q.baseChange A
```

### `Submodule.eq_span_singleton_of_card_eq_sq`

`Thm_Submodule_eq_span_singleton_of_card_eq_sq` — Proper submodule of an 𝔽ₚ-module of order p² is a line

```lean
theorem Submodule.eq_span_singleton_of_card_eq_sq {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] (hV : Nat.card V = p ^ 2) (N : Submodule (ZMod p) V) (htop : N ≠ ⊤) {v : V} (hv : v ∈ N) (hv0 : v ≠ 0) : N = Submodule.span (ZMod p) {v}
```

### `Submodule.eq_top_of_isAdicComplete_of_fg_of_sup_smul_eq_top`

`Thm_Submodule_eq_top_of_isAdicComplete_of_fg_of_sup_smul_eq_top` — Nakayama's lemma over an I-adically complete ring

```lean
theorem Submodule.eq_top_of_isAdicComplete_of_fg_of_sup_smul_eq_top
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) [IsAdicComplete I A] [IsHausdorff I M]
    (N : Submodule A M) (hN : N.FG) (h : N ⊔ I • ⊤ = ⊤) : N = ⊤
```

### `Submodule.exists_eq_span_singleton_of_forall_bilin_eq_zero_of_isReduced`

`Thm_Submodule_exists_eq_span_singleton_of_forall_bilin_eq_zero_of_isReduced` — Isotropic submodules of a free rank-two module are cyclic

```lean
theorem Submodule.exists_eq_span_singleton_of_forall_bilin_eq_zero_of_isReduced
    {K : Type*} [Field K] {T : Type*} [CommRing T] [Algebra K T] [FiniteDimensional K T] [IsReduced T]
    {V : Type*} [AddCommGroup V] [Module K V] [Module T V] [IsScalarTower K T V]
    (e : V ≃ₗ[T] (Fin 2 → T))
    (B : V →ₗ[K] V →ₗ[K] K)
    (hBl : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hBt : ∀ (t : T) (x y : V), B (t • x) y = B x (t • y))
    (N : Submodule T V) (hN : ∀ x ∈ N, ∀ y ∈ N, B x y = 0) :
    ∃ g : V, N = Submodule.span T {g}
```

### `Submodule.exists_finset_card_eq_finrank_forall_eq_zero_of_forall_exists_apply_ne_zero`

`Thm_Submodule_exists_finset_card_eq_finrank_forall_eq_zero_of_forall_exists_apply_ne_zero` — Choosing dim D indices cutting out 0 in D

```lean
theorem Submodule.exists_finset_card_eq_finrank_forall_eq_zero_of_forall_exists_apply_ne_zero
    {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    {ι : Type*} {W : ι → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)]
    (f : ∀ i, V →ₗ[k] W i) (D : Submodule k V) [FiniteDimensional k D]
    (good : Set ι)
    (hpad : ∀ T : Finset ι, ∃ i ∈ good, i ∉ T)
    (hkill : ∀ ψ ∈ D, ψ ≠ 0 → ∀ T : Finset ι, ∃ i ∈ good, i ∉ T ∧ f i ψ ≠ 0)
    (T₀ : Finset ι) :
    ∃ Q : Finset ι, ↑Q ⊆ good ∧ Disjoint Q T₀ ∧ Q.card = Module.finrank k D ∧
      ∀ ψ ∈ D, (∀ i ∈ Q, f i ψ = 0) → ψ = 0
```

### `Submodule.exists_generator_of_perfectPairing_antisymm_of_quotient_dual_of_finrank_eq_two_mul`

`Thm_Submodule_exists_generator_of_perfectPairing_antisymm_of_quotient_dual_of_finrank_eq_two_mul` — A generator of E modulo rP over A

```lean
theorem Submodule.exists_generator_of_perfectPairing_antisymm_of_quotient_dual_of_finrank_eq_two_mul
    {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪] [CharZero 𝒪]
    {A : Type*} [CommRing A] [Algebra 𝒪 A] [Module.Finite 𝒪 A] [Module.Free 𝒪 A]
    {P : Type*} [AddCommGroup P] [Module A P] [Module 𝒪 P] [IsScalarTower 𝒪 A P]
    [Module.Finite 𝒪 P] [Module.Free 𝒪 P]
    (hrank : Module.finrank 𝒪 P = 2 * Module.finrank 𝒪 A)
    (β : P →ₗ[𝒪] P →ₗ[𝒪] 𝒪) (hβ : Function.Bijective β)
    (hanti : ∀ v w, β v w = - β w v) (hbal : ∀ (a : A) (v w : P), β (a • v) w = β v (a • w))
    (r : 𝒪) (hr : r ∈ IsLocalRing.maximalIdeal 𝒪) (hr0 : r ≠ 0)
    (E : Submodule A P) (hrE : ∀ w : P, r • w ∈ E)
    (Φ : P →ₗ[𝒪] (A →ₗ[𝒪] 𝒪 ⧸ Ideal.span {r})) (hΦs : Function.Surjective Φ)
    (hΦk : ∀ v, Φ v = 0 ↔ v ∈ E) (hΦa : ∀ (a : A) (v : P) (t : A), Φ (a • v) t = Φ v (a * t)) :
    ∃ x ∈ E, (∀ v ∈ E, ∃ (a : A) (w : P), v = a • x + r • w) ∧
      (∀ a : A, (∃ w : P, a • x = r • w) ↔ ∃ b : A, a = algebraMap 𝒪 A r * b)
```

### `Submodule.exists_injective_linearMap_baseChange_torsionBySet_range_eq_eigenspace`

`Thm_Submodule_exists_injective_linearMap_baseChange_torsionBySet_range_eq_eigenspace` — Base change k⊗_{A/𝔪}J[𝔪] as ι-eigenspace in k⊗_ℤJ[I]

```lean
theorem Submodule.exists_injective_linearMap_baseChange_torsionBySet_range_eq_eigenspace
    {A : Type*} [CommRing A] {J : Type*} [AddCommGroup J] [Module A J]
    {k : Type*} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (I 𝔪 : Ideal A) [𝔪.IsMaximal] (hI : I ≤ 𝔪) (hp : (p : A) ∈ I)
    (hfin : Finite ↥(Submodule.torsionBySet A J (I : Set A)))
    (ι : A ⧸ 𝔪 →+* k) :
    letI := ι.toAlgebra
    ∃ j : k ⊗[A ⧸ 𝔪] ↥(Submodule.torsionBySet A J (𝔪 : Set A)) →ₗ[k]
        k ⊗[ℤ] ↥(Submodule.torsionBySet A J (I : Set A)),
      Function.Injective j ∧
      ∀ w : k ⊗[ℤ] ↥(Submodule.torsionBySet A J (I : Set A)),
        w ∈ LinearMap.range j ↔
          ∀ a : A,
            ((DistribSMul.toLinearMap ℤ ↥(Submodule.torsionBySet A J (I : Set A)) a).baseChange k) w =
              ι (Ideal.Quotient.mk 𝔪 a) • w
```

### `Submodule.exists_invertible_quotient_and_forall_localized_eq`

`Thm_Submodule_exists_invertible_quotient_and_forall_localized_eq` — Gluing local submodules with invertible quotients

```lean
theorem Submodule.exists_invertible_quotient_and_forall_localized_eq
    {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V] [Module.FinitePresentation R V]
    (Vₚ : PrimeSpectrum R → Type) [∀ x, AddCommGroup (Vₚ x)] [∀ x, Module R (Vₚ x)]
    [∀ x, Module (Localization.AtPrime x.asIdeal) (Vₚ x)]
    [∀ x, IsScalarTower R (Localization.AtPrime x.asIdeal) (Vₚ x)]
    (f : ∀ x, V →ₗ[R] Vₚ x) [∀ x, IsLocalizedModule x.asIdeal.primeCompl (f x)]
    (Λ : ∀ x, Submodule (Localization.AtPrime x.asIdeal) (Vₚ x))
    (hinv : ∀ x, Module.Invertible (Localization.AtPrime x.asIdeal) (Vₚ x ⧸ Λ x))
    (hloc : ∀ x : PrimeSpectrum R, ∃ r : R, r ∉ x.asIdeal ∧ ∃ N : Submodule R V, N.FG ∧
      ∀ y : PrimeSpectrum R, r ∉ y.asIdeal →
        Submodule.localized' (Localization.AtPrime y.asIdeal) y.asIdeal.primeCompl (f y) N = Λ y) :
    ∃ N : Submodule R V, Module.Invertible R (V ⧸ N) ∧
      ∀ x : PrimeSpectrum R, Submodule.localized' (Localization.AtPrime x.asIdeal) x.asIdeal.primeCompl (f x) N = Λ x
```

### `Submodule.exists_isPerfPair_dotProduct_of_saturated`

`Thm_Submodule_exists_isPerfPair_dotProduct_of_saturated` — A perfect pairing from orthogonal saturated sublattices of ℤ^ι

```lean
theorem Submodule.exists_isPerfPair_dotProduct_of_saturated {ι : Type*} [Fintype ι]
    {L : Type*} [AddCommGroup L] [Module ℤ L]
    (B E : Submodule ℤ (ι → ℤ))
    (hB : ∀ (n : ℤ) (v : ι → ℤ), n ≠ 0 → n • v ∈ B → v ∈ B)
    (hE : ∀ (n : ℤ) (v : ι → ℤ), n ≠ 0 → n • v ∈ E → v ∈ E)
    (hBE : ∀ b ∈ B, ∀ e ∈ E, b ⬝ᵥ e = 0)
    (f X : L →ₗ[ℤ] (ι → ℤ))
    (hf : ∀ y, ∀ e ∈ E, f y ⬝ᵥ e = 0) (hX : ∀ x, ∀ b ∈ B, X x ⬝ᵥ b = 0)
    (hfB : ∀ y, f y ∈ B → y = 0) (hXE : ∀ x, X x ∈ E → x = 0)
    (hZ : ∀ v : ι → ℤ, (∀ e ∈ E, v ⬝ᵥ e = 0) → ∃ y, v - f y ∈ B)
    (hsat : ∀ (n : ℤ) (v : ι → ℤ), n ≠ 0 → (∃ x, n • v - X x ∈ E) → ∃ x, v - X x ∈ E) :
    ∃ p : L →ₗ[ℤ] L →ₗ[ℤ] ℤ, (∀ x y, p x y = X x ⬝ᵥ f y) ∧ p.IsPerfPair
```

### `Submodule.exists_mem_forall_of_finset_of_directed`

`Thm_Submodule_exists_mem_forall_of_finset_of_directed` — Finite subsets of a directed family of submodules

```lean
theorem Submodule.exists_mem_forall_of_finset_of_directed {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {ι : Type*} [Nonempty ι] (T : ι → Submodule k V) (hdir : Directed (· ≤ ·) T)
    (s : Finset V) (hs : ∀ x ∈ s, ∃ i, x ∈ T i) : ∃ j, ∀ x ∈ s, x ∈ T j
```

### `Submodule.exists_smul_eq_self_and_smul_mem_torsionBySet_of_torsionBySet_pow_succ_eq`

`Thm_Submodule_exists_smul_eq_self_and_smul_mem_torsionBySet_of_torsionBySet_pow_succ_eq` — A ring element projecting a finite module onto stabilised I^N-torsion

```lean
theorem Submodule.exists_smul_eq_self_and_smul_mem_torsionBySet_of_torsionBySet_pow_succ_eq
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Finite M]
    (I : Ideal R) (N : ℕ)
    (hN : Submodule.torsionBySet R M (↑(I ^ (N + 1)) : Set R) = Submodule.torsionBySet R M (↑(I ^ N) : Set R)) :
    ∃ t : R, (∀ v ∈ Submodule.torsionBySet R M (↑(I ^ N) : Set R), t • v = v) ∧
      ∀ m : M, t • m ∈ Submodule.torsionBySet R M (↑(I ^ N) : Set R)
```

### `Submodule.finiteDimensional_and_finrank_le_of_forall_orthonormal_card_le_of_definite`

`Thm_Submodule_finiteDimensional_and_finrank_le_of_forall_orthonormal_card_le_of_definite` — Bounded orthonormal families force dim V ≤ D

```lean
theorem Submodule.finiteDimensional_and_finrank_le_of_forall_orthonormal_card_le_of_definite
    {E : Type*} [AddCommGroup E] [Module ℂ E] (V : Submodule ℂ E)
    (B : E → E → ℂ)
    (hadd : ∀ x y z, B (x + y) z = B x z + B y z)
    (hsmul : ∀ (c : ℂ) (x y : E), B (c • x) y = c * B x y)
    (hsymm : ∀ x y, B y x = conj (B x y))
    (hpos : ∀ x ∈ V, 0 ≤ (B x x).re)
    (hdef : ∀ x ∈ V, B x x = 0 → x = 0)
    (D : ℕ) (hD : ∀ (n : ℕ) (e : Fin n → E), (∀ i, e i ∈ V) →
      (∀ i j, B (e i) (e j) = if i = j then 1 else 0) → n ≤ D) :
    FiniteDimensional ℂ V ∧ Module.finrank ℂ V ≤ D
```

### `Submodule.finiteDimensional_of_isCompactOperator_of_forall_apply_eq`

`Thm_Submodule_finiteDimensional_of_isCompactOperator_of_forall_apply_eq` — Subspaces fixed pointwise by a compact operator are finite-dimensional

```lean
theorem Submodule.finiteDimensional_of_isCompactOperator_of_forall_apply_eq
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {T : E →L[𝕜] E} (hT : IsCompactOperator T) (V : Submodule 𝕜 E) (hV : ∀ v ∈ V, T v = v) :
    FiniteDimensional 𝕜 ↥V
```

### `Submodule.finite_torsionBy_pow_of_finite_torsionBy`

`Thm_Submodule_finite_torsionBy_pow_of_finite_torsionBy` — Finite a-torsion implies finite a^k-torsion

```lean
theorem Submodule.finite_torsionBy_pow_of_finite_torsionBy
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (a : R)
    (h : Finite (Submodule.torsionBy R M a)) (k : ℕ) :
    Finite (Submodule.torsionBy R M (a ^ k))
```

### `Submodule.finrank_baseChange_eq_finrank_of_isCompl_of_eq_span_image`

`Thm_Submodule_finrank_baseChange_eq_finrank_of_isCompl_of_eq_span_image` — Base change preserves dimensions of complementary lattices in S²

```lean
theorem Submodule.finrank_baseChange_eq_finrank_of_isCompl_of_eq_span_image
    {S : Type} [CommRing S] {K : Type} [Field K] [Algebra S K]
    (L₀ L₁ : Submodule S (Fin 2 → S)) (hL : IsCompl L₀ L₁)
    (M₀ M₁ : Submodule K (Fin 2 → K)) (hM : IsCompl M₀ M₁)
    (h₀ : M₀ = Submodule.span K ((fun v : Fin 2 → S => ⇑(algebraMap S K) ∘ v) '' (L₀ : Set (Fin 2 → S))))
    (h₁ : M₁ = Submodule.span K ((fun v : Fin 2 → S => ⇑(algebraMap S K) ∘ v) '' (L₁ : Set (Fin 2 → S)))) :
    Module.finrank K (K ⊗[S] ↥L₀) = Module.finrank K ↥M₀ ∧ Module.finrank K (K ⊗[S] ↥L₁) = Module.finrank K ↥M₁
```

### `Submodule.finrank_comap_eq_finrank_ker_add_finrank_range_inf`

`Thm_Submodule_finrank_comap_eq_finrank_ker_add_finrank_range_inf` — Dimension of a preimage subspace: rank–nullity for `comap`

```lean
theorem Submodule.finrank_comap_eq_finrank_ker_add_finrank_range_inf
    {k : Type*} [Field k] {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (f : V →ₗ[k] W) (N : Submodule k W) [FiniteDimensional k (N.comap f)] :
    finrank k (N.comap f)
      = finrank k (LinearMap.ker f) + finrank k (LinearMap.range f ⊓ N : Submodule k W)
```

### `Submodule.finrank_pi_univ_eq_sum`

`Thm_Submodule_finrank_pi_univ_eq_sum` — Dimension of a product of subspaces

```lean
theorem Submodule.finrank_pi_univ_eq_sum
    {k : Type*} [Field k] {ι : Type*} [Fintype ι] {Φ : ι → Type*}
    [∀ v, AddCommGroup (Φ v)] [∀ v, Module k (Φ v)]
    (L : ∀ v, Submodule k (Φ v)) [∀ v, FiniteDimensional k (L v)] :
    finrank k (Submodule.pi Set.univ L) = ∑ v, finrank k (L v)
```

### `Submodule.free_of_free_of_isPrincipalIdealRing`

`Thm_Submodule_free_of_free_of_isPrincipalIdealRing` — Submodules of free modules over a principal ideal domain are free

```lean
theorem Submodule.free_of_free_of_isPrincipalIdealRing {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Free R M] (N : Submodule R M) :
    Module.Free R N
```

### `Submodule.iInf_sup_pow_smul_top_eq_of_le_jacobson`

`Thm_Submodule_iInf_sup_pow_smul_top_eq_of_le_jacobson` — Submodules of finite modules are I-adically closed

```lean
theorem Submodule.iInf_sup_pow_smul_top_eq_of_le_jacobson
    {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥)
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] (N : Submodule R M) :
    ⨅ n : ℕ, N ⊔ I ^ n • (⊤ : Submodule R M) = N
```

### `Submodule.mem_ideal_smul_top_of_smul_mem_of_free_of_noZeroSMulDivisors_quotient`

`Thm_Submodule_mem_ideal_smul_top_of_smul_mem_of_free_of_noZeroSMulDivisors_quotient` — Saturation of I· M in a free module

```lean
theorem Submodule.mem_ideal_smul_top_of_smul_mem_of_free_of_noZeroSMulDivisors_quotient
    {𝒪 : Type*} [CommRing 𝒪] {R : Type*} [CommRing R] [Algebra 𝒪 R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module 𝒪 M] [IsScalarTower 𝒪 R M] [Module.Free R M]
    (I : Ideal R) [NoZeroSMulDivisors 𝒪 (R ⧸ I)]
    (a : 𝒪) (ha : a ≠ 0) (m : M) (h : a • m ∈ (I • ⊤ : Submodule R M)) :
    m ∈ (I • ⊤ : Submodule R M)
```

### `Submodule.mem_of_forall_exists_sub_mem_pow_smul_top`

`Thm_Submodule_mem_of_forall_exists_sub_mem_pow_smul_top` — Submodules of finite ℤₚ-modules are p-adically closed

```lean
theorem Submodule.mem_of_forall_exists_sub_mem_pow_smul_top
    {p : ℕ} [Fact p.Prime] {M : Type*} [AddCommGroup M] [Module ℤ_[p] M] [Module.Finite ℤ_[p] M]
    (N : Submodule ℤ_[p] M) (x : M)
    (h : ∀ n : ℕ, ∃ a ∈ N, x - a ∈ ((p : ℤ_[p]) ^ n • (⊤ : Submodule ℤ_[p] M))) : x ∈ N
```

### `Submodule.mem_of_forall_prime_exists_smul_mem`

`Thm_Submodule_mem_of_forall_prime_exists_smul_mem` — Membership in a ℤ-submodule from prime-by-prime multipliers

```lean
theorem Submodule.mem_of_forall_prime_exists_smul_mem
    {V : Type*} [AddCommGroup V] (M : Submodule ℤ V) (x : V)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ∃ s : ℤ, ¬ (ℓ : ℤ) ∣ s ∧ s • x ∈ M) : x ∈ M
```

### `Submodule.mem_smul_top_of_isLocalizedModule_primeCompl_of_isPrime_span_singleton`

`Thm_Submodule_mem_smul_top_of_isLocalizedModule_primeCompl_of_isPrime_span_singleton` — Divisibility by a prime element descends from a localisation

```lean
theorem Submodule.mem_smul_top_of_isLocalizedModule_primeCompl_of_isPrime_span_singleton
    {A : Type*} [CommRing A] {M N : Type*} [AddCommGroup M] [Module A M] [Module.Projective A M]
    [AddCommGroup N] [Module A N]
    (ϖ : A) (hϖ : (Ideal.span {ϖ} : Ideal A).IsPrime)
    (𝔭 : Ideal A) [𝔭.IsPrime] (h𝔭 : ϖ ∈ 𝔭)
    (f : M →ₗ[A] N) [IsLocalizedModule 𝔭.primeCompl f]
    (m : M) (hm : f m ∈ ϖ • (⊤ : Submodule A N)) :
    m ∈ ϖ • (⊤ : Submodule A M)
```

### `Submodule.moduleFinite_adjoin_eigenvalues_of_map_le_of_span_eq_top`

`Thm_Submodule_moduleFinite_adjoin_eigenvalues_of_map_le_of_span_eq_top` — Eigenvalues on a lattice-preserving family are integral

```lean
theorem Submodule.moduleFinite_adjoin_eigenvalues_of_map_le_of_span_eq_top
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (Λ : Submodule ℤ V) (hΛfg : Λ.FG) (hΛspan : Submodule.span ℂ (Λ : Set V) = ⊤)
    {J : Type*} (S : J → V →ₗ[ℂ] V) (hS : ∀ (j : J), ∀ x ∈ Λ, S j x ∈ Λ)
    (lam : J → ℂ) (v : V) (hv0 : v ≠ 0) (hv : ∀ j : J, S j v = lam j • v) :
    Module.Finite ℤ (Algebra.adjoin ℤ (Set.range lam))
```

### `Submodule.natCard_quotient_eq_natCard_quotient_span_det`

`Thm_Submodule_natCard_quotient_eq_natCard_quotient_span_det` — Index of a full-rank submodule equals the determinant ideal's index

```lean
theorem Submodule.natCard_quotient_eq_natCard_quotient_span_det
    {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {M : Type} [AddCommGroup M] [Module R M]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R M) (N : Submodule R M) (bN : Module.Basis ι R N) :
    Nat.card (M ⧸ N) = Nat.card (R ⧸ Ideal.span ({b.det (fun i => (bN i : M))} : Set R))
```

### `Submodule.natCard_quotient_pow_smul_top_linear_of_finite_quotient`

`Thm_Submodule_natCard_quotient_pow_smul_top_linear_of_finite_quotient` — Linear growth of #(X/I^mX) in powers of q

```lean
theorem Submodule.natCard_quotient_pow_smul_top_linear_of_finite_quotient
    (R : Type*) [CommRing R] [IsNoetherianRing R] (q : ℕ) [Fact q.Prime]
    (hRq : Finite (R ⧸ Ideal.span {(q : R)}))
    (I : Ideal R) (hqI : (q : R) ∈ I)
    (X : Type*) [AddCommGroup X] [Module R X] [Module.Finite R X] :
    ∃ e C : ℕ, ∀ m : ℕ,
      Nat.card (X ⧸ (I ^ m • (⊤ : Submodule R X))) ≤ q ^ (m * e + C) ∧
        q ^ (m * e) ≤ Nat.card (X ⧸ (I ^ m • (⊤ : Submodule R X))) * q ^ C
```

### `Submodule.natCard_torsionBySet_pow_linear_of_finite_torsionBy`

`Thm_Submodule_natCard_torsionBySet_pow_linear_of_finite_torsionBy` — Linear growth of I^m-torsion when q-torsion is finite

```lean
theorem Submodule.natCard_torsionBySet_pow_linear_of_finite_torsionBy
    (T : Type*) [CommRing T] (G : Type*) [AddCommGroup G] [Module T G]
    (q : ℕ) [Fact q.Prime] (hfin : Finite ↥(Submodule.torsionBy ℤ G (q : ℤ)))
    (I : Ideal T) (hqI : (q : T) ∈ I) :
    ∃ e C : ℕ, ∀ m : ℕ,
      Nat.card ↥(Submodule.torsionBySet T G (↑(I ^ m) : Set T)) ≤ q ^ (m * e + C) ∧
        q ^ (m * e) ≤ Nat.card ↥(Submodule.torsionBySet T G (↑(I ^ m) : Set T)) * q ^ C
```

### `Submodule.natCard_torsionBy_quotient_eq_pow_finrank`

`Thm_Submodule_natCard_torsionBy_quotient_eq_pow_finrank` — Torsion of a quotient by a lattice: #(V/L)[n]=n^{rk L}

```lean
theorem Submodule.natCard_torsionBy_quotient_eq_pow_finrank
    {K : Type*} [DivisionRing K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V]
    (L : Submodule ℤ V) [Module.Free ℤ L] [Module.Finite ℤ L]
    (n : ℕ) (hn : n ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (V ⧸ L) (n : ℤ)) = n ^ Module.finrank ℤ L
```

### `Submodule.span_fixedPoints_semilinear_eq_top`

`Thm_Submodule_span_fixedPoints_semilinear_eq_top` — Fixed vectors of a semilinear Galois action span

```lean
theorem Submodule.span_fixedPoints_semilinear_eq_top
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (V : Type*) [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V]
    (ρ : (L ≃ₐ[K] L) → V →+ V)
    (hρ_smul : ∀ (σ : L ≃ₐ[K] L) (a : L) (v : V), ρ σ (a • v) = σ a • ρ σ v)
    (hρ_one : ∀ v : V, ρ 1 v = v)
    (hρ_mul : ∀ (σ τ : L ≃ₐ[K] L) (v : V), ρ (σ * τ) v = ρ σ (ρ τ v)) :
    Submodule.span L {v : V | ∀ σ : L ≃ₐ[K] L, ρ σ v = v} = ⊤
```

### `Submodule.stableLine_fixed_or_cofixed_of_absorbing`

`Thm_Submodule_stableLine_fixed_or_cofixed_of_absorbing` — Stable line in an mathbb Fₚ-plane: fixed or cofixed

```lean
theorem Submodule.stableLine_fixed_or_cofixed_of_absorbing {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] (hV : Nat.card V = p ^ 2) {G : Type*} [SMul G V] (S : Set G) (N : Submodule (ZMod p) V) (hN : ∀ g ∈ S, ∀ x ∈ N, g • x ∈ N) (hbot : N ≠ ⊥) (htop : N ≠ ⊤) (M : Submodule (ZMod p) V) (hM : M ≠ ⊤) (habs : ∀ g ∈ S, ∀ y : V, g • y - y ∈ M) : (∀ g ∈ S, ∀ x ∈ N, g • x = x) ∨ (∀ g ∈ S, ∀ y : V, g • y - y ∈ N)
```

## HaarQuotient (20)

### `HaarQuotient.exists_forall_integrable_comp_mul_right_iff_and_integral_eq_smul`

`Thm_HaarQuotient_exists_forall_integrable_comp_mul_right_iff_and_integral_eq_smul` — Right translation scales H-invariant Bochner integrals

```lean
theorem HaarQuotient.exists_forall_integrable_comp_mul_right_iff_and_integral_eq_smul
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (μ : Measure G) [μ.IsHaarMeasure]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant] (x : G) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ (Φ : G → E), Measurable Φ → (∀ (h : H) (g : G), Φ ((h : G) * g) = Φ g) →
      (Integrable (fun g => Φ (g * x)) (μ.withDensity (HaarQuotient.density H μH)) ↔
        Integrable Φ (μ.withDensity (HaarQuotient.density H μH))) ∧
      (∫ g, Φ (g * x) ∂(μ.withDensity (HaarQuotient.density H μH))) =
        (c : ℝ) • ∫ g, Φ g ∂(μ.withDensity (HaarQuotient.density H μH))
```

### `HaarQuotient.exists_forall_integral_withDensity_density_eq_smul_of_isHaarMeasure`

`Thm_HaarQuotient_exists_forall_integral_withDensity_density_eq_smul_of_isHaarMeasure` — Rescaling of quotient integrals under change of Haar normalisations

```lean
theorem HaarQuotient.exists_forall_integral_withDensity_density_eq_smul_of_isHaarMeasure
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μ μ' : Measure G) [μ.IsHaarMeasure] [μ'.IsHaarMeasure]
    (μH μH' : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    [μH'.IsHaarMeasure] [μH'.IsMulRightInvariant] :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ (Φ : G → E), (∀ (h : H) (g : G), Φ ((h : G) * g) = Φ g) →
      (∫ g, Φ g ∂(μ'.withDensity (HaarQuotient.density H μH'))) =
        (c : ℝ) • ∫ g, Φ g ∂(μ.withDensity (HaarQuotient.density H μH))
```

### `HaarQuotient.exists_lintegral_comp_mul_right_withDensity_density_eq_mul`

`Thm_HaarQuotient_exists_lintegral_comp_mul_right_withDensity_density_eq_mul` — Right translation scales the density-weighted Haar integral

```lean
theorem HaarQuotient.exists_lintegral_comp_mul_right_withDensity_density_eq_mul
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant] (x : G) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ (Φ : G → ℝ≥0∞), Measurable Φ → (∀ (h : H) (g : G), Φ ((h : G) * g) = Φ g) →
      ∫⁻ g, Φ (g * x) ∂(μ.withDensity (HaarQuotient.density H μH)) =
        c * ∫⁻ g, Φ g ∂(μ.withDensity (HaarQuotient.density H μH))
```

### `HaarQuotient.integrable_and_integral_mul_comp_out_eq_tsum_mul_setIntegral_of_mem_normalizer`

`Thm_HaarQuotient_integrable_and_integral_mul_comp_out_eq_tsum_mul_setIntegral_of_mem_normalizer` — Complex shell-peeling identity for integrals over Hbackslash G

```lean
theorem HaarQuotient.integrable_and_integral_mul_comp_out_eq_tsum_mul_setIntegral_of_mem_normalizer
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (b : G) (hb : ∀ y : G, y ∈ H ↔ b * y * b⁻¹ ∈ H) (D : ℝ≥0) (hD₀ : D ≠ 0)
    (hbD : ∀ F : H → ℝ≥0∞, Measurable F →
      ∫⁻ x, F ⟨b * (x : G) * b⁻¹, (hb (x : G)).mp x.2⟩ ∂μH = (D : ℝ≥0∞) * ∫⁻ x, F x ∂μH)
    (m : G → ℤ) (hm : Measurable m) (hmH : ∀ x ∈ H, ∀ g : G, m (x * g) = m g)
    (hmb : ∀ g : G, m (b * g) = m g + 1)
    (h : G → ℂ) (hh : Measurable h) (hhH : ∀ x ∈ H, ∀ g : G, h (x * g) = h g)
    (hhb : ∀ g : G, h (b * g) = h g)
    (hint : IntegrableOn (fun q : MulAction.orbitRel.Quotient H G => h q.out)
      {q : MulAction.orbitRel.Quotient H G | m q.out = 0} (HaarQuotient.measure μ H μH))
    (Φ : ℤ → ℂ) (hΦ : Summable fun n : ℤ => (D : ℝ) ^ n * ‖Φ n‖) :
    Integrable (fun q : MulAction.orbitRel.Quotient H G => h q.out * Φ (m q.out)) (HaarQuotient.measure μ H μH) ∧
    (∫ q, h q.out * Φ (m q.out) ∂(HaarQuotient.measure μ H μH)) =
      (∑' n : ℤ, ((D : ℝ) : ℂ) ^ n * Φ n) *
        ∫ q in {q : MulAction.orbitRel.Quotient H G | m q.out = 0}, h q.out ∂(HaarQuotient.measure μ H μH)
```

### `HaarQuotient.integrable_integral_comp_mul_out_and_integral_eq_integral_integral_comp_mul_out`

`Thm_HaarQuotient_integrable_integral_comp_mul_out_and_integral_eq_integral_integral_comp_mul_out` — Quotient integral formula for complex integrable functions

```lean
theorem HaarQuotient.integrable_integral_comp_mul_out_and_integral_eq_integral_integral_comp_mul_out
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (f : G → ℂ) (hf : Measurable f) (hfi : ∫⁻ g, ‖f g‖ₑ ∂μ < ∞) :
    (∀ᵐ q ∂(HaarQuotient.measure μ H μH), Integrable (fun x : H => f ((x : G) * q.out)) μH) ∧
    Integrable (fun q : MulAction.orbitRel.Quotient H G => (∫ x : H, f ((x : G) * q.out) ∂μH))
      (HaarQuotient.measure μ H μH) ∧
    ∫ g, f g ∂μ = ∫ q, (∫ x : H, f ((x : G) * q.out) ∂μH) ∂(HaarQuotient.measure μ H μH)
```

### `HaarQuotient.integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out`

`Thm_HaarQuotient_integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out` — Bochner quotient integral formula over a fundamental domain

```lean
theorem HaarQuotient.integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (Γ : Subgroup G) (hΓ : Γ ≤ H) [Countable Γ]
    (f : G → ℂ) (hf : Measurable f) (hfΓ : ∀ γ ∈ Γ, ∀ g : G, f (γ * g) = f g)
    (S : Set G) (hS : IsFundamentalDomain Γ S μ)
    (T : Set H) (hT : IsFundamentalDomain (Γ.subgroupOf H) T μH)
    (hfin : ∫⁻ g in S, ‖f g‖ₑ ∂μ < ∞) :
    (∀ᵐ q ∂(HaarQuotient.measure μ H μH), IntegrableOn (fun x : H => f ((x : G) * q.out)) T μH) ∧
    Integrable (fun q : MulAction.orbitRel.Quotient H G => ∫ x in T, f ((x : G) * q.out) ∂μH)
      (HaarQuotient.measure μ H μH) ∧
    ∫ g in S, f g ∂μ =
      ∫ q, (∫ x in T, f ((x : G) * q.out) ∂μH) ∂(HaarQuotient.measure μ H μH)
```

### `HaarQuotient.integral_comp_mulEquiv_withDensity_density_eq_of_involutive`

`Thm_HaarQuotient_integral_comp_mulEquiv_withDensity_density_eq_of_involutive` — Involutive automorphism preserving H fixes the quotient integral

```lean
theorem HaarQuotient.integral_comp_mulEquiv_withDensity_density_eq_of_involutive
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μ : Measure G) [μ.IsHaarMeasure] (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (φ : G ≃* G) (hφc : Continuous φ) (hφφ : ∀ g : G, φ (φ g) = g) (hφH : ∀ g : G, φ g ∈ H ↔ g ∈ H) :
    ∀ (Φ : G → E), (∀ (h : H) (g : G), Φ ((h : G) * g) = Φ g) →
      (∫ g, Φ (φ g) ∂(μ.withDensity (HaarQuotient.density H μH))) =
        ∫ g, Φ g ∂(μ.withDensity (HaarQuotient.density H μH))
```

### `HaarQuotient.lintegral_comp_inv_mul_out_eq_mul_lintegral_of_mem_normalizer`

`Thm_HaarQuotient_lintegral_comp_inv_mul_out_eq_mul_lintegral_of_mem_normalizer` — Relative invariance of the quotient measure under the normaliser

```lean
theorem HaarQuotient.lintegral_comp_inv_mul_out_eq_mul_lintegral_of_mem_normalizer
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (b : G) (hb : ∀ y : G, y ∈ H ↔ b * y * b⁻¹ ∈ H) (D : ℝ≥0∞)
    (hD : ∀ F : H → ℝ≥0∞, Measurable F →
      ∫⁻ x, F ⟨b * (x : G) * b⁻¹, (hb (x : G)).mp x.2⟩ ∂μH = D * ∫⁻ x, F x ∂μH)
    (f : G → ℝ≥0∞) (hf : Measurable f) (hfH : ∀ x ∈ H, ∀ g : G, f (x * g) = f g) :
    ∫⁻ q, f (b⁻¹ * q.out) ∂(HaarQuotient.measure μ H μH) =
      D * ∫⁻ q, f q.out ∂(HaarQuotient.measure μ H μH)
```

### `HaarQuotient.lintegral_comp_out_mul_eq_of_map_mul_right_eq`

`Thm_HaarQuotient_lintegral_comp_out_mul_eq_of_map_mul_right_eq` — Right translations preserving μ preserve quotient integrals on Hbackslash G

```lean
theorem HaarQuotient.lintegral_comp_out_mul_eq_of_map_mul_right_eq
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (f : G → ENNReal) (hfH : ∀ x ∈ H, ∀ g : G, f (x * g) = f g) (k : G)
    (hμk : Measure.map (· * k) μ = μ) :
    ∫⁻ q : MulAction.orbitRel.Quotient H G, f (q.out * k) ∂(HaarQuotient.measure μ H μH) =
      ∫⁻ q : MulAction.orbitRel.Quotient H G, f q.out ∂(HaarQuotient.measure μ H μH)
```

### `HaarQuotient.lintegral_density_mul_comp_mul_right_eq_of_map_mul_right_eq`

`Thm_HaarQuotient_lintegral_density_mul_comp_mul_right_eq_of_map_mul_right_eq` — Right translation invariance of the density-weighted integral

```lean
theorem HaarQuotient.lintegral_density_mul_comp_mul_right_eq_of_map_mul_right_eq
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant] [SFinite μH]
    (f : G → ENNReal) (hf : Measurable f) (hfH : ∀ x ∈ H, ∀ g : G, f (x * g) = f g) (h : G)
    (hμh : Measure.map (· * h) μ = μ) :
    ∫⁻ g, HaarQuotient.density H μH g * f (g * h) ∂μ = ∫⁻ g, HaarQuotient.density H μH g * f g ∂μ
```

### `HaarQuotient.lintegral_density_mul_eq_one`

`Thm_HaarQuotient_lintegral_density_mul_eq_one` — Bruhat density integrates to one over each coset

```lean
theorem HaarQuotient.lintegral_density_mul_eq_one
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant] (g : G) :
    ∫⁻ x : H, HaarQuotient.density H μH ((x : G) * g) ∂μH = 1
```

### `HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out`

`Thm_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out` — Unfolding a left invariant measure along a closed unimodular subgroup

```lean
theorem HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (f : G → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ g, f g ∂μ = ∫⁻ q, (∫⁻ x, f ((x : G) * q.out) ∂μH) ∂(HaarQuotient.measure μ H μH)
```

### `HaarQuotient.lintegral_indicator_coe_mul_coe_withDensity_density_eq_div_and_lt_top`

`Thm_HaarQuotient_lintegral_indicator_coe_mul_coe_withDensity_density_eq_div_and_lt_top` — Measure of H· K for the pinned orbit density

```lean
theorem HaarQuotient.lintegral_indicator_coe_mul_coe_withDensity_density_eq_div_and_lt_top
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (K : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) :
    ∫⁻ g, ((H : Set G) * (K : Set G)).indicator (fun _ => (1 : ℝ≥0∞)) g ∂(μ.withDensity (HaarQuotient.density H μH)) =
        μ K / μH (((↑) : H → G) ⁻¹' (K : Set G)) ∧
      ∫⁻ g, ((H : Set G) * (K : Set G)).indicator (fun _ => (1 : ℝ≥0∞)) g ∂(μ.withDensity (HaarQuotient.density H μH)) < ⊤
```

### `HaarQuotient.lintegral_mul_comp_out_eq_tsum_zpow_mul_setLIntegral_of_mem_normalizer`

`Thm_HaarQuotient_lintegral_mul_comp_out_eq_tsum_zpow_mul_setLIntegral_of_mem_normalizer` — Peeling a ℤ-index off a quotient integral over Hbackslash G

```lean
theorem HaarQuotient.lintegral_mul_comp_out_eq_tsum_zpow_mul_setLIntegral_of_mem_normalizer
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (b : G) (hb : ∀ y : G, y ∈ H ↔ b * y * b⁻¹ ∈ H) (D : ℝ≥0∞) (hD₀ : D ≠ 0) (hD : D ≠ ∞)
    (hbD : ∀ F : H → ℝ≥0∞, Measurable F →
      ∫⁻ x, F ⟨b * (x : G) * b⁻¹, (hb (x : G)).mp x.2⟩ ∂μH = D * ∫⁻ x, F x ∂μH)
    (m : G → ℤ) (hm : Measurable m) (hmH : ∀ x ∈ H, ∀ g : G, m (x * g) = m g)
    (hmb : ∀ g : G, m (b * g) = m g + 1)
    (h : G → ℝ≥0∞) (hh : Measurable h) (hhH : ∀ x ∈ H, ∀ g : G, h (x * g) = h g)
    (hhb : ∀ g : G, h (b * g) = h g)
    (Φ : ℤ → ℝ≥0∞) :
    ∫⁻ q, h q.out * Φ (m q.out) ∂(HaarQuotient.measure μ H μH) =
      (∑' n : ℤ, D ^ n * Φ n) *
        ∫⁻ q in {q : MulAction.orbitRel.Quotient H G | m q.out = 0}, h q.out ∂(HaarQuotient.measure μ H μH)
```

### `HaarQuotient.map_mk_withDensity_eq_smul_measure`

`Thm_HaarQuotient_map_mk_withDensity_eq_smul_measure` — Pushforward of a density with constant coset integral

```lean
theorem HaarQuotient.map_mk_withDensity_eq_smul_measure
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (ρ : G → ℝ≥0∞) (hρ : Measurable ρ) (c : ℝ≥0∞)
    (hρc : ∀ g : G, ∫⁻ x : H, ρ ((x : G) * g) ∂μH = c) :
    Measure.map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) (μ.withDensity ρ) =
      c • HaarQuotient.measure μ H μH
```

### `HaarQuotient.measurable_lintegral_mul_out`

`Thm_HaarQuotient_measurable_lintegral_mul_out` — Measurability of orbit integrals on the coset space H backslash G

```lean
theorem HaarQuotient.measurable_lintegral_mul_out
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (f : G → ℝ≥0∞) (hf : Measurable f) :
    Measurable fun q : MulAction.orbitRel.Quotient H G => ∫⁻ x, f ((x : G) * q.out) ∂μH
```

### `HaarQuotient.measure_image_mk_lt_top_and_withDensity_density_coe_mul_lt_top_of_isCompact`

`Thm_HaarQuotient_measure_image_mk_lt_top_and_withDensity_density_coe_mul_lt_top_of_isCompact` — Compact sets have finite Haar quotient measure

```lean
theorem HaarQuotient.measure_image_mk_lt_top_and_withDensity_density_coe_mul_lt_top_of_isCompact
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (K : Set G) (hK : IsCompact K) :
    HaarQuotient.measure μ H μH ((Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) '' K) < ⊤ ∧
    (μ.withDensity (HaarQuotient.density H μH)) ((H : Set G) * K) < ⊤
```

### `HaarQuotient.setLIntegral_eq_lintegral_setLIntegral_mul_out`

`Thm_HaarQuotient_setLIntegral_eq_lintegral_setLIntegral_mul_out` — Quotient integration formula over fundamental domains for Γ ≤ H ≤ G

```lean
theorem HaarQuotient.setLIntegral_eq_lintegral_setLIntegral_mul_out
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (Γ : Subgroup G) (hΓ : Γ ≤ H) [Countable Γ]
    (f : G → ℝ≥0∞) (hf : Measurable f) (hfΓ : ∀ γ ∈ Γ, ∀ g : G, f (γ * g) = f g)
    (S : Set G) (hS : IsFundamentalDomain Γ S μ)
    (T : Set H) (hT : IsFundamentalDomain (Γ.subgroupOf H) T μH) :
    ∫⁻ g in S, f g ∂μ =
      ∫⁻ q, (∫⁻ x in T, f ((x : G) * q.out) ∂μH) ∂(HaarQuotient.measure μ H μH)
```

### `HaarQuotient.setLIntegral_withDensity_eq_inv_mul_setLIntegral_of_forall_lintegral_eq`

`Thm_HaarQuotient_setLIntegral_withDensity_eq_inv_mul_setLIntegral_of_forall_lintegral_eq` — Integral over a double coset HtK against a quotient density

```lean
theorem HaarQuotient.setLIntegral_withDensity_eq_inv_mul_setLIntegral_of_forall_lintegral_eq
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (H : Subgroup G) (μH : Measure ↥H) [μH.IsMulRightInvariant]
    (ρ : G → ENNReal)
    (hquot : ∀ h : G → ENNReal, Measurable h →
      ∫⁻ g, h g ∂μ = ∫⁻ q, (∫⁻ x, h ((x : G) * q.out) ∂μH)
        ∂(Measure.map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) (μ.withDensity ρ)))
    (K : Subgroup G) (hK : IsClosed (K : Set G)) (t : G) (S : Set G) (hS : MeasurableSet S)
    (hmemS : ∀ g : G, g ∈ S ↔ ∃ x ∈ H, ∃ k ∈ K, g = x * t * k)
    (D : ENNReal) (hD : μH {y : ↥H | t⁻¹ * (y : G) * t ∈ K} = D) (hD0 : D ≠ 0) (hDtop : D ≠ ⊤)
    (f : G → ENNReal) (hf : Measurable f) (hfH : ∀ x ∈ H, ∀ g : G, f (x * g) = f g) :
    ∫⁻ g in S, f g ∂(μ.withDensity ρ) = D⁻¹ * ∫⁻ k in (K : Set G), f (t * k) ∂μ
```

### `HaarQuotient.withDensity_density_coe_mul_lt_top_of_isCompact`

`Thm_HaarQuotient_withDensity_density_coe_mul_lt_top_of_isCompact` — Finiteness of H· K for the Haar cut-off measure

```lean
theorem HaarQuotient.withDensity_density_coe_mul_lt_top_of_isCompact
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (hK₀ : ∃ K₀ : Subgroup G, IsOpen (K₀ : Set G) ∧ IsCompact (K₀ : Set G))
    (K : Set G) (hK : IsCompact K) :
    (μ.withDensity (HaarQuotient.density H μH)) ((H : Set G) * K) < ⊤
```

## AddCommGroup (18)

### `AddCommGroup.apply_zsmul_add_eq_of_forall_cube`

`Thm_AddCommGroup_apply_zsmul_add_eq_of_forall_cube` — Cube identity forces quadratic behaviour along lines

```lean
theorem AddCommGroup.apply_zsmul_add_eq_of_forall_cube
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] (Λ : M → N)
    (hΛ : ∀ x y z : M,
      Λ (x + y + z) - Λ (x + y) - Λ (x + z) - Λ (y + z) + Λ x + Λ y + Λ z = Λ 0)
    (x y : M) (n : ℤ) :
    Λ (n • x + y) =
      Λ y + n • (Λ (x + y) - Λ y) + (n * (n - 1) / 2) • (Λ (2 • x) - 2 • Λ x + Λ 0)
```

### `AddCommGroup.exists_addEquiv_prod_torsionBy_apply_eq_of_forall_exists_ne_smul`

`Thm_AddCommGroup_exists_addEquiv_prod_torsionBy_apply_eq_of_forall_exists_ne_smul` — Cyclic basis (v,σ v) of the n-torsion under a non-scalar endomorphism

```lean
theorem AddCommGroup.exists_addEquiv_prod_torsionBy_apply_eq_of_forall_exists_ne_smul
    {A : Type*} [AddCommGroup A] (n : ℕ) [NeZero n]
    (e : ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n) (σ : A →+ A)
    (hns : ∀ p : ℕ, p.Prime → p ∣ n → ∃ a : A, addOrderOf a = p ∧ ∀ k : ℕ, σ a ≠ k • a) :
    ∃ e' : ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n,
      ((e' (0, 1) : Submodule.torsionBy ℤ A n) : A) =
        σ ((e' (1, 0) : Submodule.torsionBy ℤ A n) : A)
```

### `AddCommGroup.exists_basis_smul_eq_of_card_torsionBy`

`Thm_AddCommGroup_exists_basis_smul_eq_of_card_torsionBy` — Lifting bases of M[ℓ^m] to bases of M[ℓ^{m+1}]

```lean
theorem AddCommGroup.exists_basis_smul_eq_of_card_torsionBy (ℓ : ℕ) [Fact ℓ.Prime]
    {M : Type*} [AddCommGroup M] (r m : ℕ)
    (hcard : ∀ j ≤ m + 1, Nat.card (Submodule.torsionBy ℤ M ((ℓ ^ j : ℕ) : ℤ)) = (ℓ ^ j) ^ r)
    {V : Type*} [AddCommGroup V] [Module (ZMod (ℓ ^ m)) V]
    (ι : V →+ M) (hι : Function.Injective ι)
    (hιr : ∀ x : M, x ∈ ι.range ↔ ((ℓ ^ m : ℕ) : ℤ) • x = 0)
    {V' : Type*} [AddCommGroup V'] [Module (ZMod (ℓ ^ (m + 1))) V']
    (ι' : V' →+ M) (hι' : Function.Injective ι')
    (hι'r : ∀ x : M, x ∈ ι'.range ↔ ((ℓ ^ (m + 1) : ℕ) : ℤ) • x = 0)
    (c : Module.Basis (Fin r) (ZMod (ℓ ^ m)) V) :
    ∃ c' : Module.Basis (Fin r) (ZMod (ℓ ^ (m + 1))) V', ∀ i, ι (c i) = ℓ • ι' (c' i)
```

### `AddCommGroup.exists_fg_saturation_of_isHomogeneous_degree`

`Thm_AddCommGroup_exists_fg_saturation_of_isHomogeneous_degree` — Finitely generated saturations from a separating homogeneous degree

```lean
theorem AddCommGroup.exists_fg_saturation_of_isHomogeneous_degree
    {R : Type*} [AddCommGroup R] (deg : R → ℤ) (D : ℕ) (hD : D ≠ 0)
    (hpoly : ∀ (m : ℕ) (α : Fin m → R), ∃ P : MvPolynomial (Fin m) ℚ, P.IsHomogeneous D ∧
      ∀ n : Fin m → ℤ, (deg (∑ i, n i • α i) : ℚ) = MvPolynomial.eval (fun i => (n i : ℚ)) P)
    (hsep : ∀ x : R, x ≠ 0 → deg x ≠ 0)
    (M : AddSubgroup R) (hM : M.FG) :
    ∃ M' : AddSubgroup R, M'.FG ∧ ∀ x : R, x ∈ M' ↔ ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ M
```

### `AddCommGroup.exists_mem_torsionBy_smul_eq_of_card_torsionBy`

`Thm_AddCommGroup_exists_mem_torsionBy_smul_eq_of_card_torsionBy` — Divisibility of ℓ-power torsion from exact torsion counts

```lean
theorem AddCommGroup.exists_mem_torsionBy_smul_eq_of_card_torsionBy (ℓ : ℕ) [Fact ℓ.Prime]
    {M : Type*} [AddCommGroup M] (r m : ℕ)
    (hcard : ∀ j ≤ m + 1, Nat.card (Submodule.torsionBy ℤ M ((ℓ ^ j : ℕ) : ℤ)) = (ℓ ^ j) ^ r)
    (x : M) (hx : x ∈ Submodule.torsionBy ℤ M ((ℓ ^ m : ℕ) : ℤ)) :
    ∃ y ∈ Submodule.torsionBy ℤ M ((ℓ ^ (m + 1) : ℕ) : ℤ), ℓ • y = x
```

### `AddCommGroup.exists_mvPolynomial_totalDegree_le_eval_eq_of_forall_exists_polynomial_zsmul_add`

`Thm_AddCommGroup_exists_mvPolynomial_totalDegree_le_eval_eq_of_forall_exists_polynomial_zsmul_add` — Polynomial along every progression implies polynomial function

```lean
theorem AddCommGroup.exists_mvPolynomial_totalDegree_le_eval_eq_of_forall_exists_polynomial_zsmul_add
    {M : Type*} [AddCommGroup M] {R : Type*} [Field R] [CharZero R] (f : M → R) (d : ℕ)
    (hf : ∀ x y : M, ∃ p : Polynomial R, p.natDegree ≤ d ∧
      ∀ n : ℤ, f (n • x + y) = p.eval (n : R))
    {ι : Type*} [Fintype ι] (e : ι → M) :
    ∃ P : MvPolynomial ι R, P.totalDegree ≤ d ∧
      ∀ c : ι → ℤ, MvPolynomial.eval (fun i => (c i : R)) P = f (∑ i, c i • e i)
```

### `AddCommGroup.exists_torsionBy_coords_of_dicyclic_relations`

`Thm_AddCommGroup_exists_torsionBy_coords_of_dicyclic_relations` — M-torsion free of rank one over ℤ[β]/M and ℤ[α]/M

```lean
theorem AddCommGroup.exists_torsionBy_coords_of_dicyclic_relations
    (M : ℕ) [NeZero M] (hM : ¬ 3 ∣ M) {A : Type*} [AddCommGroup A]
    (e : ZMod M × ZMod M ≃+ Submodule.torsionBy ℤ A M)
    (α β : A →+ A) (hα : ∀ T, α (α T) = -T) (hβ : ∀ T, β (β T) + β T + T = 0)
    (hαβ : ∀ T, α (β T) = β (β (α T))) :
    (∃ P : A, (M : ℤ) • P = 0 ∧ ∀ T : A, (M : ℤ) • T = 0 →
      ∃! c : ZMod M × ZMod M, c.1.val • P + c.2.val • β P = T) ∧
    (∃ P : A, (M : ℤ) • P = 0 ∧ ∀ T : A, (M : ℤ) • T = 0 →
      ∃! c : ZMod M × ZMod M, c.1.val • P + c.2.val • α P = T)
```

### `AddCommGroup.finite_and_natCard_torsionBy_le_of_natCard_fixed_primaryComponent_le_of_divisible`

`Thm_AddCommGroup_finite_and_natCard_torsionBy_le_of_natCard_fixed_primaryComponent_le_of_divisible` — Bound on A[ℓ] from growth of τ^{ℓ^k}-fixed points

```lean
theorem AddCommGroup.finite_and_natCard_torsionBy_le_of_natCard_fixed_primaryComponent_le_of_divisible
    {A : Type*} [AddCommGroup A] (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ) (τ : A →+ A)
    (hexh : ∀ x ∈ AddCommGroup.primaryComponent A ℓ, ∃ k : ℕ, (⇑τ)^[ℓ ^ k] x = x)
    (hfix : ∃ c : ℕ, ∀ k : ℕ,
      Finite {x : A // x ∈ AddCommGroup.primaryComponent A ℓ ∧ (⇑τ)^[ℓ ^ k] x = x} ∧
      Nat.card {x : A // x ∈ AddCommGroup.primaryComponent A ℓ ∧ (⇑τ)^[ℓ ^ k] x = x} ≤
        ℓ ^ (r * k + c))
    (hdiv : ∀ x ∈ AddCommGroup.primaryComponent A ℓ, ∃ y : A, ℓ • y = x) :
    Finite (Submodule.torsionBy ℤ A (ℓ : ℤ)) ∧
      Nat.card (Submodule.torsionBy ℤ A (ℓ : ℤ)) ≤ ℓ ^ r
```

### `AddCommGroup.moduleFinite_and_free_of_fg_saturation_of_ker_le_nsmul`

`Thm_AddCommGroup_moduleFinite_and_free_of_fg_saturation_of_ker_le_nsmul` — Finite freeness from finitely generated saturations and an n-divisible kernel

```lean
theorem AddCommGroup.moduleFinite_and_free_of_fg_saturation_of_ker_le_nsmul
    {R : Type*} [AddCommGroup R] [IsAddTorsionFree R]
    (hsat : ∀ M : AddSubgroup R, M.FG →
      ∃ M' : AddSubgroup R, M'.FG ∧ ∀ x : R, x ∈ M' ↔ ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ M)
    {G : Type*} [AddCommGroup G] [Finite G] (ρ : R →+ G) (n : ℕ) (hn : 1 < n)
    (hρ : ∀ x : R, ρ x = 0 → ∃ y : R, x = n • y) :
    Module.Finite ℤ R ∧ Module.Free ℤ R
```

### `AddCommGroup.natCard_addMonoidHom_eq_of_isAddCyclic`

`Thm_AddCommGroup_natCard_addMonoidHom_eq_of_isAddCyclic` — Counting homomorphisms into a cyclic group killing X

```lean
theorem AddCommGroup.natCard_addMonoidHom_eq_of_isAddCyclic {X Y : Type} [AddCommGroup X] [Finite X] [AddCommGroup Y] [Finite Y]
    [IsAddCyclic Y] (hX : ∀ x : X, Nat.card Y • x = 0) :
    Nat.card (X →+ Y) = Nat.card X
```

### `AddCommGroup.natCard_primaryComponent_ker_aeval_of_forall_natCard_ker_aeval_eq_natAbs_resultant`

`Thm_AddCommGroup_natCard_primaryComponent_ker_aeval_of_forall_natCard_ker_aeval_eq_natAbs_resultant` — ℓ-primary kernel orders of G(T) from resultants

```lean
theorem AddCommGroup.natCard_primaryComponent_ker_aeval_of_forall_natCard_ker_aeval_eq_natAbs_resultant
    {M : Type*} [AddCommGroup M] (T : M →+ M) (P : Polynomial ℤ) (hP : P.Monic)
    (R : Type*) [CommRing R] [IsDomain R]
    (h : ∀ G : Polynomial ℤ, G.Monic → ((G.coeff 0 : ℤ) : R) ≠ 0 →
        (G.resultant P ≠ 0 →
          Nat.card (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom.ker =
            (G.resultant P).natAbs) ∧
        (G.resultant P = 0 →
          ¬ Finite (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom.ker))
    (G : Polynomial ℤ) (hG : G.Monic) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : R) ≠ 0) :
    (G.resultant P ≠ 0 →
      Nat.card (AddCommGroup.primaryComponent
        (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom.ker ℓ) =
        ℓ ^ ((G.resultant P).natAbs.factorization ℓ)) ∧
    (G.resultant P = 0 →
      ¬ Finite (AddCommGroup.primaryComponent
        (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom.ker ℓ))
```

### `AddCommGroup.natCard_torsionBy_pow_eq_pow_of_natCard_fixed_primaryComponent`

`Thm_AddCommGroup_natCard_torsionBy_pow_eq_pow_of_natCard_fixed_primaryComponent` — ℓ-power torsion from fixed-point counts of an endomorphism

```lean
theorem AddCommGroup.natCard_torsionBy_pow_eq_pow_of_natCard_fixed_primaryComponent
    {A : Type*} [AddCommGroup A] (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ) (τ : A →+ A)
    (hfin : Finite (Submodule.torsionBy ℤ A (ℓ : ℤ)))
    (hle : Nat.card (Submodule.torsionBy ℤ A (ℓ : ℤ)) ≤ ℓ ^ r)
    (hτ : ∀ x : A, ℓ ^ 2 • x = 0 → τ x = x)
    (hfix : ∃ c k₀ : ℕ, ∀ k : ℕ,
      Nat.card {x : A // x ∈ AddCommGroup.primaryComponent A ℓ ∧ (⇑τ)^[ℓ ^ (k₀ + k)] x = x} =
        ℓ ^ (r * k + c))
    (n : ℕ) :
    Nat.card (Submodule.torsionBy ℤ A ((ℓ ^ n : ℕ) : ℤ)) = ℓ ^ (r * n)
```

### `AddCommGroup.natCard_torsionBy_prod_eq_mul`

`Thm_AddCommGroup_natCard_torsionBy_prod_eq_mul` — Multiplicativity of N-torsion cardinality in a product

```lean
theorem AddCommGroup.natCard_torsionBy_prod_eq_mul
    (A : Type u) (B : Type v) [AddCommGroup A] [AddCommGroup B] (N : ℕ) :
    Nat.card (Submodule.torsionBy ℤ (A × B) (N : ℤ)) =
      Nat.card (Submodule.torsionBy ℤ A (N : ℤ)) * Nat.card (Submodule.torsionBy ℤ B (N : ℤ))
```

### `AddCommGroup.nonempty_addEquiv_of_forall_natCard_torsionBy_eq`

`Thm_AddCommGroup_nonempty_addEquiv_of_forall_natCard_torsionBy_eq` — Equal N-torsion counts force isomorphism of finite abelian groups

```lean
theorem AddCommGroup.nonempty_addEquiv_of_forall_natCard_torsionBy_eq
    (A : Type u) (B : Type v) [AddCommGroup A] [AddCommGroup B] [Finite A] [Finite B]
    (h : ∀ N : ℕ, Nat.card (Submodule.torsionBy ℤ A (N : ℤ)) = Nat.card (Submodule.torsionBy ℤ B (N : ℤ))) :
    Nonempty (A ≃+ B)
```

### `AddCommGroup.nonempty_addMonoidHom_zmod_addEquiv_of_forall_nsmul_eq_zero`

`Thm_AddCommGroup_nonempty_addMonoidHom_zmod_addEquiv_of_forall_nsmul_eq_zero` — A finite abelian group killed by d is isomorphic to Hom(L,ℤ/d)

```lean
theorem AddCommGroup.nonempty_addMonoidHom_zmod_addEquiv_of_forall_nsmul_eq_zero
    (L : Type u) [AddCommGroup L] [Finite L] (d : ℕ) [NeZero d] (hd : ∀ x : L, d • x = 0) :
    Nonempty ((L →+ ZMod d) ≃+ L)
```

### `AddCommGroup.nonempty_basis_zmod_pow_of_card_torsionBy`

`Thm_AddCommGroup_nonempty_basis_zmod_pow_of_card_torsionBy` — Levelwise torsion counts give a free ℤ/ℓ^m-module of rank r

```lean
theorem AddCommGroup.nonempty_basis_zmod_pow_of_card_torsionBy (ℓ : ℕ) [Fact ℓ.Prime]
    {M : Type*} [AddCommGroup M] (r m : ℕ)
    (hcard : ∀ j ≤ m, Nat.card (Submodule.torsionBy ℤ M ((ℓ ^ j : ℕ) : ℤ)) = (ℓ ^ j) ^ r)
    {V : Type*} [AddCommGroup V] [Module (ZMod (ℓ ^ m)) V]
    (ι : V →+ M) (hι : Function.Injective ι)
    (hιr : ∀ x : M, x ∈ ι.range ↔ ((ℓ ^ m : ℕ) : ℤ) • x = 0) :
    Nonempty (Module.Basis (Fin r) (ZMod (ℓ ^ m)) V)
```

### `AddCommGroup.nonempty_pi_zmod_addEquiv_torsionBy_of_card_torsionBy_eq_pow`

`Thm_AddCommGroup_nonempty_pi_zmod_addEquiv_torsionBy_of_card_torsionBy_eq_pow` — Recognising A[n] as (ℤ/n)^r from torsion counts

```lean
theorem AddCommGroup.nonempty_pi_zmod_addEquiv_torsionBy_of_card_torsionBy_eq_pow
    {A : Type u} [AddCommGroup A] {n : ℕ} (hn : n ≠ 0) (r : ℕ)
    (hcard : ∀ d : ℕ, d ∣ n → Nat.card (Submodule.torsionBy ℤ A d) = d ^ r) :
    Nonempty ((Fin r → ZMod n) ≃+ Submodule.torsionBy ℤ A n)
```

### `AddCommGroup.nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq`

`Thm_AddCommGroup_nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq` — #A[d]=d² for all d∣ n forces A[n]≅(ℤ/n)²

```lean
theorem AddCommGroup.nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq
    {A : Type*} [AddCommGroup A] {n : ℕ} (hn : n ≠ 0)
    (hcard : ∀ d : ℕ, d ∣ n → Nat.card (Submodule.torsionBy ℤ A d) = d ^ 2) :
    Nonempty (ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n)
```

## Subgroup (18)

### `Subgroup.IsArithmetic.exists_nat_mem_strictPeriods_conj`

`Thm_Subgroup_IsArithmetic_exists_nat_mem_strictPeriods_conj` — A uniform integer period for all SL₂(ℤ)-conjugates

```lean
theorem Subgroup.IsArithmetic.exists_nat_mem_strictPeriods_conj (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic] : ∃ M : ℕ, 0 < M ∧ ∀ γ : SL(2, ℤ), (M : ℝ) ∈ (ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ γ) • 𝒢).strictPeriods
```

### `Subgroup.card_orbitRelQuotient_mul_card_eq_index`

`Thm_Subgroup_card_orbitRelQuotient_mul_card_eq_index` — Free double-coset count: #(Hbackslash M/K)·|K|=[M:H]

```lean
theorem Subgroup.card_orbitRelQuotient_mul_card_eq_index {M : Type*} [Group M] (H K : Subgroup M)
    (hKH : ∀ g x : M, x ∈ K → g⁻¹ * x * g ∈ H → x = 1) :
    Nat.card (MulAction.orbitRel.Quotient H (M ⧸ K)) * Nat.card K = H.index
```

### `Subgroup.card_quotient_zpowers_le_three_of_injective_of_sq_sub_mul_add_one_eq_zero`

`Thm_Subgroup_card_quotient_zpowers_le_three_of_injective_of_sq_sub_mul_add_one_eq_zero` — Quotient by an involution under quadratic trace relations mod M

```lean
theorem Subgroup.card_quotient_zpowers_le_three_of_injective_of_sq_sub_mul_add_one_eq_zero
    (M : ℕ) (hM : 3 ≤ M) (H : Type*) [CommGroup H] [Finite H]
    (c : H) (hc2 : c * c = 1)
    (χ : H →* (ZMod M)ˣ) (hχ : Function.Injective χ) (hc : ((χ c : (ZMod M)ˣ) : ZMod M) = -1)
    (htr : ∀ h : H, ∃ t : ℤ, (t = -2 ∨ t = -1 ∨ t = 0 ∨ t = 1 ∨ t = 2) ∧
      ((χ h : (ZMod M)ˣ) : ZMod M) ^ 2 - (t : ZMod M) * ((χ h : (ZMod M)ˣ) : ZMod M) + 1 = 0 ∧
      (t = 2 → h = 1) ∧ (t = -2 → h = c)) :
    Nat.card (H ⧸ Subgroup.zpowers c) ≤ 3 ∧ IsCyclic (H ⧸ Subgroup.zpowers c) ∧
      (2 ∣ Nat.card (H ⧸ Subgroup.zpowers c) → ∃ lam : ZMod M, lam ^ 2 + 1 = 0) ∧
      (3 ∣ Nat.card (H ⧸ Subgroup.zpowers c) → ∃ lam : ZMod M, lam ^ 2 + lam + 1 = 0)
```

### `Subgroup.commutatorElement_eq_and_mul_and_pow_of_forall_commutatorElement_mem_of_le_center`

`Thm_Subgroup_commutatorElement_eq_and_mul_and_pow_of_forall_commutatorElement_mem_of_le_center` — Central commutators give a bimultiplicative alternating pairing

```lean
theorem Subgroup.commutatorElement_eq_and_mul_and_pow_of_forall_commutatorElement_mem_of_le_center
    {G : Type*} [Group G] (Z : Subgroup G) (hZ : Z ≤ Subgroup.center G)
    (hcomm : ∀ g h : G, ⁅g, h⁆ ∈ Z) :
    (∀ g g' h h' : G, g⁻¹ * g' ∈ Z → h⁻¹ * h' ∈ Z → ⁅g, h⁆ = ⁅g', h'⁆) ∧
    (∀ g g' h : G, ⁅g * g', h⁆ = ⁅g, h⁆ * ⁅g', h⁆) ∧
    (∀ g h h' : G, ⁅g, h * h'⁆ = ⁅g, h⁆ * ⁅g, h'⁆) ∧
    (∀ g h : G, ⁅g, h⁆ * ⁅h, g⁆ = 1) ∧
    (∀ g : G, ⁅g, g⁆ = 1) ∧
    (∀ (g h : G) (n : ℕ), ⁅g ^ n, h⁆ = ⁅g, h⁆ ^ n ∧ ⁅g, h ^ n⁆ = ⁅g, h⁆ ^ n)
```

### `Subgroup.existsUnique_eq_mul_mul_and_finsum_mem_eq_sum_sum_finsum_mem_of_existsUnique_mul_inv_mem`

`Thm_Subgroup_existsUnique_eq_mul_mul_and_finsum_mem_eq_sum_sum_finsum_mem_of_existsUnique_mul_inv_mem` — Unique factorisation A=μ·{cⱼ}· H and sum re-indexing

```lean
theorem Subgroup.existsUnique_eq_mul_mul_and_finsum_mem_eq_sum_sum_finsum_mem_of_existsUnique_mul_inv_mem
    {G : Type*} [CommGroup G] (μ F A H : Subgroup G) (hμ : (μ : Set G).Finite)
    (hμF : ∀ ζ ∈ μ, ζ ∈ F → ζ = 1) (hμA : μ ≤ A)
    (hA : ∀ u ∈ A, ∃ ζ ∈ μ, ∃ φ ∈ F, u = ζ * φ)
    (hHF : H ≤ F) (hHA : H ≤ A)
    {m : ℕ} (c : Fin m → G) (hcF : ∀ j, c j ∈ F) (hcA : ∀ j, c j ∈ A)
    (hclass : ∀ φ ∈ F, φ ∈ A → ∃! j : Fin m, φ * (c j)⁻¹ ∈ H) :
    (∀ u ∈ A, ∃! p : μ × Fin m × H, u = (p.1 : G) * c p.2.1 * (p.2.2 : G)) ∧
    ∀ {M : Type*} [AddCommMonoid M] (g : G → M), ((A : Set G) ∩ Function.support g).Finite →
      ∑ᶠ u ∈ (A : Set G), g u = ∑ ζ ∈ hμ.toFinset, ∑ j : Fin m, ∑ᶠ h ∈ (H : Set G), g (ζ * c j * h)
```

### `Subgroup.exists_eq_mul_of_index_inf_eq`

`Thm_Subgroup_exists_eq_mul_of_index_inf_eq` — Index multiplicativity forces G = H₁H₂

```lean
theorem Subgroup.exists_eq_mul_of_index_inf_eq {G : Type*} [Group G] [Finite G] (H₁ H₂ : Subgroup G) (h : (H₁ ⊓ H₂).index = H₁.index * H₂.index) (g : G) : ∃ h₁ ∈ H₁, ∃ h₂ ∈ H₂, g = h₁ * h₂
```

### `Subgroup.exists_exact_fundamental_domain_of_secondCountableTopology`

`Thm_Subgroup_exists_exact_fundamental_domain_of_secondCountableTopology` — Exact fundamental domain for a discrete subgroup

```lean
theorem Subgroup.exists_exact_fundamental_domain_of_secondCountableTopology
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    (Γ : Subgroup G) (hdisc : ∃ V : Set G, IsOpen V ∧ V ∩ (Γ : Set G) = {1}) :
    ∃ F : Set G,
      (∃ U C : ℕ → Set G, (∀ n, IsOpen (U n)) ∧ (∀ n, IsOpen (C n)) ∧ F = ⋃ n, U n \ C n) ∧
      ∀ x : G, ∃! γ : ↥Γ, (γ : G) * x ∈ F
```

### `Subgroup.exists_int_forall_finsum_ite_eq_one`

`Thm_Subgroup_exists_int_forall_finsum_ite_eq_one` — Existence of Artin induction coefficients on cyclic p'-subgroups

```lean
theorem Subgroup.exists_int_forall_finsum_ite_eq_one (p : ℕ) {G : Type} [Group G] [Finite G] :
    ∃ b : Subgroup G → ℤ, ∀ H : Subgroup G, IsCyclic H → (Nat.card H).Coprime p →
      ∑ᶠ D : Subgroup G, (if IsCyclic D ∧ (Nat.card D).Coprime p ∧ H ≤ D then b D else 0) = 1
```

### `Subgroup.exists_le_normal_subgroupOf_relIndex_ne_zero_torsionFree_of_relIndex_ne_zero`

`Thm_Subgroup_exists_le_normal_subgroupOf_relIndex_ne_zero_torsionFree_of_relIndex_ne_zero` — Normal torsion-free finite-index subgroup via the normal core

```lean
theorem Subgroup.exists_le_normal_subgroupOf_relIndex_ne_zero_torsionFree_of_relIndex_ne_zero
    {G : Type} [Group G] (H K N₀ : Subgroup G) (hHK : H ≤ K) (hHidx : H.relIndex K ≠ 0)
    (hN₀ : N₀ ≤ H) (hN₀idx : N₀.relIndex H ≠ 0) (htf : ∀ g ∈ N₀, IsOfFinOrder g → g = 1) :
    ∃ N : Subgroup G, N ≤ N₀ ∧ (N.subgroupOf K).Normal ∧ N.relIndex H ≠ 0 ∧ ∀ g ∈ N, IsOfFinOrder g → g = 1
```

### `Subgroup.exists_subgroup_injOn_map_eq_of_ker_le_center_of_comm`

`Thm_Subgroup_exists_subgroup_injOn_map_eq_of_ker_le_center_of_comm` — Splitting a central extension over an exponent-2 subgroup

```lean
theorem Subgroup.exists_subgroup_injOn_map_eq_of_ker_le_center_of_comm {G : Type*} [Group G] {V : Type*} [CommGroup V] (π : G →* V) (hZ : π.ker ≤ Subgroup.center G) (hsq : ∀ z ∈ π.ker, ∃ w ∈ π.ker, w * w = z) (H : Subgroup V) (hH : ∀ h ∈ H, h * h = 1) (hlift : ∀ h ∈ H, ∃ g : G, π g = h) (hcomm : ∀ g g' : G, π g ∈ H → π g' ∈ H → g * g' = g' * g) : ∃ K : Subgroup G, (∀ g ∈ K, ∀ g' ∈ K, π g = π g' → g = g') ∧ ∀ v : V, (∃ g ∈ K, π g = v) ↔ v ∈ H
```

### `Subgroup.exists_wild_tame_cyclic_unramified_chain_of_le`

`Thm_Subgroup_exists_wild_tame_cyclic_unramified_chain_of_le` — Wild–tame–unramified chain with cyclic tame and top steps

```lean
theorem Subgroup.exists_wild_tame_cyclic_unramified_chain_of_le
    {G : Type*} [Group G] {q : ℕ} [Fact q.Prime]
    (U W : Subgroup G) [U.Normal] [U.FiniteIndex] [W.Normal] (hUW : U ≤ W)
    (hWq : ∀ w ∈ W, ∃ a : ℕ, w ^ (q ^ a) ∈ U)
    (t φ : G) (hφt : (t ^ q)⁻¹ * (φ * t * φ⁻¹) ∈ W)
    (hgen : ∀ g : G, ∃ n : ℕ, (φ ^ n)⁻¹ * g ∈ Subgroup.closure {t} ⊔ W)
    (S H : Subgroup G) (hUH : U ≤ H) (hHS : H ≤ S) (hHn : (H.subgroupOf S).Normal) :
    ∃ P I : Subgroup G, H ≤ P ∧ P ≤ I ∧ I ≤ S ∧ (P.subgroupOf S).Normal ∧ (I.subgroupOf S).Normal ∧
      (∃ n : ℕ, (H.subgroupOf P).index = q ^ n) ∧ ¬ q ∣ (P.subgroupOf I).index ∧
      (∃ g ∈ I, ∀ s ∈ I, ∃ n : ℕ, (g ^ n)⁻¹ * s ∈ P) ∧
      (∃ g ∈ S, ∀ s ∈ S, ∃ n : ℕ, (g ^ n)⁻¹ * s ∈ I)
```

### `Subgroup.exists_wild_tame_unramified_chain_of_le`

`Thm_Subgroup_exists_wild_tame_unramified_chain_of_le` — Wild–tame–unramified chain descends to intermediate normal pairs

```lean
theorem Subgroup.exists_wild_tame_unramified_chain_of_le
    {G : Type*} [Group G] {q : ℕ} [Fact q.Prime]
    (U W : Subgroup G) [U.Normal] [U.FiniteIndex] [W.Normal] (hUW : U ≤ W)
    (hWq : ∀ w ∈ W, ∃ a : ℕ, w ^ (q ^ a) ∈ U)
    (t φ : G) (hφt : (t ^ q)⁻¹ * (φ * t * φ⁻¹) ∈ W)
    (hgen : ∀ g : G, ∃ n : ℕ, (φ ^ n)⁻¹ * g ∈ Subgroup.closure {t} ⊔ W)
    (S H : Subgroup G) (hUH : U ≤ H) (hHS : H ≤ S) (hHn : (H.subgroupOf S).Normal) :
    ∃ P I : Subgroup G, H ≤ P ∧ P ≤ I ∧ I ≤ S ∧ (P.subgroupOf S).Normal ∧ (I.subgroupOf S).Normal ∧
      (∃ n : ℕ, (H.subgroupOf P).index = q ^ n) ∧ ¬ q ∣ (P.subgroupOf I).index ∧
      (∃ g ∈ S, ∀ s ∈ S, ∃ n : ℕ, (g ^ n)⁻¹ * s ∈ I)
```

### `Subgroup.finsum_card_mul_card_fixedBy_quotient_eq_card`

`Thm_Subgroup_finsum_card_mul_card_fixedBy_quotient_eq_card` — Artin's counting identity at p-regular elements

```lean
theorem Subgroup.finsum_card_mul_card_fixedBy_quotient_eq_card (p : ℕ) {G : Type} [Group G] [Finite G]
    (b : Subgroup G → ℤ)
    (hb : ∀ H : Subgroup G, IsCyclic H → (Nat.card H).Coprime p →
      ∑ᶠ D : Subgroup G, (if IsCyclic D ∧ (Nat.card D).Coprime p ∧ H ≤ D then b D else 0) = 1)
    (g : G) (hg : (orderOf g).Coprime p) :
    ∑ᶠ D : Subgroup G, (if IsCyclic D ∧ (Nat.card D).Coprime p
      then (Nat.card D : ℤ) * b D * Nat.card (MulAction.fixedBy (G ⧸ D) g) else 0) = Nat.card G
```

### `Subgroup.nonempty_quotient_zpowers_mulEquiv_of_forall_apply_mem_iff`

`Thm_Subgroup_nonempty_quotient_zpowers_mulEquiv_of_forall_apply_mem_iff` — Quotient H/⟨ c⟩ ≅ I from a surjection with index-matched cyclic kernel

```lean
theorem Subgroup.nonempty_quotient_zpowers_mulEquiv_of_forall_apply_mem_iff
    {U G : Type*} [CommGroup U] [Group G] [Finite U]
    (Ψ : U →* G) (hΨ : Function.Surjective Ψ)
    (c : U) (hc : Ψ c = 1) (hcard : Nat.card G = (Subgroup.zpowers c).index)
    (H : Subgroup U) (hcH : c ∈ H) (I : Subgroup G) (hI : ∀ u : U, Ψ u ∈ I ↔ u ∈ H) :
    Nonempty (↥H ⧸ Subgroup.zpowers (⟨c, hcH⟩ : ↥H) ≃* ↥I)
```

### `Subgroup.relIndex_inf_map_conj_eq_natCard_setOf_exists_quotientMk_mul_eq`

`Thm_Subgroup_relIndex_inf_map_conj_eq_natCard_setOf_exists_quotientMk_mul_eq` — Index of K∩ gKg⁻¹ counts K-cosets in KgK

```lean
theorem Subgroup.relIndex_inf_map_conj_eq_natCard_setOf_exists_quotientMk_mul_eq
    {G : Type*} [Group G] (K : Subgroup G) (g : G) :
    (K ⊓ K.map (MulAut.conj g).toMonoidHom).relIndex K =
      Nat.card {c : G ⧸ K // ∃ k ∈ K, (QuotientGroup.mk (k * g) : G ⧸ K) = c}
```

### `Subgroup.sum_fibre_doubleCoset_relIndex_inf_map_conj_eq_relIndex`

`Thm_Subgroup_sum_fibre_doubleCoset_relIndex_inf_map_conj_eq_relIndex` — Fibre degrees of a double coset degeneracy map sum to [K:K']

```lean
theorem Subgroup.sum_fibre_doubleCoset_relIndex_inf_map_conj_eq_relIndex
    {G : Type*} [Group G] (H K K' : Subgroup G) (hK : K' ≤ K) (x : G) [K'.IsFiniteRelIndex K]
    [Fintype {c : DoubleCoset.Quotient (H : Set G) (K' : Set G) // DoubleCoset.mk H K c.out = DoubleCoset.mk H K x}] :
    ∑ c : {c : DoubleCoset.Quotient (H : Set G) (K' : Set G) // DoubleCoset.mk H K c.out = DoubleCoset.mk H K x},
      (H ⊓ K'.map (MulAut.conj c.1.out).toMonoidHom).relIndex (H ⊓ K.map (MulAut.conj c.1.out).toMonoidHom) =
        K'.relIndex K
```

### `Subgroup.sum_fibre_doubleCoset_relIndex_inf_map_conj_eq_relIndex_of_le_inf`

`Thm_Subgroup_sum_fibre_doubleCoset_relIndex_inf_map_conj_eq_relIndex_of_le_inf` — Harmonicity of forgetful maps between double coset spaces

```lean
theorem Subgroup.sum_fibre_doubleCoset_relIndex_inf_map_conj_eq_relIndex_of_le_inf
    {G : Type*} [Group G] (H K K₁ K₂ K₁₂ : Subgroup G) (hK₁ : K₁ ≤ K) (hK₂ : K₂ ≤ K)
    (h₁ : K₁₂ ≤ K₁) (h₂ : K₁₂ ≤ K₂) (hinf : K₁ ⊓ K₂ ≤ K₁₂)
    (hsurj : ∀ k : K, ∃ k₁ : K₁, ((k₁ : G)⁻¹ * k) ∈ K₂)
    (z y : G) (hyz : DoubleCoset.mk H K z = DoubleCoset.mk H K y)
    [K₂.IsFiniteRelIndex K] [K₁₂.IsFiniteRelIndex K₁]
    [Fintype {c : DoubleCoset.Quotient (H : Set G) (K₁₂ : Set G) //
      DoubleCoset.mk H K₂ c.out = DoubleCoset.mk H K₂ y ∧ DoubleCoset.mk H K₁ c.out = DoubleCoset.mk H K₁ z}] :
    ∑ c : {c : DoubleCoset.Quotient (H : Set G) (K₁₂ : Set G) //
        DoubleCoset.mk H K₂ c.out = DoubleCoset.mk H K₂ y ∧ DoubleCoset.mk H K₁ c.out = DoubleCoset.mk H K₁ z},
      (H ⊓ K₁₂.map (MulAut.conj c.1.out).toMonoidHom).relIndex (H ⊓ K₁.map (MulAut.conj c.1.out).toMonoidHom) =
        (H ⊓ K₂.map (MulAut.conj y).toMonoidHom).relIndex (H ⊓ K.map (MulAut.conj y).toMonoidHom)
```

### `Subgroup.sum_sum_mul_ite_inv_mul_mem_and_eq_of_pairwise_inv_mul_notMem`

`Thm_Subgroup_sum_sum_mul_ite_inv_mul_mem_and_eq_of_pairwise_inv_mul_notMem` — Exactly one coset cell contributes to a double sum

```lean
theorem Subgroup.sum_sum_mul_ite_inv_mul_mem_and_eq_of_pairwise_inv_mul_notMem
    {G : Type*} [Group G] (A V : Subgroup G) (Fa Ft : Finset G) (c : G → G → ℂ)
    (hFa : ∀ α ∈ Fa, ∀ α' ∈ Fa, α ≠ α' → α⁻¹ * α' ∉ A)
    (hFt : ∀ τ ∈ Ft, ∀ τ' ∈ Ft, τ ≠ τ' → τ⁻¹ * τ' ∉ V)
    (a t α τ : G) (hα : α ∈ Fa) (hτ : τ ∈ Ft) (hA : a⁻¹ * α ∈ A) (hV : t⁻¹ * τ ∈ V) :
    (∑ α' ∈ Fa, ∑ τ' ∈ Ft, c α' τ' * (if a⁻¹ * α' ∈ A ∧ t⁻¹ * τ' ∈ V then 1 else 0)) = c α τ
```

## AddMonoidHom (16)

### `AddMonoidHom.exists_addEquiv_prod_addMonoidHom_forall_apply_eq_sub_of_alternating_of_nondegenerate`

`Thm_AddMonoidHom_exists_addEquiv_prod_addMonoidHom_forall_apply_eq_sub_of_alternating_of_nondegenerate` — Symplectic normal form for finite abelian groups with alternating pairing

```lean
theorem AddMonoidHom.exists_addEquiv_prod_addMonoidHom_forall_apply_eq_sub_of_alternating_of_nondegenerate
    {d : ℕ} [NeZero d] (K : Type) [AddCommGroup K] [Finite K]
    (B : K →+ K →+ ZMod d) (halt : ∀ a : K, B a a = 0) (hnd : ∀ a : K, (∀ b : K, B a b = 0) → a = 0) :
    ∃ (L : Type) (_ : AddCommGroup L) (_ : Fintype L) (α : L × (L →+ ZMod d) ≃+ K),
      ∀ (x x' : L) (c c' : L →+ ZMod d), B (α (x, c)) (α (x', c')) = c x' - c' x
```

### `AddMonoidHom.exists_addOrderOf_apply_eq_forall_apply_mem_zmultiples_of_ker_eq_zmultiples`

`Thm_AddMonoidHom_exists_addOrderOf_apply_eq_forall_apply_mem_zmultiples_of_ker_eq_zmultiples` — Completing a point of order N to a basis of A[N]

```lean
theorem AddMonoidHom.exists_addOrderOf_apply_eq_forall_apply_mem_zmultiples_of_ker_eq_zmultiples
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] {N : ℕ} [NeZero N]
    (e : ZMod N × ZMod N ≃+ Submodule.torsionBy ℤ A N)
    (Q : A) (hQ : addOrderOf Q = N) (φ : A →+ B) (hφ : φ.ker = AddSubgroup.zmultiples Q) :
    ∃ R : A, N • R = 0 ∧ addOrderOf (φ R) = N ∧
      ∀ P : A, N • P = 0 → φ P ∈ AddSubgroup.zmultiples (φ R)
```

### `AddMonoidHom.exists_basis_apply_eq_self_of_map_smul_eq_pow_smul_of_isAlgClosed`

`Thm_AddMonoidHom_exists_basis_apply_eq_self_of_map_smul_eq_pow_smul_of_isAlgClosed` — Frobenius-semilinear injections have a basis of fixed vectors

```lean
theorem AddMonoidHom.exists_basis_apply_eq_self_of_map_smul_eq_pow_smul_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    (V : Type v) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (φ : V →+ V) (hφ : ∀ (c : k) (x : V), φ (c • x) = c ^ p • φ x)
    (hinj : Function.Injective φ) :
    ∃ b : Module.Basis (Fin (Module.finrank k V)) k V, ∀ i, φ (b i) = b i
```

### `AddMonoidHom.exists_comp_self_sub_smul_add_eq_zero_of_dicyclic_relations_of_char_three_words`

`Thm_AddMonoidHom_exists_comp_self_sub_smul_add_eq_zero_of_dicyclic_relations_of_char_three_words` — Quadratic relations for the six words in a dicyclic pair

```lean
theorem AddMonoidHom.exists_comp_self_sub_smul_add_eq_zero_of_dicyclic_relations_of_char_three_words
    {V : Type*} [AddCommGroup V] (α β : V →+ V)
    (hα : ∀ T, α (α T) = -T) (hβ : ∀ T, β (β T) + β T + T = 0) (hαβ : ∀ T, α (β T) = β (β (α T)))
    (m : V →+ V)
    (hm : m = AddMonoidHom.id _ ∨ m = α ∨ m = β ∨ m = β.comp β ∨ m = α.comp β ∨ m = α.comp (β.comp β)) :
    ∃ t : ℤ, (t = -1 ∨ t = 0 ∨ t = 1 ∨ t = 2) ∧ (t = 2 → m = AddMonoidHom.id _) ∧
      ∀ T, m (m T) - t • m T + T = 0
```

### `AddMonoidHom.exists_comp_self_sub_smul_add_eq_zero_of_quaternionic_relations_of_char_two_words`

`Thm_AddMonoidHom_exists_comp_self_sub_smul_add_eq_zero_of_quaternionic_relations_of_char_two_words` — Quadratic relations for twelve words in σ,i,j

```lean
theorem AddMonoidHom.exists_comp_self_sub_smul_add_eq_zero_of_quaternionic_relations_of_char_two_words
    {V : Type*} [AddCommGroup V] (σ i j : V →+ V)
    (hσ3 : ∀ T, σ (σ (σ T)) = T) (hi : ∀ T, i (i T) = -T) (hj : ∀ T, j (j T) = -T)
    (hij : ∀ T, i (j T) = -(j (i T))) (hσi : ∀ T, σ (i T) = j (σ T)) (hσj : ∀ T, σ (j T) = j (i (σ T)))
    (hσ : ∀ T, σ (σ T) + σ T + T = 0)
    (m : V →+ V)
    (hm : m = AddMonoidHom.id _ ∨ m = σ ∨ m = σ.comp σ ∨
        m = i ∨ m = i.comp σ ∨ m = i.comp (σ.comp σ) ∨
        m = j ∨ m = j.comp σ ∨ m = j.comp (σ.comp σ) ∨
        m = i.comp j ∨ m = (i.comp j).comp σ ∨ m = (i.comp j).comp (σ.comp σ)) :
    ∃ t : ℤ, (t = -1 ∨ t = 0 ∨ t = 1 ∨ t = 2) ∧ (t = 2 → m = AddMonoidHom.id _) ∧
      ∀ T, m (m T) - t • m T + T = 0
```

### `AddMonoidHom.exists_isAddCyclic_natCard_eq_forall_apply_mem_of_apply_apply_eq_smul`

`Thm_AddMonoidHom_exists_isAddCyclic_natCard_eq_forall_apply_mem_of_apply_apply_eq_smul` — An f-stable cyclic subgroup of order M from a split quadratic relation

```lean
theorem AddMonoidHom.exists_isAddCyclic_natCard_eq_forall_apply_mem_of_apply_apply_eq_smul
    {G : Type*} [AddCommGroup G] {M : ℕ} (hM : M ≠ 0)
    (e : ZMod M × ZMod M ≃+ Submodule.torsionBy ℤ G (M : ℤ))
    (f : G →+ G) (u v : ℤ) (huv : (M : ℤ) ∣ u * v - 1)
    (hf : ∀ x : G, (M : ℤ) • x = 0 → f (f x) = u • f x) :
    ∃ C : AddSubgroup G, IsAddCyclic C ∧ Nat.card C = M ∧ ∀ x ∈ C, f x ∈ C
```

### `AddMonoidHom.exists_linearEquiv_tensorProduct_zmod_addMonoidHom_apply_tmul_of_moduleFinite_padicInt`

`Thm_AddMonoidHom_exists_linearEquiv_tensorProduct_zmod_addMonoidHom_apply_tmul_of_moduleFinite_padicInt` — Base change of additive duals for finite ℤₚ-modules

```lean
theorem AddMonoidHom.exists_linearEquiv_tensorProduct_zmod_addMonoidHom_apply_tmul_of_moduleFinite_padicInt
    (p : ℕ) [Fact p.Prime] (P : Type*) [AddCommGroup P] [Module ℤ_[p] P] [Module.Finite ℤ_[p] P]
    (B : Type*) [CommRing B] [Algebra (ZMod p) B] :
    ∃ e : B ⊗[ZMod p] (P →+ ZMod p) ≃ₗ[B] (P →+ B),
      ∀ (b : B) (φ : P →+ ZMod p) (x : P), e (b ⊗ₜ[ZMod p] φ) x = b * algebraMap (ZMod p) B (φ x)
```

### `AddMonoidHom.exists_nsmul_eq_zero_and_apply_eq_of_surjective_of_forall_ker`

`Thm_AddMonoidHom_exists_nsmul_eq_zero_and_apply_eq_of_surjective_of_forall_ker` — Surjectivity on m-torsion when the kernel is m-divisible

```lean
theorem AddMonoidHom.exists_nsmul_eq_zero_and_apply_eq_of_surjective_of_forall_ker
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (hf : Function.Surjective f)
    (m : ℕ) (hdiv : ∀ k : A, f k = 0 → ∃ j : A, f j = 0 ∧ m • j = k)
    (b : B) (hmb : m • b = 0) :
    ∃ a : A, m • a = 0 ∧ f a = b
```

### `AddMonoidHom.exists_pos_forall_nsmul_eq_zero_of_add_eq_zero_of_finite_fixedPoints_comp_self`

`Thm_AddMonoidHom_exists_pos_forall_nsmul_eq_zero_of_add_eq_zero_of_finite_fixedPoints_comp_self` — A uniform exponent killing solutions of a₀+Fa₁=Fa₀+a₁=0

```lean
theorem AddMonoidHom.exists_pos_forall_nsmul_eq_zero_of_add_eq_zero_of_finite_fixedPoints_comp_self
    {M : Type u} [AddCommGroup M] (F : M →+ M)
    (hfin : (Function.fixedPoints (F ∘ F)).Finite) :
    ∃ c : ℕ, 0 < c ∧ ∀ a₀ a₁ : M, a₀ + F a₁ = 0 → F a₀ + a₁ = 0 → c • a₀ = 0 ∧ c • a₁ = 0
```

### `AddMonoidHom.finite_setOf_pushPull_eq_zero`

`Thm_AddMonoidHom_finite_setOf_pushPull_eq_zero` — Finiteness of the kernel of a push–pull operator on M× M

```lean
theorem AddMonoidHom.finite_setOf_pushPull_eq_zero {M : Type*} [AddCommGroup M] (p : ℕ) (F V δ δ' : M →+ M)
    (hFV : F.comp V = p • AddMonoidHom.id M) (hVF : V.comp F = p • AddMonoidHom.id M)
    (hδδ' : δ.comp δ' = AddMonoidHom.id M) (hδ'δ : δ'.comp δ = AddMonoidHom.id M)
    (hFδ : F.comp δ = δ.comp F) (hVδ : V.comp δ = δ.comp V) (hFδ' : F.comp δ' = δ'.comp F) (hVδ' : V.comp δ' = δ'.comp V)
    (h1 : {x | x - δ (F (F x)) = 0}.Finite) (h2 : {x | x - δ' (V (V x)) = 0}.Finite) :
    {ab : M × M | (1 + p) • ab.1 + (V ab.2 + F (δ ab.2)) = 0 ∧ (F ab.1 + δ' (V ab.1)) + (1 + p) • ab.2 = 0}.Finite
```

### `AddMonoidHom.mem_range_of_smul_eq_zero_of_natCard_ker_mul_le_of_natCard_mul_le`

`Thm_AddMonoidHom_mem_range_of_smul_eq_zero_of_natCard_ker_mul_le_of_natCard_mul_le` — Counting criterion for surjectivity onto q-torsion

```lean
theorem AddMonoidHom.mem_range_of_smul_eq_zero_of_natCard_ker_mul_le_of_natCard_mul_le
    {T J : Type*} [AddCommGroup T] [AddCommGroup J] (f : T →+ J) (q : ℤ) (hT : ∀ t : T, q • t = 0)
    [Finite T] (hfinJ : Finite {x : J // q • x = 0}) (X Y : ℕ) (hY : 0 < Y)
    (hker : Nat.card f.ker * X ≤ Nat.card T * Y) (hJ : Nat.card {x : J // q • x = 0} * Y ≤ X) :
    ∀ x : J, q • x = 0 → x ∈ f.range
```

### `AddMonoidHom.natCard_ker_comp_eq_mul_of_surjective`

`Thm_AddMonoidHom_natCard_ker_comp_eq_mul_of_surjective` — Kernel orders multiply along a surjection

```lean
theorem AddMonoidHom.natCard_ker_comp_eq_mul_of_surjective
    {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]
    (f : A →+ B) (g : B →+ C) (hf : Function.Surjective f) :
    Nat.card (g.comp f).ker = Nat.card g.ker * Nat.card f.ker
```

### `AddMonoidHom.natCard_ker_eq_natCard_ker_of_pairing_adjoint`

`Thm_AddMonoidHom_natCard_ker_eq_natCard_ker_of_pairing_adjoint` — Adjoint endomorphisms under a perfect pairing have equinumerous kernels

```lean
theorem AddMonoidHom.natCard_ker_eq_natCard_ker_of_pairing_adjoint
    {P : Type*} [AddCommGroup P] [Finite P] {K : Type*} [Field K]
    (e : P → P → Kˣ)
    (hadd₁ : ∀ x x' y, e (x + x') y = e x y * e x' y) (hadd₂ : ∀ x y y', e x (y + y') = e x y * e x y')
    (hleft : ∀ x, (∀ y, e x y = 1) → x = 0) (hright : ∀ y, (∀ x, e x y = 1) → y = 0)
    (hsurj : ∀ χ : Multiplicative P →* Kˣ, ∃ y, ∀ x, e x y = χ (Multiplicative.ofAdd x))
    (T T' : P →+ P) (hadj : ∀ x y, e (T x) y = e x (T' y)) :
    Nat.card (T.ker) = Nat.card (T'.ker)
```

### `AddMonoidHom.natCard_le_pow_finrank_of_apply_eq_self_of_map_pow_smul`

`Thm_AddMonoidHom_natCard_le_pow_finrank_of_apply_eq_self_of_map_pow_smul` — Cartier–Serre bound: C-fixed vectors in a K-subspace

```lean
theorem AddMonoidHom.natCard_le_pow_finrank_of_apply_eq_self_of_map_pow_smul
    {K F M : Type*} [Field K] [Field F] [Algebra K F] [AddCommGroup M] [Module F M]
    [Module K M] [IsScalarTower K F M]
    (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]
    (C : M →+ M) (hsemi : ∀ (f : F) (m : M), C (f ^ p • m) = f • C m)
    (W : Submodule K M) [FiniteDimensional K W]
    {G : Type*} [AddCommGroup G] (φ : G →+ M) (hφ : Function.Injective φ)
    (hfix : ∀ g : G, C (φ g) = φ g) (hW : ∀ g : G, φ g ∈ W) :
    Finite G ∧ Nat.card G ≤ p ^ Module.finrank K W
```

### `AddMonoidHom.natCard_sq_le_of_isotropic`

`Thm_AddMonoidHom_natCard_sq_le_of_isotropic` — Isotropic subgroups of a left-nondegenerate pairing: #K² ≤ #V

```lean
theorem AddMonoidHom.natCard_sq_le_of_isotropic
    {V Q : Type*} [AddCommGroup V] [Finite V] [AddCommGroup Q]
    (β : V →+ V →+ Q) (hβ : ∀ v, β v = 0 → v = 0)
    (hQ : ∀ n : ℕ, n ≠ 0 → {x : Q | n • x = 0}.encard ≤ n)
    (K : AddSubgroup V) (hK : ∀ k ∈ K, ∀ k' ∈ K, β k k' = 0) :
    Nat.card K ^ 2 ≤ Nat.card V
```

### `AddMonoidHom.sub_mul_add_one_smul_eq_zero_of_comp_self_sub_smul_add_eq_zero_of_apply_eq_smul`

`Thm_AddMonoidHom_sub_mul_add_one_smul_eq_zero_of_comp_self_sub_smul_add_eq_zero_of_apply_eq_smul` — Integer eigenvalues of a quadratic endomorphism annihilate c²-tc+1

```lean
theorem AddMonoidHom.sub_mul_add_one_smul_eq_zero_of_comp_self_sub_smul_add_eq_zero_of_apply_eq_smul
    {V : Type*} [AddCommGroup V] (m : V →+ V) (t : ℤ) (hm : ∀ T, m (m T) - t • m T + T = 0)
    (P : V) (c : ℤ) (hP : m P = c • P) :
    (c ^ 2 - t * c + 1) • P = 0
```

## CategoryTheory (15)

### `CategoryTheory.Functor.exists_algEquiv_tensorProduct_descentDatum_of_corepresents_univ`

`Thm_CategoryTheory_Functor_exists_algEquiv_tensorProduct_descentDatum_of_corepresents_univ` — Descent datum on an algebra corepresenting a functor after base change

```lean
theorem CategoryTheory.Functor.exists_algEquiv_tensorProduct_descentDatum_of_corepresents_univ
    {R : Type u} [CommRing R] (F : Under (CommRingCat.of R) ⥤ Type v)
    (S₁ : Type u) [CommRing S₁] [Algebra R S₁]
    (C₁ : Type u) [CommRing C₁] [Algebra R C₁] [Algebra S₁ C₁] [IsScalarTower R S₁ C₁]
    (e : ∀ (B : Type u) [CommRing B] [Algebra R B] (j : S₁ →ₐ[R] B),
      F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B))) ≃
        {g : C₁ →ₐ[R] B // g.comp (IsScalarTower.toAlgHom R S₁ C₁) = j})
    (he : ∀ (B B' : Type u) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
      (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))),
      ((e B' (ψ.comp j)) (F.map (Under.homMk (CommRingCat.ofHom ψ.toRingHom)
        (by ext r; exact ψ.commutes r)) x)).1 = ψ.comp ((e B j) x).1) :
    ∃ φ : C₁ ⊗[R] S₁ ≃ₐ[R] S₁ ⊗[R] C₁,
      φ.toAlgHom.comp (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R S₁ C₁) (AlgHom.id R S₁)) =
        Algebra.TensorProduct.map (AlgHom.id R S₁) (IsScalarTower.toAlgHom R S₁ C₁) ∧
      (Algebra.TensorProduct.map (AlgHom.id R S₁) φ.toAlgHom).comp
          ((Algebra.TensorProduct.assoc R R R S₁ C₁ S₁).toAlgHom.comp
            (Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id R S₁))) =
        (Algebra.TensorProduct.map (AlgHom.id R S₁) (Algebra.TensorProduct.comm R C₁ S₁).toAlgHom).comp
          ((Algebra.TensorProduct.assoc R R R S₁ C₁ S₁).toAlgHom.comp
            ((Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id R S₁)).comp
              ((Algebra.TensorProduct.assoc R R R C₁ S₁ S₁).symm.toAlgHom.comp
                ((Algebra.TensorProduct.map (AlgHom.id R C₁) (Algebra.TensorProduct.comm R S₁ S₁).toAlgHom).comp
                  (Algebra.TensorProduct.assoc R R R C₁ S₁ S₁).toAlgHom)))) ∧
      ∀ (D : Type u) [CommRing D] [Algebra R D] (d : S₁ ⊗[R] S₁ →ₐ[R] D)
        (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R D)))),
        Algebra.TensorProduct.lift
            ((e D (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            (fun _ _ => Commute.all _ _) =
          (Algebra.TensorProduct.lift
            (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            ((e D (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (fun _ _ => Commute.all _ _)).comp φ.toAlgHom
```

### `CategoryTheory.Functor.exists_corepresentableBy_of_descentDatum_of_bijective_univ`

`Thm_CategoryTheory_Functor_exists_corepresentableBy_of_descentDatum_of_bijective_univ` — Affine descent criterion for corepresentability of a functor

```lean
theorem CategoryTheory.Functor.exists_corepresentableBy_of_descentDatum_of_bijective_univ
    {R : Type u} [CommRing R] (F : Under (CommRingCat.of R) ⥤ Type v)
    (hsheaf : ∀ (B B' : Under (CommRingCat.of R)) (φ : B ⟶ B'),
      φ.right.hom.Flat → Function.Surjective (PrimeSpectrum.comap φ.right.hom) →
        Function.Injective (F.map φ) ∧
        ∀ y : F.obj B', F.map (pushout.inl φ φ) y = F.map (pushout.inr φ φ) y → ∃ x : F.obj B, F.map φ x = y)
    (S₁ : Type u) [CommRing S₁] [Algebra R S₁] [Module.FaithfullyFlat R S₁]
    (C₁ : Type u) [CommRing C₁] [Algebra R C₁] [Algebra S₁ C₁] [IsScalarTower R S₁ C₁]
    (e : ∀ (B : Type u) [CommRing B] [Algebra R B] (j : S₁ →ₐ[R] B),
      F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B))) ≃
        {g : C₁ →ₐ[R] B // g.comp (IsScalarTower.toAlgHom R S₁ C₁) = j})
    (he : ∀ (B B' : Type u) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
      (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))),
      ((e B' (ψ.comp j)) (F.map (Under.homMk (CommRingCat.ofHom ψ.toRingHom)
        (by ext r; exact ψ.commutes r)) x)).1 = ψ.comp ((e B j) x).1)
    (φ : C₁ ⊗[R] S₁ ≃ₐ[R] S₁ ⊗[R] C₁)
    (hφ : ∀ (D : Type u) [CommRing D] [Algebra R D] (d : S₁ ⊗[R] S₁ →ₐ[R] D)
        (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R D)))),
        Algebra.TensorProduct.lift
            ((e D (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            (fun _ _ => Commute.all _ _) =
          (Algebra.TensorProduct.lift
            (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            ((e D (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (fun _ _ => Commute.all _ _)).comp φ.toAlgHom)
    (hbij : Function.Bijective (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S₁ C₁)
      (AlgHom.equalizer (φ.toAlgHom.comp (Algebra.TensorProduct.includeLeft : C₁ →ₐ[R] C₁ ⊗[R] S₁))
        (Algebra.TensorProduct.includeRight : C₁ →ₐ[R] S₁ ⊗[R] C₁)).val (fun s a => Commute.all _ _))) :
    ∃ C : Under (CommRingCat.of R), Nonempty (F.CorepresentableBy C)
```

### `CategoryTheory.Functor.exists_corepresentableBy_of_faithfullyFlat_of_sheaf_univ`

`Thm_CategoryTheory_Functor_exists_corepresentableBy_of_faithfullyFlat_of_sheaf_univ` — Corepresentability descends along a faithfully flat base change

```lean
theorem CategoryTheory.Functor.exists_corepresentableBy_of_faithfullyFlat_of_sheaf_univ
    {R : Type u} [CommRing R] (F : Under (CommRingCat.of R) ⥤ Type v)
    (hsheaf : ∀ (B B' : Under (CommRingCat.of R)) (φ : B ⟶ B'),
      φ.right.hom.Flat → Function.Surjective (PrimeSpectrum.comap φ.right.hom) →
        Function.Injective (F.map φ) ∧
        ∀ y : F.obj B', F.map (pushout.inl φ φ) y = F.map (pushout.inr φ φ) y → ∃ x : F.obj B, F.map φ x = y)
    (S₁ : Type u) [CommRing S₁] [Algebra R S₁] (hflat : (algebraMap R S₁).Flat)
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R S₁)))
    (C₁ : Under (CommRingCat.of R)) (c : Under.mk (CommRingCat.ofHom (algebraMap R S₁)) ⟶ C₁)
    (e : ∀ (B' : Under (CommRingCat.of R)) (b : Under.mk (CommRingCat.ofHom (algebraMap R S₁)) ⟶ B'),
      F.obj B' ≃ {g : C₁ ⟶ B' // c ≫ g = b})
    (he : ∀ (B' B'' : Under (CommRingCat.of R)) (b : Under.mk (CommRingCat.ofHom (algebraMap R S₁)) ⟶ B')
      (ψ : B' ⟶ B'') (x : F.obj B'),
      ((e B'' (b ≫ ψ)) (F.map ψ x)).1 = ((e B' b) x).1 ≫ ψ) :
    ∃ C : Under (CommRingCat.of R), Nonempty (F.CorepresentableBy C)
```

### `CategoryTheory.Functor.exists_overTotal_chart_relative_isOpenImmersion_of_representableBy_over_map`

`Thm_CategoryTheory_Functor_exists_overTotal_chart_relative_isOpenImmersion_of_representableBy_over_map` — Open chart of the total presheaf from representability over U

```lean
theorem CategoryTheory.Functor.exists_overTotal_chart_relative_isOpenImmersion_of_representableBy_over_map
    {S U : Scheme.{u}} (j : U ⟶ S) [IsOpenImmersion j]
    (G : (Over S)ᵒᵖ ⥤ Type (u + 1))
    {Y : Scheme.{u}} (p : Y ⟶ U) (e : ((Over.map j).op ⋙ G).RepresentableBy (Over.mk p)) :
    ∃ φ : uliftYoneda.{u + 1}.obj Y ⟶ G.overTotal,
      (∀ {T : Scheme.{u}} (y : T ⟶ Y),
        uliftYonedaEquiv (uliftYoneda.{u + 1}.map y ≫ φ) =
          ⟨(y ≫ p) ≫ j, e.homEquiv (Over.homMk y rfl : Over.mk (y ≫ p) ⟶ Over.mk p)⟩) ∧
      MorphismProperty.relative uliftYoneda.{u + 1} @IsOpenImmersion φ ∧
      ∀ {T : Scheme.{u}} (x : uliftYoneda.{u + 1}.obj T ⟶ G.overTotal),
        Set.range ((uliftYonedaEquiv x).1).base ⊆ Set.range j.base →
        ∃ ψ : T ⟶ Y, uliftYoneda.{u + 1}.map ψ ≫ φ = x
```

### `CategoryTheory.Functor.nonempty_algEquiv_tensorProduct_right_of_corepresentableBy_of_corepresents_under`

`Thm_CategoryTheory_Functor_nonempty_algEquiv_tensorProduct_right_of_corepresentableBy_of_corepresents_under` — Corepresenting algebra base-changes to the S₁-corepresenting algebra

```lean
theorem CategoryTheory.Functor.nonempty_algEquiv_tensorProduct_right_of_corepresentableBy_of_corepresents_under
    {R : Type u} [CommRing R] (F : Under (CommRingCat.of R) ⥤ Type v)
    (C : Under (CommRingCat.of R)) (hC : F.CorepresentableBy C)
    (S₁ : Type u) [CommRing S₁] [Algebra R S₁]
    (C₁ : Type u) [CommRing C₁] [Algebra R C₁] [Algebra S₁ C₁] [IsScalarTower R S₁ C₁]
    (e : ∀ (B' : Under (CommRingCat.of R)) (b : Under.mk (CommRingCat.ofHom (algebraMap R S₁)) ⟶ B'),
      F.obj B' ≃
        {g : Under.mk (CommRingCat.ofHom (algebraMap R C₁)) ⟶ B' //
          Under.homMk (U := Under.mk (CommRingCat.ofHom (algebraMap R S₁)))
              (V := Under.mk (CommRingCat.ofHom (algebraMap R C₁)))
              (CommRingCat.ofHom (algebraMap S₁ C₁)) (by ext r; exact (IsScalarTower.algebraMap_apply R S₁ C₁ r).symm) ≫ g = b})
    (he : ∀ (B' B'' : Under (CommRingCat.of R)) (b : Under.mk (CommRingCat.ofHom (algebraMap R S₁)) ⟶ B')
      (ψ : B' ⟶ B'') (x : F.obj B'), ((e B'' (b ≫ ψ)) (F.map ψ x)).1 = ((e B' b) x).1 ≫ ψ) :
    letI : Algebra R C.right := C.hom.hom.toAlgebra
    Nonempty (S₁ ⊗[R] C.right ≃ₐ[S₁] C₁)
```

### `CategoryTheory.IsPullback.fst_pullbackMap_of_comp_eq`

`Thm_CategoryTheory_IsPullback_fst_pullbackMap_of_comp_eq` — Base change along t is a pullback of π

```lean
theorem CategoryTheory.IsPullback.fst_pullbackMap_of_comp_eq {C : Type w} [Category.{v} C] {X X' S T : C}
    (f : X ⟶ S) (f' : X' ⟶ S) (t : T ⟶ S) (π : X' ⟶ X) (hπ : π ≫ f = f')
    [HasPullback f t] [HasPullback f' t] :
    IsPullback (pullback.fst f' t)
      (pullback.map f' t f t π (𝟙 T) (𝟙 S) (by rw [Category.comp_id, hπ]) (by rw [Category.comp_id, Category.id_comp]))
      π (pullback.fst f t)
```

### `CategoryTheory.MonoidalCategory.nonempty_iso_of_tensor_iso_tensorUnit`

`Thm_CategoryTheory_MonoidalCategory_nonempty_iso_of_tensor_iso_tensorUnit` — Tensor inverses in a braided category are unique up to isomorphism

```lean
theorem CategoryTheory.MonoidalCategory.nonempty_iso_of_tensor_iso_tensorUnit
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    {M N M' N' : C} (e : M ≅ M') (h : Nonempty (M ⊗ N ≅ 𝟙_ C)) (h' : Nonempty (M' ⊗ N' ≅ 𝟙_ C)) :
    Nonempty (N ≅ N')
```

### `CategoryTheory.MonoidalClosed.isIso_ev_app_and_isIso_curry_braiding_ev_of_tensor_iso_unit`

`Thm_CategoryTheory_MonoidalClosed_isIso_ev_app_and_isIso_curry_braiding_ev_of_tensor_iso_unit` — Tensor-invertible objects: evaluation and the bidual map are isomorphisms

```lean
theorem CategoryTheory.MonoidalClosed.isIso_ev_app_and_isIso_curry_braiding_ev_of_tensor_iso_unit
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
    {M N : C} (e : M ⊗ N ≅ 𝟙_ C) :
    (∀ X : C, IsIso ((ihom.ev M).app X)) ∧
      IsIso (MonoidalClosed.curry
        ((β_ ((ihom M).obj (𝟙_ C)) M).hom ≫ (ihom.ev M).app (𝟙_ C)))
```

### `CategoryTheory.MorphismProperty.widePullback_base`

`Thm_CategoryTheory_MorphismProperty_widePullback_base` — Base morphism of a finite wide pullback lies in P

```lean
theorem CategoryTheory.MorphismProperty.widePullback_base
    {C : Type u} [Category.{v} C] [HasPullbacks C] [HasFiniteWidePullbacks C]
    {P : MorphismProperty C} [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    {S : C} {r : ℕ} (X : Fin r → C) (f : ∀ i, X i ⟶ S) (hf : ∀ i, P (f i)) :
    P (WidePullback.base f)
```

### `CategoryTheory.Pseudofunctor.DescentData.exists_iso_toDescentData_obj_of_isStackFor_of_forall_exists_iso_pullFunctor_obj`

`Thm_CategoryTheory_Pseudofunctor_DescentData_exists_iso_toDescentData_obj_of_isStackFor_of_forall_exists_iso_pullFunctor_obj` — Effectiveness of a descent datum is local on the base

```lean
theorem CategoryTheory.Pseudofunctor.DescentData.exists_iso_toDescentData_obj_of_isStackFor_of_forall_exists_iso_pullFunctor_obj
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    (P : ∀ ⦃Z : C⦄, F.obj (.mk (op Z)) → Prop)
    (hP : ∀ ⦃Z Z' : C⦄ (g : Z' ⟶ Z) (M : F.obj (.mk (op Z))), P M → P ((F.map g.op.toLoc).toFunctor.obj M))
    (hP' : ∀ ⦃Z : C⦄ (M N : F.obj (.mk (op Z))), Nonempty (M ≅ N) → P M → P N)
    {S X : C} (f : X ⟶ S) {ι : Type t} {U : ι → C} (u : ∀ i, U i ⟶ S)
    (hS : F.IsStackFor (Presieve.ofArrows U u))
    (hZ : ∀ ⦃Z : C⦄ (z : Z ⟶ S),
      F.IsPrestackFor (Presieve.ofArrows (fun i => pullback z (u i)) (fun i => pullback.fst z (u i))))
    (hf : ∀ ⦃Z : C⦄ (z : Z ⟶ S) (M N : F.obj (.mk (op Z))), P M → P N →
      Function.Bijective ((F.toDescentData (fun _ : Unit => pullback.snd f z)).map : (M ⟶ N) → _))
    (D : F.DescentData (fun _ : Unit => f))
    (hD : ∀ i, ∃ L : F.obj (.mk (op (U i))), P L ∧
      Nonempty ((F.toDescentData (fun _ : Unit => pullback.snd f (u i))).obj L ≅
        (Pseudofunctor.DescentData.pullFunctor F (f := fun _ : Unit => f) (p := u i)
          (f' := fun _ : Unit => pullback.snd f (u i)) (α := fun j => j) (p' := fun _ => pullback.fst f (u i))
          (fun _ => pullback.condition)).obj D)) :
    ∃ L : F.obj (.mk (op S)), (∀ i, P ((F.map (u i).op.toLoc).toFunctor.obj L)) ∧
      Nonempty ((F.toDescentData (fun _ : Unit => f)).obj L ≅ D)
```

### `CategoryTheory.Sheaf.exists_iso_of_addEquiv_obj_natural`

`Thm_CategoryTheory_Sheaf_exists_iso_of_addEquiv_obj_natural` — Sheaf isomorphism from a natural family of additive bijections

```lean
theorem CategoryTheory.Sheaf.exists_iso_of_addEquiv_obj_natural
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (F G : Sheaf J Ab.{w}) (e : ∀ U : Cᵒᵖ, F.obj.obj U ≃+ G.obj.obj U)
    (he : ∀ {U V : Cᵒᵖ} (k : U ⟶ V) (s : F.obj.obj U), e V (F.obj.map k s) = G.obj.map k (e U s)) :
    ∃ φ : F ≅ G, ∀ (U : Cᵒᵖ) (s : F.obj.obj U), φ.hom.hom.app U s = e U s
```

### `CategoryTheory.Sheaf.preservesInjectiveObjects_sheafCompose_uliftFunctor`

`Thm_CategoryTheory_Sheaf_preservesInjectiveObjects_sheafCompose_uliftFunctor` — Universe lifting of coefficients preserves injective abelian sheaves

```lean
theorem CategoryTheory.Sheaf.preservesInjectiveObjects_sheafCompose_uliftFunctor
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) :
    (sheafCompose J AddCommGrpCat.uliftFunctor.{u+1, u} :
      Sheaf J AddCommGrpCat.{u} ⥤ Sheaf J AddCommGrpCat.{u+1}).PreservesInjectiveObjects
```

### `CategoryTheory.ShortComplex.ShortExact.extClass_eq_zero_iff_exists_section_g`

`Thm_CategoryTheory_ShortComplex_ShortExact_extClass_eq_zero_iff_exists_section_g` — extClass = 0 iff g admits a section

```lean
theorem CategoryTheory.ShortComplex.ShortExact.extClass_eq_zero_iff_exists_section_g
    {C : Type u} [CategoryTheory.Category.{v} C] [CategoryTheory.Abelian C]
    [CategoryTheory.HasExt.{w} C] {S : CategoryTheory.ShortComplex C} (hS : S.ShortExact) :
    hS.extClass = 0 ↔ ∃ s : S.X₃ ⟶ S.X₂, s ≫ S.g = 𝟙 S.X₃
```

### `CategoryTheory.ShortComplex.shortExact_of_mono_cokernel`

`Thm_CategoryTheory_ShortComplex_shortExact_of_mono_cokernel` — A monomorphism and its cokernel form a short exact sequence

```lean
theorem CategoryTheory.ShortComplex.shortExact_of_mono_cokernel
    {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] {X Y : 𝒜} (f : X ⟶ Y) [Mono f] :
    (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact
```

### `CategoryTheory.Under.exists_finite_faithfullyFlat_equiv_ringHom_comp_algebraMap_eq_of_free`

`Thm_CategoryTheory_Under_exists_finite_faithfullyFlat_equiv_ringHom_comp_algebraMap_eq_of_free` — Base change W⊗_{R_0}H corepresents R₀-algebra maps from H

```lean
theorem CategoryTheory.Under.exists_finite_faithfullyFlat_equiv_ringHom_comp_algebraMap_eq_of_free
    (R₀ : Type) [CommRing R₀] (H : Type) [CommRing H] [Algebra R₀ H] [Module.Finite R₀ H] [Module.Free R₀ H] [Nontrivial H]
    (W : Type) [CommRing W] [Algebra R₀ W] :
    ∃ (C₁ : Type) (_ : CommRing C₁) (_ : Algebra R₀ C₁) (_ : Algebra W C₁) (_ : IsScalarTower R₀ W C₁),
      Module.Finite W C₁ ∧ Module.FaithfullyFlat W C₁ ∧
      ∃ e : ∀ (B' : Under (CommRingCat.of R₀)) (b : Under.mk (CommRingCat.ofHom (algebraMap R₀ W)) ⟶ B'),
          {χ : H →+* B'.right // χ.comp (algebraMap R₀ H) = B'.hom.hom} ≃
            {g : Under.mk (CommRingCat.ofHom (algebraMap R₀ C₁)) ⟶ B' //
              Under.homMk (U := Under.mk (CommRingCat.ofHom (algebraMap R₀ W)))
                  (V := Under.mk (CommRingCat.ofHom (algebraMap R₀ C₁)))
                  (CommRingCat.ofHom (algebraMap W C₁)) (by ext r; exact (IsScalarTower.algebraMap_apply R₀ W C₁ r).symm) ≫ g = b},
        ∀ (B' B'' : Under (CommRingCat.of R₀)) (b : Under.mk (CommRingCat.ofHom (algebraMap R₀ W)) ⟶ B')
          (ψ : B' ⟶ B'') (χ : {χ : H →+* B'.right // χ.comp (algebraMap R₀ H) = B'.hom.hom}),
          ((e B'' (b ≫ ψ)) ⟨ψ.right.hom.comp χ.1, by rw [RingHom.comp_assoc, χ.2, ← CommRingCat.hom_comp, Under.w ψ]⟩).1 =
            ((e B' b) χ).1 ≫ ψ
```

## DoubleComplex (15)

### `DoubleComplex.Convergence.finite_E2_q0`

`Thm_DoubleComplex_Convergence_finite_E2_q0` — Finiteness of E₂^{p,0} from finite Hⁿ and finite higher rows

```lean
theorem DoubleComplex.Convergence.finite_E2_q0 {R : Type u} [CommRing R] [IsNoetherianRing R]
    {E₂ : ℕ → ℕ → Type u} [∀ p q, AddCommGroup (E₂ p q)] [∀ p q, Module R (E₂ p q)]
    {H : ℕ → Type u} [∀ n, AddCommGroup (H n)] [∀ n, Module R (H n)] {N : ℕ}
    (conv : DoubleComplex.Convergence R E₂ H N)
    (hH : ∀ n, Module.Finite R (H n)) (hE₂ : ∀ p q, 1 ≤ q → Module.Finite R (E₂ p q))
    (p : ℕ) (hp : p ≤ N) : Module.Finite R (E₂ p 0)
```

### `DoubleComplex.boundedSpectralSequence`

`Thm_DoubleComplex_boundedSpectralSequence` — Convergence data for bounded double complexes

```lean
theorem DoubleComplex.boundedSpectralSequence : DoubleComplex.BoundedSpectralSequence.{u}
```

### `DoubleComplex.exists_HTot_equiv_mk_eq_mk_single_of_rows_exact_of_augmentation`

`Thm_DoubleComplex_exists_HTot_equiv_mk_eq_mk_single_of_rows_exact_of_augmentation` — Pinned edge isomorphism Hⁿ(A) ≅ Hⁿ(Tot D)

```lean
theorem DoubleComplex.exists_HTot_equiv_mk_eq_mk_single_of_rows_exact_of_augmentation
    {R : Type u} [CommRing R] (D : DoubleComplex.Bounded R)
    (A : ℕ → Type u) [∀ m, AddCommGroup (A m)] [∀ m, Module R (A m)]
    (dA : ∀ m, A m →ₗ[R] A (m + 1)) (ε : ∀ m, A m →ₗ[R] D.C 0 m)
    (hε : ∀ m, Function.Injective (ε m))
    (hεd : ∀ m, D.dV 0 m ∘ₗ ε m = ε (m + 1) ∘ₗ dA m)
    (hker : ∀ m, LinearMap.ker (D.dH 0 m) = LinearMap.range (ε m))
    (hrows : ∀ p m, LinearMap.ker (D.dH (p + 1) m) ≤ LinearMap.range (D.dH p m)) :
    (∃ e : LinearMap.ker (dA 0) ≃ₗ[R] DoubleComplex.HTot D 0,
        ∀ (a : A 0) (ha : a ∈ LinearMap.ker (dA 0)),
          ∃ hE : Pi.single (M := fun i : DoubleComplex.Diag 0 => D.C i.1.1 i.1.2) ⟨(0, 0), rfl⟩ (ε 0 a)
              ∈ LinearMap.ker (DoubleComplex.dTot D 0),
            e ⟨a, ha⟩ = Submodule.Quotient.mk ⟨_, hE⟩) ∧
      ∀ n : ℕ, ∃ e : (LinearMap.ker (dA (n + 1)) ⧸
            (LinearMap.range (dA n)).comap (LinearMap.ker (dA (n + 1))).subtype) ≃ₗ[R] DoubleComplex.HTot D (n + 1),
        ∀ (a : A (n + 1)) (ha : a ∈ LinearMap.ker (dA (n + 1))),
          ∃ hE : Pi.single (M := fun i : DoubleComplex.Diag (n + 1) => D.C i.1.1 i.1.2) ⟨(0, n + 1), by omega⟩ (ε (n + 1) a)
              ∈ LinearMap.ker (DoubleComplex.dTot D (n + 1)),
            e (Submodule.Quotient.mk ⟨a, ha⟩) = Submodule.Quotient.mk ⟨_, hE⟩
```

### `DoubleComplex.exists_HTot_equiv_of_levelwise_equiv_pinned`

`Thm_DoubleComplex_exists_HTot_equiv_of_levelwise_equiv_pinned` — Pinned functoriality of total cohomology of double complexes

```lean
theorem DoubleComplex.exists_HTot_equiv_of_levelwise_equiv_pinned
    {R : Type u} [CommRing R] (D D' : DoubleComplex.Bounded R)
    (e : ∀ p q : ℕ, D.C p q ≃ₗ[R] D'.C p q)
    (hH : ∀ (p q : ℕ) (x : D.C p q), e (p + 1) q (D.dH p q x) = D'.dH p q (e p q x))
    (hV : ∀ (p q : ℕ) (x : D.C p q), e p (q + 1) (D.dV p q x) = D'.dV p q (e p q x))
    (n : ℕ) :
    ∃ E : DoubleComplex.HTot D n ≃ₗ[R] DoubleComplex.HTot D' n,
      ∀ c : ↥(LinearMap.ker (DoubleComplex.dTot D n)),
        ∃ hc : (fun i : DoubleComplex.Diag n => e i.1.1 i.1.2 (c.1 i)) ∈ LinearMap.ker (DoubleComplex.dTot D' n),
          E (Submodule.Quotient.mk c) = Submodule.Quotient.mk ⟨_, hc⟩
```

### `DoubleComplex.exists_HTot_transpose_equiv_mk_eq_mk_swap`

`Thm_DoubleComplex_exists_HTot_transpose_equiv_mk_eq_mk_swap` — Signed transposition on total cohomology of a bounded double complex

```lean
theorem DoubleComplex.exists_HTot_transpose_equiv_mk_eq_mk_swap
    {R : Type u} [CommRing R] (D : DoubleComplex.Bounded R) (n : ℕ) :
    ∃ e : DoubleComplex.HTot (DoubleComplex.transpose D) n ≃ₗ[R] DoubleComplex.HTot D n,
      ∀ (z : DoubleComplex.Tot (DoubleComplex.transpose D) n)
        (hz : z ∈ LinearMap.ker (DoubleComplex.dTot (DoubleComplex.transpose D) n)),
        ∃ hSz : (fun pq : DoubleComplex.Diag n =>
            ((-1 : ℤ) ^ (pq.1.1 * pq.1.2)) • (show D.C pq.1.1 pq.1.2 from z ⟨(pq.1.2, pq.1.1), by have := pq.2; omega⟩))
              ∈ LinearMap.ker (DoubleComplex.dTot D n),
          e (Submodule.Quotient.mk ⟨z, hz⟩) = Submodule.Quotient.mk ⟨_, hSz⟩
```

### `DoubleComplex.finite_HTot_and_sum_finrank_HTot_eq_sub_of_rowShift`

`Thm_DoubleComplex_finite_HTot_and_sum_finrank_HTot_eq_sub_of_rowShift` — Peeling off the bottom row of a bounded double complex

```lean
theorem DoubleComplex.finite_HTot_and_sum_finrank_HTot_eq_sub_of_rowShift
    {k : Type u} [Field k] (D : DoubleComplex.Bounded k)
    (hup : ∀ n : ℕ, Module.Finite k (DoubleComplex.HTot
        ({ C := fun p q => D.C p (q + 1), dH := fun p q => D.dH p (q + 1), dV := fun p q => D.dV p (q + 1),
                dH_sq := fun p q => D.dH_sq p (q + 1), dV_sq := fun p q => D.dV_sq p (q + 1),
                dHV_comm := fun p q => D.dHV_comm p (q + 1), N := D.N,
                hBound := fun p q h => D.hBound p (q + 1) (h.imp id Nat.le_succ_of_le) } : DoubleComplex.Bounded k) n))
    (hrow : ∀ p : ℕ, Module.Finite k (DoubleComplex.colH (DoubleComplex.transpose D) 0 p)) :
    (∀ n : ℕ, Module.Finite k (DoubleComplex.HTot D n)) ∧
      ∑ n ∈ Finset.range (2 * D.N), (-1 : ℤ) ^ n * (Module.finrank k (DoubleComplex.HTot D n) : ℤ) =
        ∑ p ∈ Finset.range (2 * D.N),
            (-1 : ℤ) ^ p * (Module.finrank k (DoubleComplex.colH (DoubleComplex.transpose D) 0 p) : ℤ) -
          ∑ n ∈ Finset.range (2 * D.N), (-1 : ℤ) ^ n * (Module.finrank k (DoubleComplex.HTot
            ({ C := fun p q => D.C p (q + 1), dH := fun p q => D.dH p (q + 1), dV := fun p q => D.dV p (q + 1),
                dH_sq := fun p q => D.dH_sq p (q + 1), dV_sq := fun p q => D.dV_sq p (q + 1),
                dHV_comm := fun p q => D.dHV_comm p (q + 1), N := D.N,
                hBound := fun p q h => D.hBound p (q + 1) (h.imp id Nat.le_succ_of_le) } : DoubleComplex.Bounded k) n) : ℤ)
```

### `DoubleComplex.finite_HTot_and_sum_finrank_HTot_eq_sum_finrank_colH`

`Thm_DoubleComplex_finite_HTot_and_sum_finrank_HTot_eq_sum_finrank_colH` — Euler characteristic of a bounded double complex via columns

```lean
theorem DoubleComplex.finite_HTot_and_sum_finrank_HTot_eq_sum_finrank_colH
    {k : Type u} [Field k] (D : DoubleComplex.Bounded k)
    (hcol : ∀ p q : ℕ, Module.Finite k (DoubleComplex.colH D p q)) :
    (∀ n : ℕ, Module.Finite k (DoubleComplex.HTot D n)) ∧
      ∑ n ∈ Finset.range (2 * D.N), (-1 : ℤ) ^ n * (Module.finrank k (DoubleComplex.HTot D n) : ℤ) =
        ∑ p ∈ Finset.range D.N, ∑ q ∈ Finset.range D.N,
          (-1 : ℤ) ^ (p + q) * (Module.finrank k (DoubleComplex.colH D p q) : ℤ)
```

### `DoubleComplex.nonempty_HTot_equiv_E2II_zero_of_forall_subsingleton_colH_transpose`

`Thm_DoubleComplex_nonempty_HTot_equiv_E2II_zero_of_forall_subsingleton_colH_transpose` — Total cohomology equals ''E₂^{0,n} for rows exact in positive degree

```lean
theorem DoubleComplex.nonempty_HTot_equiv_E2II_zero_of_forall_subsingleton_colH_transpose
    {R : Type u} [CommRing R] (D : DoubleComplex.Bounded R)
    (hex : ∀ p q : ℕ, Subsingleton (DoubleComplex.colH (DoubleComplex.transpose D) q (p + 1)))
    (n : ℕ) :
    Nonempty (DoubleComplex.HTot D n ≃ₗ[R] DoubleComplex.E₂II D 0 n)
```

### `DoubleComplex.nonempty_HTot_equiv_of_levelwise_equiv`

`Thm_DoubleComplex_nonempty_HTot_equiv_of_levelwise_equiv` — Levelwise isomorphic bounded double complexes have isomorphic total cohomology

```lean
theorem DoubleComplex.nonempty_HTot_equiv_of_levelwise_equiv
    {R : Type u} [CommRing R] (D D' : DoubleComplex.Bounded R)
    (e : ∀ p q : ℕ, D.C p q ≃ₗ[R] D'.C p q)
    (hH : ∀ (p q : ℕ) (x : D.C p q), e (p + 1) q (D.dH p q x) = D'.dH p q (e p q x))
    (hV : ∀ (p q : ℕ) (x : D.C p q), e p (q + 1) (D.dV p q x) = D'.dV p q (e p q x))
    (n : ℕ) :
    Nonempty (DoubleComplex.HTot D n ≃ₗ[R] DoubleComplex.HTot D' n)
```

### `DoubleComplex.nonempty_HTot_equiv_of_rows_exact_of_augmentation`

`Thm_DoubleComplex_nonempty_HTot_equiv_of_rows_exact_of_augmentation` — Augmented staircase lemma for bounded double complexes

```lean
theorem DoubleComplex.nonempty_HTot_equiv_of_rows_exact_of_augmentation
    {R : Type u} [CommRing R] (D : DoubleComplex.Bounded R)
    (A : ℕ → Type u) [∀ m, AddCommGroup (A m)] [∀ m, Module R (A m)]
    (dA : ∀ m, A m →ₗ[R] A (m + 1)) (ε : ∀ m, A m →ₗ[R] D.C 0 m)
    (hε : ∀ m, Function.Injective (ε m))
    (hεd : ∀ m, D.dV 0 m ∘ₗ ε m = ε (m + 1) ∘ₗ dA m)
    (hker : ∀ m, LinearMap.ker (D.dH 0 m) = LinearMap.range (ε m))
    (hrows : ∀ p m, LinearMap.ker (D.dH (p + 1) m) ≤ LinearMap.range (D.dH p m)) :
    Nonempty (DoubleComplex.HTot D 0 ≃ₗ[R] LinearMap.ker (dA 0)) ∧
      ∀ n : ℕ, Nonempty (DoubleComplex.HTot D (n + 1) ≃ₗ[R]
        (LinearMap.ker (dA (n + 1)) ⧸ (LinearMap.range (dA n)).comap (LinearMap.ker (dA (n + 1))).subtype))
```

### `DoubleComplex.nonempty_HTot_equiv_prod_of_levelwise_equiv_prod`

`Thm_DoubleComplex_nonempty_HTot_equiv_prod_of_levelwise_equiv_prod` — Total cohomology of a bounded double complex is additive

```lean
theorem DoubleComplex.nonempty_HTot_equiv_prod_of_levelwise_equiv_prod
    {R : Type u} [CommRing R] (S A B : DoubleComplex.Bounded R)
    (e : ∀ p q : ℕ, S.C p q ≃ₗ[R] (A.C p q × B.C p q))
    (hH : ∀ (p q : ℕ) (x : S.C p q), e (p + 1) q (S.dH p q x) = (A.dH p q (e p q x).1, B.dH p q (e p q x).2))
    (hV : ∀ (p q : ℕ) (x : S.C p q), e p (q + 1) (S.dV p q x) = (A.dV p q (e p q x).1, B.dV p q (e p q x).2))
    (n : ℕ) :
    Nonempty (DoubleComplex.HTot S n ≃ₗ[R] (DoubleComplex.HTot A n × DoubleComplex.HTot B n))
```

### `DoubleComplex.nonempty_HTot_transpose_equiv`

`Thm_DoubleComplex_nonempty_HTot_transpose_equiv` — Transposing a bounded double complex preserves total cohomology

```lean
theorem DoubleComplex.nonempty_HTot_transpose_equiv
    {R : Type u} [CommRing R] (D : DoubleComplex.Bounded R) (n : ℕ) :
    Nonempty (DoubleComplex.HTot (DoubleComplex.transpose D) n ≃ₗ[R] DoubleComplex.HTot D n)
```

### `DoubleComplex.subsingleton_HTot_of_colContraction`

`Thm_DoubleComplex_subsingleton_HTot_of_colContraction` — Total complex acyclic from a horizontal-equivariant vertical contraction

```lean
theorem DoubleComplex.subsingleton_HTot_of_colContraction
    {R : Type u} [CommRing R] (T : DoubleComplex.Bounded R)
    (s : ∀ p q : ℕ, T.C p (q + 1) →ₗ[R] T.C p q)
    (h0 : ∀ (p : ℕ) (x : T.C p 0), s p 0 (T.dV p 0 x) = x)
    (hs : ∀ (p q : ℕ) (x : T.C p (q + 1)), s p (q + 1) (T.dV p (q + 1) x) + T.dV p q (s p q x) = x)
    (hsH : ∀ (p q : ℕ) (x : T.C p (q + 1)), s (p + 1) q (T.dH p (q + 1) x) = T.dH p q (s p q x))
    (n : ℕ) :
    Subsingleton (DoubleComplex.HTot T n)
```

### `DoubleComplex.subsingleton_HTot_of_forall_subsingleton_colH`

`Thm_DoubleComplex_subsingleton_HTot_of_forall_subsingleton_colH` — Bounded double complex with exact columns has acyclic total complex

```lean
theorem DoubleComplex.subsingleton_HTot_of_forall_subsingleton_colH
    {R : Type u} [CommRing R] (D : DoubleComplex.Bounded R)
    (h : ∀ p q : ℕ, Subsingleton (DoubleComplex.colH D p q)) (n : ℕ) :
    Subsingleton (DoubleComplex.HTot D n)
```

### `DoubleComplex.subsingleton_HTot_of_rowContraction`

`Thm_DoubleComplex_subsingleton_HTot_of_rowContraction` — Row contraction kills total cohomology of a bounded double complex

```lean
theorem DoubleComplex.subsingleton_HTot_of_rowContraction
    {R : Type u} [CommRing R] (T : DoubleComplex.Bounded R)
    (s : ∀ p q : ℕ, T.C (p + 1) q →ₗ[R] T.C p q)
    (h0 : ∀ (q : ℕ) (x : T.C 0 q), s 0 q (T.dH 0 q x) = x)
    (hs : ∀ (p q : ℕ) (x : T.C (p + 1) q), s (p + 1) q (T.dH (p + 1) q x) + T.dH p q (s p q x) = x)
    (hsV : ∀ (p q : ℕ) (x : T.C (p + 1) q), s p (q + 1) (T.dV (p + 1) q x) = T.dV p q (s p q x))
    (n : ℕ) :
    Subsingleton (DoubleComplex.HTot T n)
```

## AddSubgroup (11)

### `AddSubgroup.addGroup_fg_of_le_of_addGroup_fg`

`Thm_AddSubgroup_addGroup_fg_of_le_of_addGroup_fg` — Subgroups of finitely generated abelian groups are finitely generated

```lean
theorem AddSubgroup.addGroup_fg_of_le_of_addGroup_fg {A : Type} [AddCommGroup A] {H₁ H₂ : AddSubgroup A}
    (hle : H₁ ≤ H₂) (hfg : AddGroup.FG ↥H₂) : AddGroup.FG ↥H₁
```

### `AddSubgroup.closure_range_divisible_of_prime_tower`

`Thm_AddSubgroup_closure_range_divisible_of_prime_tower` — Nonzero divisible subgroup from a coherent p-power torsion tower

```lean
theorem AddSubgroup.closure_range_divisible_of_prime_tower
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (p : ℕ) (hp : p.Prime) (f : ℕ → M)
    (htrans : ∀ n, p • f (n + 1) = f n) (htors : ∀ n, p ^ n • f n = 0)
    (I : Set R) (hkill : ∀ t ∈ I, ∀ n, t • f n = 0) (hne : ∃ n, f n ≠ 0) :
    AddSubgroup.closure (Set.range f) ≠ ⊥ ∧
      (∀ z ∈ AddSubgroup.closure (Set.range f), ∀ k : ℕ, 0 < k →
        ∃ z' ∈ AddSubgroup.closure (Set.range f), k • z' = z) ∧
      (∀ t ∈ I, ∀ z ∈ AddSubgroup.closure (Set.range f), t • z = 0)
```

### `AddSubgroup.exists_chain_card_quotient_eq_forall_sub_mem_or_sub_smul_mem`

`Thm_AddSubgroup_exists_chain_card_quotient_eq_forall_sub_mem_or_sub_smul_mem` — Admissible filtration with steps of prime order q

```lean
theorem AddSubgroup.exists_chain_card_quotient_eq_forall_sub_mem_or_sub_smul_mem
    {Γ M : Type*} [Group Γ] [AddCommGroup M] (φ : Γ →* AddAut M) {q : ℕ} (hq : q.Prime)
    (χ : Γ →* (ZMod q)ˣ) (A B : AddSubgroup M) (hAB : A ≤ B)
    (hfin : Finite (↥B ⧸ A.addSubgroupOf B))
    (hA : ∀ g : Γ, ∀ x ∈ A, φ g x ∈ A) (hB : ∀ g : Γ, ∀ x ∈ B, φ g x ∈ B)
    (hqB : ∀ x ∈ B, q • x ∈ A)
    (h : ∀ g : Γ, ∀ x ∈ B,
      φ g (φ g x - (χ g : ZMod q).val • x) - (φ g x - (χ g : ZMod q).val • x) ∈ A) :
    ∃ (n : ℕ) (step : Fin (n + 1) → AddSubgroup M), step 0 = A ∧ step (Fin.last n) = B ∧
      ∀ i : Fin n, step i.castSucc ≤ step i.succ ∧
        Nat.card (↥(step i.succ) ⧸ (step i.castSucc).addSubgroupOf (step i.succ)) = q ∧
        ((∀ g : Γ, ∀ x ∈ step i.succ, φ g x - x ∈ step i.castSucc) ∨
         (∀ g : Γ, ∀ x ∈ step i.succ, φ g x - (χ g : ZMod q).val • x ∈ step i.castSucc))
```

### `AddSubgroup.exists_continuousLinearEquiv_prod_mem_iff_of_discreteTopology`

`Thm_AddSubgroup_exists_continuousLinearEquiv_prod_mem_iff_of_discreteTopology` — Adapted coordinates for a discrete subgroup of a real vector space

```lean
theorem AddSubgroup.exists_continuousLinearEquiv_prod_mem_iff_of_discreteTopology
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (L : AddSubgroup V) [DiscreteTopology L] :
    ∃ (a b : ℕ) (T : ((Fin a → ℝ) × (Fin b → ℝ)) ≃L[ℝ] V),
      ∀ x : V, x ∈ L ↔ ∃ k : Fin a → ℤ, T (fun i => (k i : ℝ), 0) = x
```

### `AddSubgroup.exists_forall_mem_iff_single_sub_mul_mem_of_sum_mul_eq_one`

`Thm_AddSubgroup_exists_forall_mem_iff_single_sub_mul_mem_of_sum_mul_eq_one` — Unipotent splitting of an 𝒪-stable subgroup of D²

```lean
theorem AddSubgroup.exists_forall_mem_iff_single_sub_mul_mem_of_sum_mul_eq_one
    {D : Type*} [Ring D] (O : Set D) (M : AddSubgroup (Fin 2 → D))
    (hM : ∀ m ∈ M, ∀ o ∈ O, (fun i => m i * o) ∈ M)
    {ι : Type*} (t : Finset ι) (x y : ι → D)
    (hx : ∀ k ∈ t, ∃ m ∈ M, m 1 = x k)
    (hy : ∀ k ∈ t, ∀ m ∈ M, y k * m 1 ∈ O)
    (hsum : ∑ k ∈ t, x k * y k = 1) :
    ∃ u : D, ∀ v : Fin 2 → D,
      v ∈ M ↔ (Pi.single (0 : Fin 2) (v 0 - u * v 1) ∈ M ∧ ∃ m ∈ M, m 1 = v 1)
```

### `AddSubgroup.exists_forall_sum_prod_inv_one_add_abs_sq_le_of_discreteTopology`

`Thm_AddSubgroup_exists_forall_sum_prod_inv_one_add_abs_sq_le_of_discreteTopology` — Uniform bound for product weights over a discrete subgroup

```lean
theorem AddSubgroup.exists_forall_sum_prod_inv_one_add_abs_sq_le_of_discreteTopology
    {r : ℕ} (Γ : AddSubgroup (Fin r → ℝ)) [DiscreteTopology Γ] :
    ∃ K : ℝ, ∀ (y : Fin r → ℝ) (F : Finset (Fin r → ℝ)), (↑F : Set (Fin r → ℝ)) ⊆ Γ →
      ∑ x ∈ F, ∏ k, (1 + |y k + x k|)⁻¹ ^ 2 ≤ K
```

### `AddSubgroup.exists_units_zmod_val_smul_eq_of_addOrderOf_eq_of_mem_zmultiples`

`Thm_AddSubgroup_exists_units_zmod_val_smul_eq_of_addOrderOf_eq_of_mem_zmultiples` — Equal-order points in one cyclic subgroup differ by a unit of ℤ/ℓ

```lean
theorem AddSubgroup.exists_units_zmod_val_smul_eq_of_addOrderOf_eq_of_mem_zmultiples
    {G : Type*} [AddCommGroup G] (ℓ : ℕ) [NeZero ℓ] (P P' : G)
    (hP : addOrderOf P = ℓ) (hP' : addOrderOf P' = ℓ) (h : P' ∈ AddSubgroup.zmultiples P) :
    ∃ d : (ZMod ℓ)ˣ, P' = (d : ZMod ℓ).val • P
```

### `AddSubgroup.finite_setOf_mem_forall_abs_le_snd_eq_of_discreteTopology`

`Thm_AddSubgroup_finite_setOf_mem_forall_abs_le_snd_eq_of_discreteTopology` — Discrete subgroups of ℝ^r × ℤᶜ meet boxes finitely

```lean
theorem AddSubgroup.finite_setOf_mem_forall_abs_le_snd_eq_of_discreteTopology
    {r c : ℕ} (Λ : AddSubgroup ((Fin r → ℝ) × (Fin c → ℤ))) [DiscreteTopology Λ] (R : ℝ) (k₀ : Fin c → ℤ) :
    {γ : (Fin r → ℝ) × (Fin c → ℤ) | γ ∈ Λ ∧ (∀ i, |γ.1 i| ≤ R) ∧ γ.2 = k₀}.Finite
```

### `AddSubgroup.forall_mem_of_forall_pairing_eq_one_of_natCard_mul_eq`

`Thm_AddSubgroup_forall_mem_of_forall_pairing_eq_one_of_natCard_mul_eq` — Isotropic subgroups of complementary order are mutual annihilators

```lean
theorem AddSubgroup.forall_mem_of_forall_pairing_eq_one_of_natCard_mul_eq
    {G : Type} [AddCommGroup G] [Finite G] {L : Type} [Field L] [CharZero L] (n : ℕ) (hn : n ≠ 0)
    (B : G → G → L)
    (hval : ∀ x y : G, B x y ^ n = 1)
    (hadd₁ : ∀ x x' y : G, B (x + x') y = B x y * B x' y)
    (hadd₂ : ∀ x y y' : G, B x (y + y') = B x y * B x y')
    (hleft : ∀ x : G, (∀ y : G, B x y = 1) → x = 0)
    (hright : ∀ y : G, (∀ x : G, B x y = 1) → y = 0)
    (T F : AddSubgroup G) (hiso : ∀ t ∈ T, ∀ f ∈ F, B t f = 1)
    (hcard : Nat.card T * Nat.card F = Nat.card G) :
    (∀ x : G, (∀ f ∈ F, B x f = 1) → x ∈ T) ∧ (∀ y : G, (∀ t ∈ T, B t y = 1) → y ∈ F)
```

### `AddSubgroup.mem_of_forall_pairing_annihilator_eq_one_of_nondegenerate`

`Thm_AddSubgroup_mem_of_forall_pairing_annihilator_eq_one_of_nondegenerate` — Double annihilator of a subgroup under a non-degenerate pairing

```lean
theorem AddSubgroup.mem_of_forall_pairing_annihilator_eq_one_of_nondegenerate
    {G : Type} [AddCommGroup G] [Finite G] {L : Type} [Field L] (n : ℕ) (hn : n ≠ 0)
    (B : G → G → L)
    (hval : ∀ x y : G, B x y ^ n = 1)
    (hadd₁ : ∀ x x' y : G, B (x + x') y = B x y * B x' y)
    (hadd₂ : ∀ x y y' : G, B x (y + y') = B x y * B x y')
    (hleft : ∀ x : G, (∀ y : G, B x y = 1) → x = 0)
    (hright : ∀ y : G, (∀ x : G, B x y = 1) → y = 0)
    (A : AddSubgroup G) (x : G)
    (hx : ∀ y : G, (∀ a ∈ A, B a y = 1) → B x y = 1) :
    x ∈ A
```

### `AddSubgroup.natCard_eq_pow_finrank_span_of_forall_apply_eq_self_of_map_pow_smul`

`Thm_AddSubgroup_natCard_eq_pow_finrank_span_of_forall_apply_eq_self_of_map_pow_smul` — Counting C-fixed finite subgroups: #Y=p^{dim_Kspan_K Y}

```lean
theorem AddSubgroup.natCard_eq_pow_finrank_span_of_forall_apply_eq_self_of_map_pow_smul
    {K F M : Type*} [Field K] [Field F] [Algebra K F] [AddCommGroup M] [Module F M]
    [Module K M] [IsScalarTower K F M] (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]
    (C : M →+ M) (hsemi : ∀ (f : F) (m : M), C (f ^ p • m) = f • C m)
    (Y : AddSubgroup M) [Finite Y] (hfix : ∀ y ∈ Y, C y = y) :
    Nat.card Y = p ^ Module.finrank K (Submodule.span K (Y : Set M))
```

## ContinuousLinearMap (10)

### `ContinuousLinearMap.apply_comp_comp_torusEmb_eq_sum_laurentCoeff_mul_of_apply_fourier_eq`

`Thm_ContinuousLinearMap_apply_comp_comp_torusEmb_eq_sum_laurentCoeff_mul_of_apply_fourier_eq` — Laurent expansion of monomials pulled back to the torus

```lean
theorem ContinuousLinearMap.apply_comp_comp_torusEmb_eq_sum_laurentCoeff_mul_of_apply_fourier_eq
    {ιL : Type} (d : ℕ) (XK : Set (Fin d → ℂ × ℂ)) (X : Set (ιL → ℂ × ℂ))
    (emb : C((Fin d → AddCircle (1 : ℝ)), XK))
    (hemb : ∀ (θ : Fin d → AddCircle (1 : ℝ)) (i : Fin d),
      ((emb θ : XK) : Fin d → ℂ × ℂ) i = ((fourier 1 (θ i) : ℂ), (fourier (-1) (θ i) : ℂ)))
    (w' : Fin d → ιL) (ρ s ζ N : Fin d → ℂ) (hN : ∀ i : Fin d, N i ≠ 0)
    (bc : C(XK, X))
    (hbc1 : ∀ (x : XK) (i : Fin d), (((bc x : X) : ιL → ℂ × ℂ) (w' i)).1 =
      ρ i * s i * ((((x : XK) : Fin d → ℂ × ℂ) i).1 + (((x : XK) : Fin d → ℂ × ℂ) i).2))
    (hbc2 : ∀ (x : XK) (i : Fin d), (((bc x : X) : ιL → ℂ × ℂ) (w' i)).2 =
      N i * ζ i + ((((x : XK) : Fin d → ℂ × ℂ) i).1 * (((x : XK) : Fin d → ℂ × ℂ) i).2 - 1))
    (μ : C((Fin d → AddCircle (1 : ℝ)), ℂ) →L[ℂ] ℂ) (c : (Fin d → ℤ) → ℂ)
    (hc : ∀ (n : Fin d → ℤ) (e : C((Fin d → AddCircle (1 : ℝ)), ℂ)),
        (∀ θ, e θ = ∏ i, fourier (n i) (θ i)) → μ e = c n)
    (ks js : Fin d → ℕ) (g : C(X, ℂ))
    (hg : ∀ x : X, g x = ∏ i : Fin d,
      (((x : X) : ιL → ℂ × ℂ) (w' i)).1 ^ ks i * ((N i)⁻¹ * (((x : X) : ιL → ℂ × ℂ) (w' i)).2) ^ js i) :
    μ ((g.comp bc).comp emb) =
      ∑ n ∈ Fintype.piFinset (fun i : Fin d => Finset.Icc (-(ks i : ℤ)) (ks i)),
        (∏ i : Fin d, (ρ i * s i) ^ ks i * ζ i ^ js i *
          ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks i : LaurentPolynomial ℂ).coeff (n i)) * c n
```

### `ContinuousLinearMap.comp_eq_of_forall_apply_eq_integral_smul_apply_of_convolution`

`Thm_ContinuousLinearMap_comp_eq_of_forall_apply_eq_integral_smul_apply_of_convolution` — Weighted averages of a compact group representation compose by convolution

```lean
theorem ContinuousLinearMap.comp_eq_of_forall_apply_eq_integral_smul_apply_of_convolution
    {C : Type*} [Group C] [TopologicalSpace C] [IsTopologicalGroup C] [CompactSpace C] [T2Space C]
    [MeasurableSpace C] [BorelSpace C] (μ : Measure C) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : C →* (H →L[ℂ] H)) (B : ℝ) (hSb : ∀ c : C, ‖S c‖ ≤ B) (hSc : ∀ v : H, Continuous fun c : C => S c v) :
    (∀ (w₁ w₂ : C → ℂ), Continuous w₁ → Continuous w₂ →
      ∀ (A₁ A₂ A₁₂ : H →L[ℂ] H),
        (∀ v : H, A₁ v = ∫ c, (w₁ c) • (S c v) ∂μ) → (∀ v : H, A₂ v = ∫ c, (w₂ c) • (S c v) ∂μ) →
        (∀ v : H, A₁₂ v = ∫ c, (∫ d, w₁ d * w₂ (d⁻¹ * c) ∂μ) • (S c v) ∂μ) →
        A₁.comp A₂ = A₁₂) ∧
    (∀ A : H →L[ℂ] H, (∀ v : H, A v = ∫ c, S c v ∂μ) →
      (∀ v : H, A v = v ↔ ∀ c : C, S c v = v) ∧ A.comp A = A)
```

### `ContinuousLinearMap.eq_zero_of_forall_exists_mem_sub_real_smul_eq`

`Thm_ContinuousLinearMap_eq_zero_of_forall_exists_mem_sub_real_smul_eq` — Symmetry on a subspace forbids v∈(T-c)(E) for all real c

```lean
theorem ContinuousLinearMap.eq_zero_of_forall_exists_mem_sub_real_smul_eq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (E : Submodule ℂ H)
    (hsym : ∀ x ∈ E, ∀ y ∈ E, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ)
    (v : H) (hsurj : ∀ c : ℝ, ∃ w ∈ E, T w - (c : ℂ) • w = v) :
    v = 0
```

### `ContinuousLinearMap.exists_comp_torusEmb_eq_and_cylinder_noAtomicMass_of_box_noAtomicMass`

`Thm_ContinuousLinearMap_exists_comp_torusEmb_eq_and_cylinder_noAtomicMass_of_box_noAtomicMass` — Pushing a box-atomless functional from the torus to (ℂ×ℂ)ᵈ

```lean
theorem ContinuousLinearMap.exists_comp_torusEmb_eq_and_cylinder_noAtomicMass_of_box_noAtomicMass
    (d : ℕ) (XK : Set (Fin d → ℂ × ℂ))
    (emb : C((Fin d → AddCircle (1 : ℝ)), XK))
    (hemb : ∀ (θ : Fin d → AddCircle (1 : ℝ)) (i : Fin d),
      ((emb θ : XK) : Fin d → ℂ × ℂ) i = ((fourier 1 (θ i) : ℂ), (fourier (-1) (θ i) : ℂ)))
    (μ : C((Fin d → AddCircle (1 : ℝ)), ℂ) →L[ℂ] ℂ)
    (hμ : ∀ (τ : Fin d → AddCircle (1 : ℝ)), ∀ ε > (0 : ℝ),
        ∃ U : Fin d → Set (AddCircle (1 : ℝ)), (∀ i, IsOpen (U i) ∧ τ i ∈ U i) ∧
          ∀ g : C((Fin d → AddCircle (1 : ℝ)), ℂ),
            (∀ θ, (∃ i, θ i ∉ U i) → g θ = 0) → (∀ θ, ‖g θ‖ ≤ 1) → ‖μ g‖ < ε) :
    ∃ Λ : C(XK, ℂ) →L[ℂ] ℂ,
      (∀ h : C(XK, ℂ), Λ h = μ (h.comp emb)) ∧
      ∀ (τ : Fin d → ℂ × ℂ), ∀ ε > (0 : ℝ), ∃ U : Fin d → Set (ℂ × ℂ),
        (∀ v ∈ (Finset.univ : Finset (Fin d)), IsOpen (U v) ∧ τ v ∈ U v) ∧
        ∀ g : C(XK, ℂ), (∀ y : XK, (∃ v ∈ (Finset.univ : Finset (Fin d)), (y : Fin d → ℂ × ℂ) v ∉ U v) → g y = 0) →
          (∀ y, ‖g y‖ ≤ 1) → ‖Λ g‖ < ε
```

### `ContinuousLinearMap.exists_forall_apply_eq_integral_smul_apply_of_forall_norm_le_of_continuous`

`Thm_ContinuousLinearMap_exists_forall_apply_eq_integral_smul_apply_of_forall_norm_le_of_continuous` — Weighted Haar average of a bounded continuous representation

```lean
theorem ContinuousLinearMap.exists_forall_apply_eq_integral_smul_apply_of_forall_norm_le_of_continuous
    {C : Type*} [Group C] [TopologicalSpace C] [IsTopologicalGroup C] [CompactSpace C] [T2Space C]
    [MeasurableSpace C] [BorelSpace C] (μ : Measure C) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : C →* (H →L[ℂ] H)) (B : ℝ) (hSb : ∀ c : C, ‖S c‖ ≤ B) (hSc : ∀ v : H, Continuous fun c : C => S c v)
    (w : C → ℂ) (hw : Continuous w) :
    ∃ A : H →L[ℂ] H,
      (∀ v : H, A v = ∫ c, (w c) • (S c v) ∂μ) ∧
      (∀ M : ℝ, (∀ c : C, ‖w c‖ ≤ M) → ∀ v : H, ‖A v‖ ≤ M * B * ‖v‖) ∧
      (∀ L : Submodule ℂ H, IsClosed (L : Set H) →
        (∀ c : C, L.map (S c : H →ₗ[ℂ] H) ≤ L) → L.map (A : H →ₗ[ℂ] H) ≤ L) ∧
      (∀ T : H →L[ℂ] H, (∀ c : C, T.comp (S c) = (S c).comp T) → T.comp A = A.comp T)
```

### `ContinuousLinearMap.le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal`

`Thm_ContinuousLinearMap_le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal` — Dichotomy against high eigenspaces forces kernel or finite dimension

```lean
theorem ContinuousLinearMap.le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] {T : E →L[𝕜] E}
    (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) (X : Submodule 𝕜 E)
    (hX : ∀ r : ℝ, 0 < r → X ⊓ (⨆ (μ : 𝕜) (_ : r ≤ ‖μ‖), Module.End.eigenspace (T : Module.End 𝕜 E) μ)ᗮ = ⊥ ∨ X ≤ (⨆ (μ : 𝕜) (_ : r ≤ ‖μ‖), Module.End.eigenspace (T : Module.End 𝕜 E) μ)ᗮ) :
    X ≤ LinearMap.ker (T : E →ₗ[𝕜] E) ∨ FiniteDimensional 𝕜 ↥X
```

### `ContinuousLinearMap.map_eigenspace_orthogonal_le_of_commute`

`Thm_ContinuousLinearMap_map_eigenspace_orthogonal_le_of_commute` — Commuting operators preserve eigenspaces of a symmetric operator

```lean
theorem ContinuousLinearMap.map_eigenspace_orthogonal_le_of_commute {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {T : E →L[𝕜] E} (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric)
    (S : E →L[𝕜] E) (hST : S.comp T = T.comp S) (μ : 𝕜) (hμ : μ ≠ 0) :
    (eigenspace (T : Module.End 𝕜 E) μ).map (S : Module.End 𝕜 E) ≤ eigenspace (T : Module.End 𝕜 E) μ ∧
    ((eigenspace (T : Module.End 𝕜 E) μ)ᗮ).map (S : Module.End 𝕜 E) ≤ (eigenspace (T : Module.End 𝕜 E) μ)ᗮ
```

### `ContinuousLinearMap.map_highPart_orthogonal_le_of_commute`

`Thm_ContinuousLinearMap_map_highPart_orthogonal_le_of_commute` — Commuting operators preserve the orthocomplement of the high eigen-part

```lean
theorem ContinuousLinearMap.map_highPart_orthogonal_le_of_commute {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] {T S : E →L[𝕜] E}
    (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) (hST : S.comp T = T.comp S) (r : ℝ) :
    Submodule.map (S : E →ₗ[𝕜] E) (⨆ (μ : 𝕜) (_ : r ≤ ‖μ‖), Module.End.eigenspace (T : Module.End 𝕜 E) μ)ᗮ ≤ (⨆ (μ : 𝕜) (_ : r ≤ ‖μ‖), Module.End.eigenspace (T : Module.End 𝕜 E) μ)ᗮ
```

### `ContinuousLinearMap.noAtomicMass_comp_of_finite_fibres`

`Thm_ContinuousLinearMap_noAtomicMass_comp_of_finite_fibres` — Atom-free functionals pull back along coordinatewise finite-fibre maps

```lean
theorem ContinuousLinearMap.noAtomicMass_comp_of_finite_fibres
    {ιK ιL : Type} (XK : Set (ιK → ℂ × ℂ)) (hXKc : IsCompact XK) (X : Set (ιL → ℂ × ℂ)) (T : Finset ιK)
    (w' : ιK → ιL)
    (B : ιK → ℂ × ℂ → ℂ × ℂ) (hBc : ∀ v ∈ T, Continuous (B v))
    (hBf : ∀ v ∈ T, ∀ c : ℂ × ℂ, ((B v) ⁻¹' {c}).Finite)
    (bc : C(XK, X))
    (hbc : ∀ (x : XK), ∀ v ∈ T, ((bc x : X) : ιL → ℂ × ℂ) (w' v) = B v ((x : ιK → ℂ × ℂ) v))
    (Λ : C(XK, ℂ) →L[ℂ] ℂ)
    (hΛ : ∀ (τ : ιK → ℂ × ℂ), ∀ ε > (0 : ℝ), ∃ U : ιK → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
      ∀ g : C(XK, ℂ), (∀ y : XK, (∃ v ∈ T, (y : ιK → ℂ × ℂ) v ∉ U v) → g y = 0) → (∀ y, ‖g y‖ ≤ 1) →
        ‖Λ g‖ < ε) :
    ∀ (τ : ιK → ℂ × ℂ), ∀ ε > (0 : ℝ), ∃ U : ιK → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
      ∀ g : C(X, ℂ), (∀ y : X, (∃ v ∈ T, (y : ιL → ℂ × ℂ) (w' v) ∉ U v) → g y = 0) → (∀ y, ‖g y‖ ≤ 1) →
        ‖Λ (g.comp bc)‖ < ε
```

### `ContinuousLinearMap.orthogonal_iSup_eigenspace_ne_zero_eq_ker`

`Thm_ContinuousLinearMap_orthogonal_iSup_eigenspace_ne_zero_eq_ker` — Orthogonal complement of the non-zero eigenspaces is ker T

```lean
theorem ContinuousLinearMap.orthogonal_iSup_eigenspace_ne_zero_eq_ker {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] {T : E →L[𝕜] E}
    (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) :
    (⨆ (μ : 𝕜) (_ : μ ≠ 0), eigenspace (T : Module.End 𝕜 E) μ)ᗮ = LinearMap.ker (T : E →ₗ[𝕜] E)
```

## MonoidHom (10)

### `MonoidHom.apply_eq_one_of_sub_one_mem_maximalIdeal_of_pow_eq_one`

`Thm_MonoidHom_apply_eq_one_of_sub_one_mem_maximalIdeal_of_pow_eq_one` — Characters trivial mod 𝔪 vanish on invertible-order elements

```lean
theorem MonoidHom.apply_eq_one_of_sub_one_mem_maximalIdeal_of_pow_eq_one {G : Type u} {A : Type w} [Group G] [CommRing A] [IsLocalRing A]
    (χ : G →* Aˣ) (g : G) (hprin : (χ g : A) - 1 ∈ IsLocalRing.maximalIdeal A)
    {n : ℕ} (hn : IsUnit (n : A)) (hgn : g ^ n = 1) : χ g = 1
```

### `MonoidHom.charpoly_apply_mul_mul_inv`

`Thm_MonoidHom_charpoly_apply_mul_mul_inv` — Conjugation invariance of characteristic polynomials of a representation

```lean
theorem MonoidHom.charpoly_apply_mul_mul_inv {R : Type*} {M : Type*} {G : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] [Group G] (ρ : G →* Module.End R M) (σ τ : G) : (ρ (τ * σ * τ⁻¹)).charpoly = (ρ σ).charpoly
```

### `MonoidHom.exists_eq_comp_of_forall_val_sub_one_mem_maximalIdeal_of_coprime_card_ker`

`Thm_MonoidHom_exists_eq_comp_of_forall_val_sub_one_mem_maximalIdeal_of_coprime_card_ker` — Residually trivial character descends along a p'-order kernel

```lean
theorem MonoidHom.exists_eq_comp_of_forall_val_sub_one_mem_maximalIdeal_of_coprime_card_ker {G : Type u} {Δ : Type v} {R : Type w} [Group G] [Finite G] [Group Δ] [CommRing R] [IsLocalRing R]
    (π : G →* Δ) (hπ : Function.Surjective π) {p : ℕ} (hp : (p : R) ∈ IsLocalRing.maximalIdeal R)
    (hcop : (Nat.card π.ker).Coprime p)
    (ξ : G →* Rˣ) (hξ : ∀ g, (ξ g : R) - 1 ∈ IsLocalRing.maximalIdeal R) :
    ∃ χ : Δ →* Rˣ, ∀ g, ξ g = χ (π g)
```

### `MonoidHom.exists_finrank_two_trace_eq_add_det_eq_mul_of_mem_range`

`Thm_MonoidHom_exists_finrank_two_trace_eq_add_det_eq_mul_of_mem_range` — Descent of a sum of two characters to two dimensions

```lean
theorem MonoidHom.exists_finrank_two_trace_eq_add_det_eq_mul_of_mem_range
    {G : Type*} [Group G] {k Ω : Type} [Field k] [Finite k] [Field Ω]
    (ι : k →+* Ω) (χ₁ χ₂ : G →* Ωˣ)
    (hadd : ∀ g, (χ₁ g : Ω) + χ₂ g ∈ ι.range) (hmul : ∀ g, (χ₁ g : Ω) * χ₂ g ∈ ι.range) :
    ∃ (V₀ : Type) (_ : AddCommGroup V₀) (_ : Module k V₀) (ρ₀ : G →* (V₀ ≃ₗ[k] V₀)),
      Module.finrank k V₀ = 2 ∧
      (∀ g, χ₁ g = 1 → χ₂ g = 1 → ρ₀ g = 1) ∧
      (∀ g, ι (LinearMap.trace k V₀ (ρ₀ g).toLinearMap) = χ₁ g + χ₂ g) ∧
      (∀ g, ι (LinearMap.det (ρ₀ g).toLinearMap) = χ₁ g * χ₂ g)
```

### `MonoidHom.exists_mem_trace_sq_ne_four_mul_det_of_isCyclic_quotient`

`Thm_MonoidHom_exists_mem_trace_sq_ne_four_mul_det_of_isCyclic_quotient` — Absolutely irreducible 2-dimensional ρ is regular semisimple on N

```lean
theorem MonoidHom.exists_mem_trace_sq_ne_four_mul_det_of_isCyclic_quotient
    {G : Type*} [Group G] {𝕜 : Type*} [Field 𝕜] (h2 : (2 : 𝕜) ≠ 0)
    (ρ : G →* Matrix (Fin 2) (Fin 2) 𝕜)
    (hρ : Submodule.span 𝕜 (Set.range ρ) = ⊤)
    (N : Subgroup G) [N.Normal] [IsCyclic (G ⧸ N)] :
    ∃ σ ∈ N, (ρ σ).trace ^ 2 ≠ 4 * (ρ σ).det
```

### `MonoidHom.exists_subfield_units_coe_eq`

`Thm_MonoidHom_exists_subfield_units_coe_eq` — Co-restricting a bimultiplicative pairing to a subfield

```lean
theorem MonoidHom.exists_subfield_units_coe_eq
    {G : Type*} [Group G] {L : Type*} [Field L] (K : Subfield L)
    (F : G →* G →* Lˣ) (hF : ∀ α β : G, ((F α β : Lˣ) : L) ∈ K) :
    ∃ F' : G →* G →* (↥K)ˣ, ∀ α β : G, (((F' α β : (↥K)ˣ) : ↥K) : L) = F α β
```

### `MonoidHom.forall_eq_one_imp_eq_zero_and_exists_ne_zero_forall_mem_apply_eq_one`

`Thm_MonoidHom_forall_eq_one_imp_eq_zero_and_exists_ne_zero_forall_mem_apply_eq_one` — Characters separate points; proper character subgroups have non-trivial annihilator

```lean
theorem MonoidHom.forall_eq_one_imp_eq_zero_and_exists_ne_zero_forall_mem_apply_eq_one
    (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M] [Finite M] (hM : ∀ m : M, p • m = 0)
    (L : Type) [Field L] [IsAlgClosed L] [CharZero L] :
    (∀ m : M, (∀ χ : Multiplicative M →* Lˣ, χ (Multiplicative.ofAdd m) = 1) → m = 0) ∧
    (∀ K : Subgroup (Multiplicative M →* Lˣ), K ≠ ⊤ →
      ∃ m : M, m ≠ 0 ∧ ∀ χ ∈ K, χ (Multiplicative.ofAdd m) = 1)
```

### `MonoidHom.index_range_powMonoidHom_eq_mul_of_exact`

`Thm_MonoidHom_index_range_powMonoidHom_eq_mul_of_exact` — Multiplicativity of the n-th power index in an exact sequence

```lean
theorem MonoidHom.index_range_powMonoidHom_eq_mul_of_exact {G U F : Type*} [CommGroup G] [CommGroup U]
    [CommGroup F] (ι : U →* G) (φ : G →* F) (hι : Function.Injective ι) (hφ : Function.Surjective φ)
    (hexact : ι.range = φ.ker) {n : ℕ} (hF : ∀ x : F, x ^ n = 1 → x = 1) :
    (powMonoidHom n : G →* G).range.index
      = (powMonoidHom n : F →* F).range.index * (powMonoidHom n : U →* U).range.index
```

### `MonoidHom.isOpen_ker_of_cycloCharSpec`

`Thm_MonoidHom_isOpen_ker_of_cycloCharSpec` — Mod m cyclotomic character has open kernel

```lean
theorem MonoidHom.isOpen_ker_of_cycloCharSpec (m : ℕ) [NeZero m]
    (cyc : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod m)ˣ)
    (hcyc : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ),
      μ ^ m = 1 → σ μ = μ ^ ((cyc σ : ZMod m)).val) :
    IsOpen ((cyc.ker : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
      Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
```

### `MonoidHom.map_transfer_eq_transfer_comp`

`Thm_MonoidHom_map_transfer_eq_transfer_comp` — Transfer is natural in the coefficient group

```lean
theorem MonoidHom.map_transfer_eq_transfer_comp
    {G : Type*} [Group G] {H : Subgroup G} [H.FiniteIndex]
    {A B : Type*} [CommGroup A] [CommGroup B] (ϕ : ↥H →* A) (f : A →* B) (g : G) :
    f (MonoidHom.transfer ϕ g) = MonoidHom.transfer (f.comp ϕ) g
```

## Algebra (8)

### `Algebra.Etale.exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq`

`Thm_Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq` — Finite étale algebras of constant rank split after finite étale base change

```lean
theorem Algebra.Etale.exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq
    (R : Type u) [CommRing R] (B : Type u) [CommRing B] [Algebra R B]
    [Module.Finite R B] [Algebra.Etale R B]
    (n : ℕ) (hn : ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) B p = n) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Module.Finite R R')
      (_ : Algebra.Etale R R') (_ : Module.FaithfullyFlat R R'),
      Nonempty ((R' ⊗[R] B) ≃ₐ[R'] (Fin n → R'))
```

### `Algebra.FiniteType.exists_isMaximal_natCast_mem_of_ne_of_charZero`

`Thm_Algebra_FiniteType_exists_isMaximal_natCast_mem_of_ne_of_charZero` — Two residue characteristics for a finitely generated ℤ-algebra domain

```lean
theorem Algebra.FiniteType.exists_isMaximal_natCast_mem_of_ne_of_charZero
    (A : Type) [CommRing A] [IsDomain A] [CharZero A] [Algebra.FiniteType ℤ A] :
    ∃ (p₁ p₂ : ℕ) (𝔪₁ 𝔪₂ : Ideal A), p₁.Prime ∧ p₂.Prime ∧ p₁ ≠ p₂ ∧ 𝔪₁.IsMaximal ∧ 𝔪₂.IsMaximal ∧
      (p₁ : A) ∈ 𝔪₁ ∧ (p₂ : A) ∈ 𝔪₂
```

### `Algebra.FiniteType.finite_quotient_and_exists_charP_of_isMaximal_int`

`Thm_Algebra_FiniteType_finite_quotient_and_exists_charP_of_isMaximal_int` — Finite residue fields at maximal ideals of finite-type ℤ-algebras

```lean
theorem Algebra.FiniteType.finite_quotient_and_exists_charP_of_isMaximal_int
    (A : Type) [CommRing A] [Algebra.FiniteType ℤ A] (𝔮 : Ideal A) [𝔮.IsMaximal] :
    Finite (A ⧸ 𝔮) ∧ ∃ ℓ : ℕ, ℓ.Prime ∧ CharP (A ⧸ 𝔮) ℓ
```

### `Algebra.FormallyUnramified.nonempty_ringHom_int`

`Thm_Algebra_FormallyUnramified_nonempty_ringHom_int` — A nonzero finite flat unramified ℤ-algebra has a ℤ-point

```lean
theorem Algebra.FormallyUnramified.nonempty_ringHom_int
    (B : Type*) [CommRing B] [Nontrivial B] [Module.Finite ℤ B] [Module.Flat ℤ B]
    [Algebra.FormallyUnramified ℤ B] : Nonempty (B →+* ℤ)
```

### `Algebra.TensorProduct.isField_of_isSeparable_of_forall_isSeparable_mem_range`

`Thm_Algebra_TensorProduct_isField_of_isSeparable_of_forall_isSeparable_mem_range` — Primary extensions are linearly disjoint from separable ones

```lean
theorem Algebra.TensorProduct.isField_of_isSeparable_of_forall_isSeparable_mem_range
    (k : Type u) (F : Type v) (K : Type w) [Field k] [Field F] [Field K] [Algebra k F]
    [Algebra k K] [Algebra.IsSeparable k K]
    (hsc : ∀ y : F, IsSeparable k y → y ∈ (algebraMap k F).range) :
    IsField (F ⊗[k] K)
```

### `Algebra.TensorProduct.nilradical_isPrime_of_isAlgebraic_of_forall_isSeparable_mem_range`

`Thm_Algebra_TensorProduct_nilradical_isPrime_of_isAlgebraic_of_forall_isSeparable_mem_range` — Primary extensions: L ⊗_K Ω has prime nilradical

```lean
theorem Algebra.TensorProduct.nilradical_isPrime_of_isAlgebraic_of_forall_isSeparable_mem_range
    (K : Type u) (L : Type v) (Ω : Type w) [Field K] [Field L] [Field Ω] [Algebra K L]
    [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (hsc : ∀ y : L, IsSeparable K y → y ∈ (algebraMap K L).range) :
    (nilradical (L ⊗[K] Ω)).IsPrime
```

### `Algebra.bijective_tensorProduct_equalizer_of_faithfullyFlat_of_descentDatum`

`Thm_Algebra_bijective_tensorProduct_equalizer_of_faithfullyFlat_of_descentDatum` — Effective faithfully flat descent for commutative algebras

```lean
theorem Algebra.bijective_tensorProduct_equalizer_of_faithfullyFlat_of_descentDatum
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    (A' : Type u) [CommRing A'] [Algebra S A'] [Algebra S' A'] [IsScalarTower S S' A']
    (φ : A' ⊗[S] S' ≃ₐ[S] S' ⊗[S] A')

    (hφlin : φ.toAlgHom.comp (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S S' A') (AlgHom.id S S')) =
      Algebra.TensorProduct.map (AlgHom.id S S') (IsScalarTower.toAlgHom S S' A'))

    (hφcoc : (Algebra.TensorProduct.map (AlgHom.id S S') φ.toAlgHom).comp
        ((Algebra.TensorProduct.assoc S S S S' A' S').toAlgHom.comp
          (Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id S S'))) =
      (Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.comm S A' S').toAlgHom).comp
        ((Algebra.TensorProduct.assoc S S S S' A' S').toAlgHom.comp
          ((Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id S S')).comp
            ((Algebra.TensorProduct.assoc S S S A' S' S').symm.toAlgHom.comp
              ((Algebra.TensorProduct.map (AlgHom.id S A') (Algebra.TensorProduct.comm S S' S').toAlgHom).comp
                (Algebra.TensorProduct.assoc S S S A' S' S').toAlgHom)))))
    :
    let A : Subalgebra S A' :=
      AlgHom.equalizer (φ.toAlgHom.comp (Algebra.TensorProduct.includeLeft : A' →ₐ[S] A' ⊗[S] S'))
        (Algebra.TensorProduct.includeRight : A' →ₐ[S] S' ⊗[S] A')
    Function.Bijective (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom S S' A') A.val (fun s a => Commute.all _ _))
```

### `Algebra.exists_mvPolynomial_forall_eval_eq_norm_det_sum_smul`

`Thm_Algebra_exists_mvPolynomial_forall_eval_eq_norm_det_sum_smul` — Norm of a determinant is polynomial in the coefficients

```lean
theorem Algebra.exists_mvPolynomial_forall_eval_eq_norm_det_sum_smul
    (E : Type) [CommRing E] [Algebra ℝ E] [Module.Free ℝ E] [Module.Finite ℝ E]
    (m : Type) [Fintype m] [DecidableEq m]
    (n : ℕ) (e : Fin n → Matrix m m E) :
    ∃ P : MvPolynomial (Fin n) ℝ, ∀ c : Fin n → ℝ,
      MvPolynomial.eval c P = Algebra.norm ℝ (Matrix.det (∑ a, c a • e a))
```

## TensorProduct (8)

### `TensorProduct.AlgebraTensorModule.cancelBaseChange_baseChange_baseChange_apply`

`Thm_TensorProduct_AlgebraTensorModule_cancelBaseChange_baseChange_baseChange_apply` — Cancellation of iterated base change is natural in endomorphisms

```lean
theorem TensorProduct.AlgebraTensorModule.cancelBaseChange_baseChange_baseChange_apply
    (q : ℕ) [Fact q.Prime] (Λ : Type) [AddCommGroup Λ] (f : Λ →ₗ[ℤ] Λ)
    (x : ℚ_[q] ⊗[ℤ_[q]] (ℤ_[q] ⊗[ℤ] Λ)) :
    cancelBaseChange ℤ ℤ_[q] ℚ_[q] ℚ_[q] Λ (((f.baseChange ℤ_[q]).baseChange ℚ_[q]) x) =
      (f.baseChange ℚ_[q]) (cancelBaseChange ℤ ℤ_[q] ℚ_[q] ℚ_[q] Λ x)
```

### `TensorProduct.eq_zero_of_forall_lTensor_eq_zero_of_field`

`Thm_TensorProduct_eq_zero_of_forall_lTensor_eq_zero_of_field` — Dévissage: field case implies finitely generated case

```lean
theorem TensorProduct.eq_zero_of_forall_lTensor_eq_zero_of_field
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {B : Type v} [AddCommGroup B] [Module A B] [Module.Flat A B]
    {J : Type w} {N : J → Type v} [∀ j, AddCommGroup (N j)] [∀ j, Module A (N j)]
    [∀ j, Module.Flat A (N j)] (f : ∀ j, B →ₗ[A] N j)
    (hK : ∀ (K : Type u) [Field K] [Algebra A K] (g : K ⊗[A] B),
      (∀ j, LinearMap.lTensor K (f j) g = 0) → g = 0)
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (g : M ⊗[A] B) (hg : ∀ j, LinearMap.lTensor M (f j) g = 0) : g = 0
```

### `TensorProduct.exists_addEquiv_baseChange_tensor_baseChange_tmul_eq_of_bijective`

`Thm_TensorProduct_exists_addEquiv_baseChange_tensor_baseChange_tmul_eq_of_bijective` — Base change along C = A ⊗_k B identifies P ⊗_k Q

```lean
theorem TensorProduct.exists_addEquiv_baseChange_tensor_baseChange_tmul_eq_of_bijective
    {k A B C : Type u} [CommRing k] [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C] [Algebra A C] [Algebra B C]
    [IsScalarTower k A C] [IsScalarTower k B C]
    (Φ : A ⊗[k] B ≃ₗ[k] C) (hΦ : ∀ (a : A) (b : B), Φ (a ⊗ₜ b) = algebraMap A C a * algebraMap B C b)
    (P : Type u) [AddCommGroup P] [Module A P] [Module k P] [IsScalarTower k A P]
    (Q : Type u) [AddCommGroup Q] [Module B Q] [Module k Q] [IsScalarTower k B Q] :
    ∃ g : (C ⊗[A] P) ⊗[C] (C ⊗[B] Q) ≃+ P ⊗[k] Q,
      ∀ (p : P) (q : Q), g (((1 : C) ⊗ₜ[A] p) ⊗ₜ[C] ((1 : C) ⊗ₜ[B] q)) = p ⊗ₜ[k] q
```

### `TensorProduct.exists_linearEquiv_compHom_ringEquiv_tmul`

`Thm_TensorProduct_exists_linearEquiv_compHom_ringEquiv_tmul` — Transporting a tensor product along a field isomorphism

```lean
theorem TensorProduct.exists_linearEquiv_compHom_ringEquiv_tmul
    {k κ : Type} [Field k] [Field κ] (e : k ≃+* κ)
    (V : Type) [AddCommGroup V] [Module k V] (H : Type) [AddCommGroup H] [Module κ H] :
    letI : Module κ V := Module.compHom V (e.symm : κ ≃+* k).toRingHom
    letI : Module k H := Module.compHom H e.toRingHom
    letI : Module k (V ⊗[κ] H) := Module.compHom (V ⊗[κ] H) e.toRingHom
    (Module.Finite k H ↔ Module.Finite κ H) ∧
    Module.finrank k H = Module.finrank κ H ∧
    ∃ Θ : (V ⊗[k] H) ≃ₗ[k] (V ⊗[κ] H),
      (∀ (v : V) (h : H), Θ (v ⊗ₜ[k] h) = v ⊗ₜ[κ] h) ∧
      (∀ (f : V →ₗ[k] V) (f' : V →ₗ[κ] V) (_ : ∀ v, f' v = f v) (g : H →ₗ[κ] H) (g' : H →ₗ[k] H) (_ : ∀ h, g' h = g h)
          (x : V ⊗[k] H),
        Θ (TensorProduct.map f g' x) = TensorProduct.map f' g (Θ x))
```

### `TensorProduct.exists_linearEquiv_span_range_apply_tmul_of_natCard_eq_pow_finrank`

`Thm_TensorProduct_exists_linearEquiv_span_range_apply_tmul_of_natCard_eq_pow_finrank` — Base change isomorphism onto the K-span of an 𝔽ₚ-linear map

```lean
theorem TensorProduct.exists_linearEquiv_span_range_apply_tmul_of_natCard_eq_pow_finrank
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (K : Type*) [Field K] [Algebra (ZMod p) K]
    {W : Type*} [AddCommGroup W] [Module K W] [Module (ZMod p) W] [IsScalarTower (ZMod p) K W]
    (Θ : V →ₗ[ZMod p] W)
    (hcard : Nat.card V = p ^ Module.finrank K (Submodule.span K (Set.range Θ))) :
    ∃ e : K ⊗[ZMod p] V ≃ₗ[K] Submodule.span K (Set.range Θ),
      ∀ (c : K) (v : V), (e (c ⊗ₜ[ZMod p] v) : W) = c • Θ v
```

### `TensorProduct.exists_pow_smul_eq_one_tmul`

`Thm_TensorProduct_exists_pow_smul_eq_one_tmul` — Clearing denominators in ℚ_q ⊗_{ℤ_q} T

```lean
theorem TensorProduct.exists_pow_smul_eq_one_tmul (q : ℕ) [Fact q.Prime]
    (T : Type) [AddCommGroup T] [Module ℤ_[q] T] (w : ℚ_[q] ⊗[ℤ_[q]] T) :
    ∃ (k : ℕ) (t : T), ((q : ℚ_[q]) ^ k) • w = (1 : ℚ_[q]) ⊗ₜ[ℤ_[q]] t
```

### `TensorProduct.mem_span_unitTmul_of_forall_apply_eq_zero`

`Thm_TensorProduct_mem_span_unitTmul_of_forall_apply_eq_zero` — Joint zeros in a double base change lie in the span of unit tensors

```lean
theorem TensorProduct.mem_span_unitTmul_of_forall_apply_eq_zero
    {R S K T : Type}
    [CommRing R]
    [CommRing S] [Algebra R S]
    [Field K] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
    [AddCommGroup T] [Module R T] [NoZeroSMulDivisors R T]
    (hinj : Function.Injective (algebraMap R K))
    {ι : Type} (Φ : ι → (K ⊗[S] (S ⊗[R] T)) →ₗ[K] (K ⊗[S] (S ⊗[R] T))) (g : ι → T → T)
    (hcomm : ∀ (i : ι) (k : K) (x : T),
      Φ i (k ⊗ₜ[S] ((1 : S) ⊗ₜ[R] x)) = k ⊗ₜ[S] ((1 : S) ⊗ₜ[R] g i x))
    (v : K ⊗[S] (S ⊗[R] T)) (hv : ∀ i, Φ i v = 0) :
    v ∈ Submodule.span K
      {z : K ⊗[S] (S ⊗[R] T) | ∃ y : T, (∀ i, g i y = 0) ∧
        z = (1 : K) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] y)}
```

### `TensorProduct.mulMap_injOn_and_surjOn_diagonal_of_isSeparable`

`Thm_TensorProduct_mulMap_injOn_and_surjOn_diagonal_of_isSeparable` — Multiplication is bijective on the diagonal of K ⊗_F P

```lean
theorem TensorProduct.mulMap_injOn_and_surjOn_diagonal_of_isSeparable
    {F K P : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Algebra.IsSeparable F K]
    [AddCommGroup P] [Module K P] [Module F P] [IsScalarTower F K P]
    (π : K ⊗[F] P →ₗ[K] P) (hπ : ∀ (a : K) (v : P), π (a ⊗ₜ[F] v) = a • v) :
    (∀ w : K ⊗[F] P,
        (∀ k : K, k • w = LinearMap.baseChange K ((LinearMap.lsmul K P k).restrictScalars F) w) →
          π w = 0 → w = 0) ∧
      ∀ v : P, ∃ w : K ⊗[F] P,
        (∀ k : K, k • w = LinearMap.baseChange K ((LinearMap.lsmul K P k).restrictScalars F) w) ∧ π w = v
```

## TwoChartCech (8)

### `TwoChartCech.Mumford.bijective_kerMapBaseChange`

`Thm_TwoChartCech_Mumford_bijective_kerMapBaseChange` — Mumford truncation computes ker(d⊗ A) after any base change

```lean
theorem TwoChartCech.Mumford.bijective_kerMapBaseChange
    {R : Type u} [CommRing R]
    {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1] [Module.Flat R C1]
    (d : C0 →ₗ[R] C1) [Module.Finite R (C1 ⧸ LinearMap.range d)]
    (A : Type u) [CommRing A] [Algebra R A] :
    Function.Bijective
      (TwoChartCech.kerMapBaseChange (TwoChartCech.Mumford.dK d) d (TwoChartCech.Mumford.ι0 d)
        (TwoChartCech.Mumford.ι1 d) (TwoChartCech.Mumford.comm d) A)
```

### `TwoChartCech.Mumford.finite_K0`

`Thm_TwoChartCech_Mumford_finite_K0` — Finite generation of Mumford's degree-zero truncation term K⁰

```lean
theorem TwoChartCech.Mumford.finite_K0
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {C0 : Type v} {C1 : Type w} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    (d : C0 →ₗ[R] C1) [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)] :
    Module.Finite R (TwoChartCech.Mumford.K0 d)
```

### `TwoChartCech.Mumford.flat_K0`

`Thm_TwoChartCech_Mumford_flat_K0` — Flatness of the Mumford truncation term K⁰

```lean
theorem TwoChartCech.Mumford.flat_K0
    {R : Type u} [CommRing R]
    {C0 : Type v} {C1 : Type w} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C0] [Module.Flat R C1]
    (d : C0 →ₗ[R] C1) [Module.Finite R (C1 ⧸ LinearMap.range d)] :
    Module.Flat R (TwoChartCech.Mumford.K0 d)
```

### `TwoChartCech.exists_fibreH0Family`

`Thm_TwoChartCech_exists_fibreH0Family` — Existence of the h⁰-family of a flat two-term complex

```lean
theorem TwoChartCech.exists_fibreH0Family
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C0] [Module.Flat R C1] (d : C0 →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)]
    {T : Scheme.{u}} (f : T ⟶ Spec (.of R)) :
    ∃ F : CoherentBaseChange.FibreH0Family T,
      ∀ x : T, F.h0 x = Module.finrank (f.base x).asIdeal.ResidueField
        (LinearMap.ker (d.baseChange (f.base x).asIdeal.ResidueField))
```

### `TwoChartCech.exists_twoTermComplex_kerMapBaseChange_bijective`

`Thm_TwoChartCech_exists_twoTermComplex_kerMapBaseChange_bijective` — A finite free two-term model for ker d after every base change

```lean
theorem TwoChartCech.exists_twoTermComplex_kerMapBaseChange_bijective
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C0] [Module.Flat R C1] (d : C0 →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)] :
    ∃ (G : CoherentBaseChange.TwoTermComplex.{u, u} R) (ι0 : G.C0 →ₗ[R] C0) (ι1 : G.C1 →ₗ[R] C1)
      (comm : d ∘ₗ ι0 = ι1 ∘ₗ G.d),
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Bijective (TwoChartCech.kerMapBaseChange G.d d ι0 ι1 comm A)
```

### `TwoChartCech.finrank_ker_baseChange_eq_of_field_extension`

`Thm_TwoChartCech_finrank_ker_baseChange_eq_of_field_extension` — Invariance of dimker(d⊗ K) under field extension

```lean
theorem TwoChartCech.finrank_ker_baseChange_eq_of_field_extension
    {R : Type u} [CommRing R] {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    (d : C0 →ₗ[R] C1) (K L : Type u) [Field K] [Field L] [Algebra R K] [Algebra R L] [Algebra K L]
    [IsScalarTower R K L] :
    Module.finrank K (LinearMap.ker (d.baseChange K)) = Module.finrank L (LinearMap.ker (d.baseChange L))
```

### `TwoChartCech.isClosed_setOf_le_finrank_ker_baseChange`

`Thm_TwoChartCech_isClosed_setOf_le_finrank_ker_baseChange` — Upper semicontinuity of ker dimension for a two-term complex

```lean
theorem TwoChartCech.isClosed_setOf_le_finrank_ker_baseChange
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C0] [Module.Flat R C1] (d : C0 →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)]
    {T : Scheme.{u}} (f : T ⟶ Spec (.of R)) (n : ℕ) :
    IsClosed {x : T | n ≤ Module.finrank (f.base x).asIdeal.ResidueField
      (LinearMap.ker (d.baseChange (f.base x).asIdeal.ResidueField))}
```

### `TwoChartCech.nonempty_kerBaseChangeTowerEquiv`

`Thm_TwoChartCech_nonempty_kerBaseChangeTowerEquiv` — Transitivity of base change on kernels of a linear map

```lean
theorem TwoChartCech.nonempty_kerBaseChangeTowerEquiv
    {R : Type u} [CommRing R] {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    (d : C0 →ₗ[R] C1) (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] :
    ∃ e : LinearMap.ker ((d.baseChange S).baseChange T) ≃ₗ[T] LinearMap.ker (d.baseChange T),
      ∀ z, (e z : T ⊗[R] C0) = TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T C0 z
```

## IsLocalRing (7)

### `IsLocalRing.eq_one_of_pow_eq_one_of_sub_one_mem_maximalIdeal`

`Thm_IsLocalRing_eq_one_of_pow_eq_one_of_sub_one_mem_maximalIdeal` — Principal units have no n-torsion when n is invertible

```lean
theorem IsLocalRing.eq_one_of_pow_eq_one_of_sub_one_mem_maximalIdeal {A : Type u} [CommRing A] [IsLocalRing A]
    {u : A} (hu : u - 1 ∈ IsLocalRing.maximalIdeal A) {n : ℕ} (hn : IsUnit (n : A)) (hun : u ^ n = 1) : u = 1
```

### `IsLocalRing.exists_isNoetherianRing_faithfullyFlat_map_maximalIdeal_eq_residueField_algEquiv_of_isAlgebraic`

`Thm_IsLocalRing_exists_isNoetherianRing_faithfullyFlat_map_maximalIdeal_eq_residueField_algEquiv_of_isAlgebraic` — Flat local extension realising a prescribed algebraic residue extension

```lean
theorem IsLocalRing.exists_isNoetherianRing_faithfullyFlat_map_maximalIdeal_eq_residueField_algEquiv_of_isAlgebraic
    (T : Type u) [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    (K : Type u) [Field K] [Algebra (ResidueField T) K] [Algebra.IsAlgebraic (ResidueField T) K] :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsLocalRing B) (_ : IsNoetherianRing B) (_ : Algebra T B)
      (_ : IsLocalHom (algebraMap T B)),
      Module.FaithfullyFlat T B ∧
        Ideal.map (algebraMap T B) (maximalIdeal T) = maximalIdeal B ∧
        Nonempty (ResidueField B ≃ₐ[ResidueField T] K)
```

### `IsLocalRing.exists_mem_maximalIdeal_notMem_sq_forall_minimalPrimes_notMem`

`Thm_IsLocalRing_exists_mem_maximalIdeal_notMem_sq_forall_minimalPrimes_notMem` — Element of 𝔪∖𝔪² avoiding all minimal primes

```lean
theorem IsLocalRing.exists_mem_maximalIdeal_notMem_sq_forall_minimalPrimes_notMem
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (hdim : 0 < ringKrullDim R) :
    ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 ∧ ∀ p ∈ minimalPrimes R, x ∉ p
```

### `IsLocalRing.flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map`

`Thm_IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map` — Fibrewise criterion of flatness for a tower of local rings

```lean
theorem IsLocalRing.flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map
    {R S S' : Type} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S S')]
    [IsNoetherianRing S] [IsNoetherianRing S'] :
    letI : Algebra (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))
        (S' ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S')) :=
      Ideal.Quotient.algebraQuotientOfLEComap (Ideal.map_le_iff_le_comap.mp (le_of_eq
        (by rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R S S'])))
    Module.Flat R S' →
    Module.Flat (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))
        (S' ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S')) →
    Module.Flat S S'
```

### `IsLocalRing.isRegular_of_systemOfParameters`

`Thm_IsLocalRing_isRegular_of_systemOfParameters` — Systems of parameters in Cohen–Macaulay local rings are regular

```lean
theorem IsLocalRing.isRegular_of_systemOfParameters
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hCM : (Module.depth R R : WithBot ℕ∞) = ringKrullDim R)
    {d : ℕ} (hdim : ringKrullDim R = d)
    (xs : List R) (hlen : xs.length = d) (hmem : ∀ y ∈ xs, y ∈ maximalIdeal R)
    (hsop : ringKrullDim (R ⧸ Ideal.ofList xs) = 0) :
    RingTheory.Sequence.IsRegular R xs
```

### `IsLocalRing.map_maximalIdeal_eq_maximalIdeal_localization_atPrime_of_isReduced_of_isArtinianRing`

`Thm_IsLocalRing_map_maximalIdeal_eq_maximalIdeal_localization_atPrime_of_isReduced_of_isArtinianRing` — Localising at n over a reduced Artinian fibre

```lean
theorem IsLocalRing.map_maximalIdeal_eq_maximalIdeal_localization_atPrime_of_isReduced_of_isArtinianRing
    {C C' : Type} [CommRing C] [IsLocalRing C] [CommRing C'] [Algebra C C']
    (𝔫 : Ideal C') [𝔫.IsMaximal]
    (hle : (maximalIdeal C).map (algebraMap C C') ≤ 𝔫)
    [IsReduced (C' ⧸ (maximalIdeal C).map (algebraMap C C'))]
    [IsArtinianRing (C' ⧸ (maximalIdeal C).map (algebraMap C C'))] :
    (maximalIdeal C).map (algebraMap C (Localization.AtPrime 𝔫)) = maximalIdeal (Localization.AtPrime 𝔫) ∧
    IsLocalHom (algebraMap C (Localization.AtPrime 𝔫)) ∧
    Function.Surjective ((residue (Localization.AtPrime 𝔫)).comp (algebraMap C' (Localization.AtPrime 𝔫))) ∧
    RingHom.ker ((residue (Localization.AtPrime 𝔫)).comp (algebraMap C' (Localization.AtPrime 𝔫))) = 𝔫
```

### `IsLocalRing.uniqueFactorizationMonoid_of_isPrincipalIdealRing_quotient`

`Thm_IsLocalRing_uniqueFactorizationMonoid_of_isPrincipalIdealRing_quotient` — Noetherian local domain with principal quotient is factorial

```lean
theorem IsLocalRing.uniqueFactorizationMonoid_of_isPrincipalIdealRing_quotient
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] (t : A)
    [IsDomain (A ⧸ Ideal.span {t})] [IsPrincipalIdealRing (A ⧸ Ideal.span {t})] :
    UniqueFactorizationMonoid A
```

## groupCohomology (7)

### `groupCohomology.IsGradedCupProduct.delta_cup`

`Thm_groupCohomology_IsGradedCupProduct_delta_cup` — Connecting map commutes with cup product in the first variable

```lean
theorem groupCohomology.IsGradedCupProduct.delta_cup {k G : Type u} [CommRing k] [Group G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (B : Rep.{u} k G)
    (hXB : (X.map (MonoidalCategory.tensorRight B)).ShortExact)
    (cup₁ : groupCohomology.GradedCupFamily X.X₁ B) (h₁ : groupCohomology.IsGradedCupProduct X.X₁ B cup₁)
    (cup₃ : groupCohomology.GradedCupFamily X.X₃ B) (h₃ : groupCohomology.IsGradedCupProduct X.X₃ B cup₃)
    (p q : ℕ) (x : groupCohomology X.X₃ p) (y : groupCohomology B q) :
    (groupCohomology.δ hXB (p + q) (p + 1 + q) (by omega)).hom (cup₃ p q x y)
      = cup₁ (p + 1) q ((groupCohomology.δ hX p (p + 1) rfl).hom x) y
```

### `groupCohomology.d_cochainCup_apply`

`Thm_groupCohomology_d_cochainCup_apply` — Leibniz rule for the cup product of inhomogeneous cochains

```lean
theorem groupCohomology.d_cochainCup_apply {k G : Type u} [CommRing k] [Group G] (A B : Rep.{u} k G) (p q : ℕ)
    (f : (Fin p → G) → A) (g : (Fin q → G) → B) (σ : Fin (p + q + 1) → G) :
    (inhomogeneousCochains.d (A ⊗ B) (p + q)).hom (groupCohomology.cochainCup A B p q f g) σ
      = groupCohomology.cochainCup A B (p + 1) q ((inhomogeneousCochains.d A p).hom f) g
          (fun i => σ (Fin.cast (Nat.add_right_comm p 1 q) i))
        + ((-1 : k) ^ p) • groupCohomology.cochainCup A B p (q + 1) f ((inhomogeneousCochains.d B q).hom g) σ
```

### `groupCohomology.exists_isGradedCupProduct`

`Thm_groupCohomology_exists_isGradedCupProduct` — Existence of a graded cup product on group cohomology

```lean
theorem groupCohomology.exists_isGradedCupProduct {k G : Type u} [CommRing k] [Group G] (A B : Rep.{u} k G) :
    ∃ cup : groupCohomology.GradedCupFamily A B, groupCohomology.IsGradedCupProduct A B cup
```

### `groupCohomology.finiteDimensional_H1_of_finite`

`Thm_groupCohomology_finiteDimensional_H1_of_finite` — Finite-dimensionality of H¹(G,A) for finite G

```lean
theorem groupCohomology.finiteDimensional_H1_of_finite {k : Type u} [Field k] {G : Type u} [Group G] [Finite G] (A : Rep k G) [FiniteDimensional k A] :
    FiniteDimensional k (H1 A)
```

### `groupCohomology.finiteDimensional_inflationImage`

`Thm_groupCohomology_finiteDimensional_inflationImage` — Finite-dimensionality of the inflation image in H¹

```lean
theorem groupCohomology.finiteDimensional_inflationImage {k : Type u} [Field k] {G : Type u} [Group G] (M : Rep k G) (S : Subgroup G) [S.Normal]
    [S.FiniteIndex] [FiniteDimensional k M] :
    FiniteDimensional k (inflationImage M S)
```

### `groupCohomology.inflationImage_antitone`

`Thm_groupCohomology_inflationImage_antitone` — Antitonicity of the inflation image in the subgroup

```lean
theorem groupCohomology.inflationImage_antitone {k : Type u} [CommRing k] {G : Type u} [Group G] (M : Rep k G) {S T : Subgroup G} [S.Normal] [T.Normal]
    (hST : S ≤ T) : inflationImage M T ≤ inflationImage M S
```

### `groupCohomology.map_inflationImage_le`

`Thm_groupCohomology_map_inflationImage_le` — Inflation images are carried into inflation images

```lean
theorem groupCohomology.map_inflationImage_le {k : Type u} [CommRing k] {G : Type u} [Group G] {Δ : Type u} [Group Δ] (f : Δ →* G) {M : Rep k G} {N : Rep k Δ}
    (φ : Rep.res f M ⟶ N) (T : Subgroup G) [T.Normal] (S : Subgroup Δ) [S.Normal]
    (hST : S ≤ T.comap f) :
    (inflationImage M T).map (groupCohomology.map f φ 1).hom ≤ inflationImage N S
```

## IsArtinianRing (6)

### `IsArtinianRing.exists_faithfullyFlat_isLocalHom_isAlgClosed_residueField_of_finite_residueField`

`Thm_IsArtinianRing_exists_faithfullyFlat_isLocalHom_isAlgClosed_residueField_of_finite_residueField` — Artin local covers with algebraically closed residue field

```lean
theorem IsArtinianRing.exists_faithfullyFlat_isLocalHom_isAlgClosed_residueField_of_finite_residueField
    (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [Finite (ResidueField C)] :
    ∃ (D : Type) (_ : CommRing D) (_ : IsLocalRing D) (_ : IsArtinianRing D) (_ : Algebra C D) (ℓ : ℕ) (_ : Fact ℓ.Prime),
      Module.FaithfullyFlat C D ∧ IsLocalHom (algebraMap C D) ∧
      Ideal.map (algebraMap C D) (maximalIdeal C) = maximalIdeal D ∧
      IsAlgClosed (ResidueField D) ∧ CharP (ResidueField D) ℓ
```

### `IsArtinianRing.exists_isArtinianRing_faithfullyFlat_map_maximalIdeal_eq_isAlgClosed_residueField`

`Thm_IsArtinianRing_exists_isArtinianRing_faithfullyFlat_map_maximalIdeal_eq_isAlgClosed_residueField` — Gonflement of an Artinian local ring

```lean
theorem IsArtinianRing.exists_isArtinianRing_faithfullyFlat_map_maximalIdeal_eq_isAlgClosed_residueField
    (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] :
    ∃ (D : Type) (_ : CommRing D) (_ : IsLocalRing D) (_ : IsArtinianRing D) (_ : Algebra C D),
      Module.FaithfullyFlat C D ∧ IsLocalHom (algebraMap C D) ∧
      Ideal.map (algebraMap C D) (maximalIdeal C) = maximalIdeal D ∧
      IsAlgClosed (ResidueField D)
```

### `IsArtinianRing.finite_of_isLocalRing_of_finite_residueField`

`Thm_IsArtinianRing_finite_of_isLocalRing_of_finite_residueField` — An Artinian local ring with finite residue field is finite

```lean
theorem IsArtinianRing.finite_of_isLocalRing_of_finite_residueField
    (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [Finite (ResidueField C)] : Finite C
```

### `IsArtinianRing.flat_and_finite_and_isNoetherianRing_tensorProduct_int_of_finite_residueField`

`Thm_IsArtinianRing_flat_and_finite_and_isNoetherianRing_tensorProduct_int_of_finite_residueField` — Base change of a finite Artin local ring along a flat ℤ-algebra

```lean
theorem IsArtinianRing.flat_and_finite_and_isNoetherianRing_tensorProduct_int_of_finite_residueField
    (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [Finite (ResidueField C)]
    (O : Type) [CommRing O] [IsNoetherianRing O] [Module.Flat ℤ O] :
    Module.Flat C (C ⊗[ℤ] O) ∧ (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] C ⊗[ℤ] O).toRingHom.Finite ∧
      IsNoetherianRing (C ⊗[ℤ] O) ∧
      IsNilpotent (Ideal.map (algebraMap C (C ⊗[ℤ] O)) (maximalIdeal C))
```

### `IsArtinianRing.isAlgClosed_residueField_of_isMaximal_tensorProduct_int_of_isAlgClosed_residueField`

`Thm_IsArtinianRing_isAlgClosed_residueField_of_isMaximal_tensorProduct_int_of_isAlgClosed_residueField` — Residue fields of C⊗_ℤO are algebraically closed of characteristic ℓ

```lean
theorem IsArtinianRing.isAlgClosed_residueField_of_isMaximal_tensorProduct_int_of_isAlgClosed_residueField
    (ℓ : ℕ) [Fact ℓ.Prime]
    (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [Finite (ResidueField C)] [CharP (ResidueField C) ℓ]
    (O : Type) [CommRing O] [IsLocalRing O] (hℓ : maximalIdeal O = Ideal.span {((ℓ : ℕ) : O)})
    (hac : IsAlgClosed (ResidueField O))
    (𝔫 : Ideal (C ⊗[ℤ] O)) [𝔫.IsMaximal] :
    IsAlgClosed 𝔫.ResidueField ∧ CharP 𝔫.ResidueField ℓ
```

### `IsArtinianRing.isReduced_and_isArtinianRing_tensorProduct_int_quotient_map_maximalIdeal`

`Thm_IsArtinianRing_isReduced_and_isArtinianRing_tensorProduct_int_quotient_map_maximalIdeal` — Reducedness of the fibre of C ⊗_ℤ O over mathfrak m_C

```lean
theorem IsArtinianRing.isReduced_and_isArtinianRing_tensorProduct_int_quotient_map_maximalIdeal
    (ℓ : ℕ) [Fact ℓ.Prime]
    (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [Finite (ResidueField C)] [CharP (ResidueField C) ℓ]
    (O : Type) [CommRing O] (hℓ : (Ideal.span {((ℓ : ℕ) : O)}).IsMaximal) :
    IsReduced ((C ⊗[ℤ] O) ⧸ Ideal.map (algebraMap C (C ⊗[ℤ] O)) (maximalIdeal C)) ∧
      IsArtinianRing ((C ⊗[ℤ] O) ⧸ Ideal.map (algebraMap C (C ⊗[ℤ] O)) (maximalIdeal C)) ∧
      Nontrivial ((C ⊗[ℤ] O) ⧸ Ideal.map (algebraMap C (C ⊗[ℤ] O)) (maximalIdeal C))
```

## IsRegularLocalRing (6)

### `IsRegularLocalRing.adjoinRoot_of_monic_of_coeff_mem_maximalIdeal_of_coeff_zero_not_mem_sq`

`Thm_IsRegularLocalRing_adjoinRoot_of_monic_of_coeff_mem_maximalIdeal_of_coeff_zero_not_mem_sq` — Regularity of S[X]/(g) for an Eisenstein polynomial g

```lean
theorem IsRegularLocalRing.adjoinRoot_of_monic_of_coeff_mem_maximalIdeal_of_coeff_zero_not_mem_sq
    (S : Type*) [CommRing S] [IsRegularLocalRing S]
    (g : S[X]) (hg : g.Monic) (hn : 1 ≤ g.natDegree)
    (hcoeff : ∀ i < g.natDegree, g.coeff i ∈ maximalIdeal S)
    (h0 : g.coeff 0 ∉ maximalIdeal S ^ 2) :
    IsRegularLocalRing (AdjoinRoot g) ∧ ringKrullDim (AdjoinRoot g) = ringKrullDim S
```

### `IsRegularLocalRing.depth_self_eq_ringKrullDim`

`Thm_IsRegularLocalRing_depth_self_eq_ringKrullDim` — Regular local rings are Cohen–Macaulay

```lean
theorem IsRegularLocalRing.depth_self_eq_ringKrullDim
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsRegularLocalRing R] :
    (Module.depth R R : WithBot ℕ∞) = ringKrullDim R
```

### `IsRegularLocalRing.isDomain`

`Thm_IsRegularLocalRing_isDomain` — A regular local ring is a domain

```lean
theorem IsRegularLocalRing.isDomain (R : Type*) [CommRing R] [IsRegularLocalRing R] :
    IsDomain R
```

### `IsRegularLocalRing.mvPowerSeries_fin`

`Thm_IsRegularLocalRing_mvPowerSeries_fin` — 𝒪[[X₁,…,Xₙ]] over a discrete valuation ring is regular local

```lean
theorem IsRegularLocalRing.mvPowerSeries_fin (𝓞 : Type*) [CommRing 𝓞] [IsDomain 𝓞]
    [IsDiscreteValuationRing 𝓞] (n : ℕ) :
    IsRegularLocalRing (MvPowerSeries (Fin n) 𝓞)
```

### `IsRegularLocalRing.quotient_span_singleton_of_notMem_sq_of_forall_minimalPrimes_notMem`

`Thm_IsRegularLocalRing_quotient_span_singleton_of_notMem_sq_of_forall_minimalPrimes_notMem` — Regularity of R/(x) for x ∈ 𝔪 ∖ 𝔪²

```lean
theorem IsRegularLocalRing.quotient_span_singleton_of_notMem_sq_of_forall_minimalPrimes_notMem
    (R : Type*) [CommRing R] [IsRegularLocalRing R] {x : R}
    (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2)
    (hxmin : ∀ p ∈ minimalPrimes R, x ∉ p) [IsLocalRing (R ⧸ Ideal.span {x})] :
    IsRegularLocalRing (R ⧸ Ideal.span {x}) ∧
      (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 = (maximalIdeal R).spanFinrank
```

### `IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two`

`Thm_IsRegularLocalRing_uniqueFactorizationMonoid_of_ringKrullDim_le_two` — Regular local rings of dimension ≤ 2 are factorial

```lean
theorem IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two
    (R : Type*) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (hdim : ringKrullDim R ≤ 2) :
    UniqueFactorizationMonoid R
```

## Nat (6)

### `Nat.eq_of_forall_dvd_sum_divisors_eq`

`Thm_Nat_eq_of_forall_dvd_sum_divisors_eq` — Divisor sums over all divisors of n determine the summands

```lean
theorem Nat.eq_of_forall_dvd_sum_divisors_eq {n : ℕ} (hn : 0 < n) (m m' : ℕ → ℕ)
    (h : ∀ e, e ∣ n → ∑ d ∈ e.divisors, m d = ∑ d ∈ e.divisors, m' d) :
    ∀ d, d ∣ n → m d = m' d
```

### `Nat.exists_forall_eq_macaulayPow_of_forall_le_macaulayPow`

`Thm_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow` — Eventual equality in Macaulay's growth bound

```lean
theorem Nat.exists_forall_eq_macaulayPow_of_forall_le_macaulayPow
    (H : ℕ → ℕ) (d₀ : ℕ) (hd₀ : 1 ≤ d₀)
    (hH : ∀ d, d₀ ≤ d → H (d + 1) ≤ Nat.macaulayPow d (H d)) :
    ∃ D₀ : ℕ, ∀ e, D₀ ≤ e → H (e + 1) = Nat.macaulayPow e (H e)
```

### `Nat.exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow`

`Thm_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow` — Maximal Macaulay growth forces polynomial behaviour

```lean
theorem Nat.exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow
    (H : ℕ → ℕ) (D₀ : ℕ) (hD₀ : 1 ≤ D₀)
    (hH : ∀ e, D₀ ≤ e → H (e + 1) = Nat.macaulayPow e (H e)) :
    ∃ P : Polynomial ℚ, ∀ e, D₀ ≤ e → (H e : ℚ) = P.eval (e : ℚ)
```

### `Nat.exists_squarefree_sq_add`

`Thm_Nat_exists_squarefree_sq_add` — Squarefree values of c² + D

```lean
theorem Nat.exists_squarefree_sq_add (D : ℕ) (hD : 1 ≤ D) :
    ∃ c : ℕ, 1 ≤ c ∧ Squarefree (c ^ 2 + D)
```

### `Nat.macaulayPow_add_add_le_macaulayPow_add_of_le_add`

`Thm_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add` — Green's numerical lemma for Macaulay pseudo-powers

```lean
theorem Nat.macaulayPow_add_add_le_macaulayPow_add_of_le_add
    (d x y u v : ℕ) (hd : 1 ≤ d) (hx : x ≤ u + v)
    (hu : Nat.macaulayPow d u + y ≤ Nat.macaulayPow d y)
    (hv : Nat.macaulayPow (d + 1) v + x ≤ Nat.macaulayPow (d + 1) x) :
    Nat.macaulayPow (d + 1) x + (x + y) ≤ Nat.macaulayPow (d + 1) (x + y)
```

### `Nat.macaulayPow_lt_macaulayPow_of_lt`

`Thm_Nat_macaulayPow_lt_macaulayPow_of_lt` — Macaulay's pseudo-power a ↦ a^{⟨ d⟩} is strictly increasing

```lean
theorem Nat.macaulayPow_lt_macaulayPow_of_lt {d : ℕ} (hd : 1 ≤ d) {a b : ℕ} (h : a < b) :
    Nat.macaulayPow d a < Nat.macaulayPow d b
```

## Real (6)

### `Real.abs_one_sub_exp_inv_eq_exp_neg_mul_abs_one_sub_exp_and_contDiff`

`Thm_Real_abs_one_sub_exp_inv_eq_exp_neg_mul_abs_one_sub_exp_and_contDiff` — Absolute value of 1-(± e^X)⁻¹ in exponential coordinates

```lean
theorem Real.abs_one_sub_exp_inv_eq_exp_neg_mul_abs_one_sub_exp_and_contDiff :
    (∀ X : ℝ, |1 - (Real.exp X)⁻¹| = Real.exp (-X) * |1 - Real.exp X|) ∧
    (∀ X : ℝ, |1 - (-Real.exp X)⁻¹| = 1 + Real.exp (-X)) ∧
    (∀ X : ℝ, 0 < 1 + Real.exp (-X)) ∧
    ContDiff ℝ (⊤ : ℕ∞) (fun X : ℝ => 1 + Real.exp (-X))
```

### `Real.exists_forall_norm_pow_mul_norm_iteratedFDeriv_mul_log_quadratic_le`

`Thm_Real_exists_forall_norm_pow_mul_norm_iteratedFDeriv_mul_log_quadratic_le` — Derivative bounds for the germ slog s of a positive definite binary form

```lean
theorem Real.exists_forall_norm_pow_mul_norm_iteratedFDeriv_mul_log_quadratic_le
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ∃ C : ℝ, 0 ≤ C ∧
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : ℝ × ℝ => (α * p.1 ^ 2 + β * p.2 ^ 2) * Real.log (α * p.1 ^ 2 + β * p.2 ^ 2))
        {p : ℝ × ℝ | p ≠ 0} ∧
      ∀ n : ℕ, n ≤ 4 → ∀ p : ℝ × ℝ, p ≠ 0 →
        ‖p‖ ^ n *
            ‖iteratedFDeriv ℝ n
                (fun p : ℝ × ℝ => (α * p.1 ^ 2 + β * p.2 ^ 2) * Real.log (α * p.1 ^ 2 + β * p.2 ^ 2))
                p‖ ≤
          C * ‖p‖ ^ 2 * (1 + |Real.log ‖p‖|)
```

### `Real.norm_le_and_norm_integral_cexp_mul_le_mul_inv_one_add_abs_sq_of_piecewise_contDiff_two`

`Thm_Real_norm_le_and_norm_integral_cexp_mul_le_mul_inv_one_add_abs_sq_of_piecewise_contDiff_two` — Quadratic decay of g and ̂ g for a C² function with one corner

```lean
theorem Real.norm_le_and_norm_integral_cexp_mul_le_mul_inv_one_add_abs_sq_of_piecewise_contDiff_two
    (g gm gp : ℝ → ℂ) (R M₀ M₂ J : ℝ) (hR : 0 ≤ R)
    (hgm : ContDiff ℝ 2 gm) (hgp : ContDiff ℝ 2 gp)
    (hm : ∀ x, x ≤ 0 → g x = gm x) (hp : ∀ x, 0 ≤ x → g x = gp x)
    (hsupp : ∀ x, R < |x| → g x = 0)
    (hM₀ : ∀ x, ‖g x‖ ≤ M₀)
    (hM₂m : ∀ x, x ≤ 0 → ‖iteratedDeriv 2 gm x‖ ≤ M₂)
    (hM₂p : ∀ x, 0 ≤ x → ‖iteratedDeriv 2 gp x‖ ≤ M₂)
    (hJ : ‖deriv gp 0 - deriv gm 0‖ ≤ J) :
    (∀ x : ℝ, ‖g x‖ ≤
        (M₀ * (1 + R) ^ 2 + 8 * R * M₀ + (2 * R * M₂ + J) / Real.pi ^ 2) * (1 + |x|)⁻¹ ^ 2) ∧
    (∀ ξ : ℝ, ‖∫ x : ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((ξ * x : ℝ) : ℂ))) * g x‖ ≤
        (M₀ * (1 + R) ^ 2 + 8 * R * M₀ + (2 * R * M₂ + J) / Real.pi ^ 2) * (1 + |ξ|)⁻¹ ^ 2)
```

### `Real.norm_le_and_norm_integral_cexp_sum_mul_le_mul_prod_inv_one_add_abs_sq_of_contDiff`

`Thm_Real_norm_le_and_norm_integral_cexp_sum_mul_le_mul_prod_inv_one_add_abs_sq_of_contDiff` — Quadratic decay of a compactly supported C^{2r} function and its Fourier transform

```lean
theorem Real.norm_le_and_norm_integral_cexp_sum_mul_le_mul_prod_inv_one_add_abs_sq_of_contDiff
    {r : ℕ} (g : (Fin r → ℝ) → ℂ) (R M : ℝ) (hR : 0 ≤ R)
    (hg : ContDiff ℝ ((2 * r : ℕ) : ℕ∞) g)
    (hsupp : ∀ x : Fin r → ℝ, (∃ k, R < |x k|) → g x = 0)
    (hM : ∀ n : ℕ, n ≤ 2 * r → ∀ x : Fin r → ℝ, ‖iteratedFDeriv ℝ n g x‖ ≤ M) :
    (∀ x : Fin r → ℝ, ‖g x‖ ≤ (M * ((1 + R) ^ (2 * r) + (8 * R) ^ r)) * ∏ k, (1 + |x k|)⁻¹ ^ 2) ∧
    (∀ ξ : Fin r → ℝ,
      ‖∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) * g x‖ ≤
        (M * ((1 + R) ^ (2 * r) + (8 * R) ^ r)) * ∏ k, (1 + |ξ k|)⁻¹ ^ 2)
```

### `Real.poitouKernel_admissible_and_archBound`

`Thm_Real_poitouKernel_admissible_and_archBound` — Properties of Poitou's kernel e^{-11x^2/100}/cosh(x/2)

```lean
theorem Real.poitouKernel_admissible_and_archBound :
    let F : ℝ → ℝ := fun x => Real.exp (-(11 / 100) * x ^ 2) / Real.cosh (x / 2)

    Differentiable ℝ F ∧ (∀ x : ℝ, F (-x) = F x) ∧ F 0 = 1 ∧ (∀ x : ℝ, 0 ≤ F x) ∧
    (∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧ ∀ x : ℝ, |F x| ≤ c * Real.exp (-(1 / 2 + ε) * |x|)) ∧

    (∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 →
      0 ≤ ∫ x : ℝ, F x * Real.exp ((ρ.re - 1 / 2) * x) * Real.cos (ρ.im * x)) ∧

    ContDiff ℝ 2 F ∧
    (∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧ ∀ k : Fin 3, ∀ x : ℝ,
      |iteratedDeriv k F x| ≤ c * Real.exp (-(1 / 2 + ε) * |x|)) ∧

    (2 * ∫ x in Set.Ioi (0 : ℝ), F x * (Real.exp (x / 2) + Real.exp (-(x / 2)))
        = 2 * Real.sqrt (100 * Real.pi / 11)) ∧

    (Real.log (9805 / 2000) + (1 / 12) * Real.sqrt (100 * Real.pi / 11)
      ≤ Real.eulerMascheroniConstant + Real.log (4 * Real.pi)
          - ∫ x in Set.Ioi (0 : ℝ), (1 - F x) / (Real.exp (x / 2) - Real.exp (-(x / 2))))
```

### `Real.tsum_comp_add_intCast_eq_tsum_integral_mul_cexp`

`Thm_Real_tsum_comp_add_intCast_eq_tsum_integral_mul_cexp` — Poisson summation on ℝᵈ for the lattice ℤᵈ

```lean
theorem Real.tsum_comp_add_intCast_eq_tsum_integral_mul_cexp
    {d : Type*} [Fintype d] (f : C(d → ℝ, ℂ))
    (h_norm : ∀ K : Compacts (d → ℝ),
      Summable fun n : d → ℤ => ‖(f.comp (ContinuousMap.addRight (fun i => (n i : ℝ)))).restrict K‖)
    (h_sum : Summable fun n : d → ℤ =>
      ∫ y : d → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, (n i : ℝ) * y i : ℝ) : ℂ))) * f y)
    (x : d → ℝ) :
    ∑' n : d → ℤ, f (x + fun i => (n i : ℝ)) =
      ∑' n : d → ℤ, (∫ y : d → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, (n i : ℝ) * y i : ℝ) : ℂ))) * f y) *
        Complex.exp (2 * Real.pi * Complex.I * ((∑ i, (n i : ℝ) * x i : ℝ) : ℂ))
```

## SchwartzMap (5)

### `SchwartzMap.exists_coe_eq_vectorFourierIntegral`

`Thm_SchwartzMap_exists_coe_eq_vectorFourierIntegral` — Fourier transform for a nondegenerate pairing preserves S(V)

```lean
theorem SchwartzMap.exists_coe_eq_vectorFourierIntegral
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure]
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate) (f : 𝓢(V, ℂ)) :
    ∃ g : 𝓢(V, ℂ), ⇑g = VectorFourier.fourierIntegral 𝐞 μ B f
```

### `SchwartzMap.exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq`

`Thm_SchwartzMap_exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq` — The Gaussian e^{-π‖x‖^2} is a Schwartz function

```lean
theorem SchwartzMap.exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq (ι : Type) [Fintype ι] :
    ∃ g : 𝓢(EuclideanSpace ℝ ι, ℂ), ∀ x : EuclideanSpace ℝ ι,
      g x = ((Real.exp (-(Real.pi * ‖x‖ ^ 2)) : ℝ) : ℂ)
```

### `SchwartzMap.exists_hasCompactSupport_re_nonneg_apply_eq_one_of_norm_le_one`

`Thm_SchwartzMap_exists_hasCompactSupport_re_nonneg_apply_eq_one_of_norm_le_one` — A compactly supported Schwartz bump on a finite-dimensional real space

```lean
theorem SchwartzMap.exists_hasCompactSupport_re_nonneg_apply_eq_one_of_norm_le_one
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    ∃ g : 𝓢(E, ℂ), HasCompactSupport g ∧ (∀ x, 0 ≤ (g x).re ∧ (g x).im = 0) ∧ (∀ x, ‖g x‖ ≤ 1) ∧
      (∀ x, ‖x‖ ≤ 1 → g x = 1) ∧ (∀ x, 2 ≤ ‖x‖ → g x = 0)
```

### `SchwartzMap.exists_seminorm_vectorFourierIntegral_le`

`Thm_SchwartzMap_exists_seminorm_vectorFourierIntegral_le` — Seminorm bound for the Fourier transform of a nondegenerate pairing

```lean
theorem SchwartzMap.exists_seminorm_vectorFourierIntegral_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure]
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate) (k n : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ f : 𝓢(V, ℂ), ∃ g : 𝓢(V, ℂ),
      ⇑g = VectorFourier.fourierIntegral 𝐞 μ B f ∧
      SchwartzMap.seminorm ℝ k n g ≤ C * (s.sup (schwartzSeminormFamily ℝ V ℂ)) f
```

### `SchwartzMap.tsum_eq_tsum_fourier_euclideanSpace`

`Thm_SchwartzMap_tsum_eq_tsum_fourier_euclideanSpace` — Poisson summation on ℝ^ι for Schwartz functions

```lean
theorem SchwartzMap.tsum_eq_tsum_fourier_euclideanSpace
    {ι : Type*} [Fintype ι] (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) (x : EuclideanSpace ℝ ι) :
    ∑' n : ι → ℤ, f (x + WithLp.toLp 2 (fun i ↦ (n i : ℝ))) =
      ∑' n : ι → ℤ, 𝓕 f (WithLp.toLp 2 (fun i ↦ (n i : ℝ))) *
        (𝐞 ⟪(WithLp.toLp 2 (fun i ↦ (n i : ℝ)) : EuclideanSpace ℝ ι), x⟫_ℝ : ℂ)
```

## exteriorPower (5)

### `exteriorPower.exists_linearEquiv_baseChange`

`Thm_exteriorPower_exists_linearEquiv_baseChange` — Exterior powers commute with base change

```lean
theorem exteriorPower.exists_linearEquiv_baseChange
    (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
    (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ) :
    ∃ e : A ⊗[R] (⋀[R]^n M) ≃ₗ[A] ⋀[A]^n (A ⊗[R] M),
      ∀ (a : A) (m : Fin n → M),
        e (a ⊗ₜ exteriorPower.ιMulti R n m) =
          a • exteriorPower.ιMulti A n (fun i => (1 : A) ⊗ₜ[R] m i)
```

### `exteriorPower.iotaMulti_comp_eq_det_smul`

`Thm_exteriorPower_iotaMulti_comp_eq_det_smul` — Top wedge of images under an endomorphism is det f times the wedge

```lean
theorem exteriorPower.iotaMulti_comp_eq_det_smul {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M]
    [Module A M] {n : ℕ} (b : Module.Basis (Fin n) A M) (f : M →ₗ[A] M) (m : Fin n → M) :
    exteriorPower.ιMulti A n (f ∘ m) = LinearMap.det f • exteriorPower.ιMulti A n m
```

### `exteriorPower.map_apply_eq_det_smul`

`Thm_exteriorPower_map_apply_eq_det_smul` — Top exterior power of an endomorphism is multiplication by det

```lean
theorem exteriorPower.map_apply_eq_det_smul {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M]
    [Module A M] {ι : Type*} [Fintype ι] (b : Module.Basis ι A M) {n : ℕ} (hn : Fintype.card ι = n)
    (f : M →ₗ[A] M) (x : ⋀[A]^n M) :
    exteriorPower.map n f x = LinearMap.det f • x
```

### `exteriorPower.map_mulLeft_apply_eq_norm_smul`

`Thm_exteriorPower_map_mulLeft_apply_eq_norm_smul` — Top exterior power of multiplication by x is N_{B/A}(x)

```lean
theorem exteriorPower.map_mulLeft_apply_eq_norm_smul {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι A B) {n : ℕ} (hn : Fintype.card ι = n)
    (x : B) (w : ⋀[A]^n B) :
    exteriorPower.map n (LinearMap.mulLeft A x) w = Algebra.norm A x • w
```

### `exteriorPower.range_map_subtype_eq_maximalIdeal_smul_top`

`Thm_exteriorPower_range_map_subtype_eq_maximalIdeal_smul_top` — Image of bigwedgeᵈ N in bigwedgeᵈ M for corank-one N over a DVR

```lean
theorem exteriorPower.range_map_subtype_eq_maximalIdeal_smul_top {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    {d : ℕ} (hd : Module.finrank R M = d)
    (N : Submodule R M) (e : (M ⧸ N) ≃ₗ[R] (R ⧸ IsLocalRing.maximalIdeal R)) :
    LinearMap.range (exteriorPower.map d N.subtype) = IsLocalRing.maximalIdeal R • ⊤
```

## AnalyticOnNhd (4)

### `AnalyticOnNhd.integrableOn_log_norm_ball`

`Thm_AnalyticOnNhd_integrableOn_log_norm_ball` — Integrability of log‖F‖ on a disc

```lean
theorem AnalyticOnNhd.integrableOn_log_norm_ball {F : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall c R)) (hc : F c ≠ 0) :
    MeasureTheory.IntegrableOn (fun z ↦ Real.log ‖F z‖) (Metric.ball c R)
```

### `AnalyticOnNhd.log_norm_le_circleAverage_log_norm`

`Thm_AnalyticOnNhd_log_norm_le_circleAverage_log_norm` — Sub-mean-value inequality for log‖F‖ on circles

```lean
theorem AnalyticOnNhd.log_norm_le_circleAverage_log_norm {F : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall c |R|)) (hc : F c ≠ 0) :
    Real.log ‖F c‖ ≤ Real.circleAverage (fun z ↦ Real.log ‖F z‖) c R
```

### `AnalyticOnNhd.log_norm_sub_mul_le_circleAverage`

`Thm_AnalyticOnNhd_log_norm_sub_mul_le_circleAverage` — Weighted sub-mean-value inequality for log‖F‖

```lean
theorem AnalyticOnNhd.log_norm_sub_mul_le_circleAverage {F : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall c |R|)) (hc : F c ≠ 0) {g : ℂ → ℝ} {k M : ℝ}
    (hg : CircleIntegrable g c R) (hM : ∀ z ∈ Metric.sphere c |R|, g z ≤ M) (hk : 0 ≤ k) :
    Real.log ‖F c‖ - k * M ≤ Real.circleAverage (fun z ↦ Real.log ‖F z‖ - k * g z) c R
```

### `AnalyticOnNhd.log_norm_sub_mul_le_setAverage_ball`

`Thm_AnalyticOnNhd_log_norm_sub_mul_le_setAverage_ball` — Solid sub-mean-value inequality for log‖F‖-kg on a disc

```lean
theorem AnalyticOnNhd.log_norm_sub_mul_le_setAverage_ball {F : ℂ → ℂ} {g : ℂ → ℝ} {c : ℂ}
    {R k M : ℝ} (hF : AnalyticOnNhd ℂ F (Metric.closedBall c R)) (hc : F c ≠ 0) (hR : 0 < R)
    (hg : ContinuousOn g (Metric.closedBall c R)) (hM : ∀ z ∈ Metric.closedBall c R, g z ≤ M)
    (hk : 0 ≤ k) :
    Real.log ‖F c‖ - k * M ≤ ⨍ z in Metric.ball c R, (Real.log ‖F z‖ - k * g z)
```

## Function (4)

### `Function.exists_eq_apply_sub_of_sum_range_minimalPeriod_eq_zero`

`Thm_Function_exists_eq_apply_sub_of_sum_range_minimalPeriod_eq_zero` — Vanishing orbit sums give a coboundary G∘ f-G

```lean
theorem Function.exists_eq_apply_sub_of_sum_range_minimalPeriod_eq_zero {X : Type*} {A : Type*} [AddCommGroup A]
    (f : X → X) (hf : ∀ x : X, 0 < Function.minimalPeriod f x) (v : X → A)
    (hv : ∀ x : X, ∑ k ∈ Finset.range (Function.minimalPeriod f x), v (f^[k] x) = 0) :
    ∃ G : X → A, ∀ x : X, v x = G (f x) - G x
```

### `Function.exists_eq_sum_mul_prod_apply_update_of_forall_exists_forall_apply_update_eq_sum_mul`

`Thm_Function_exists_eq_sum_mul_prod_apply_update_of_forall_exists_forall_apply_update_eq_sum_mul` — Finite-rank partial spans give a finite sum of products

```lean
theorem Function.exists_eq_sum_mul_prod_apply_update_of_forall_exists_forall_apply_update_eq_sum_mul
    {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type}
    (Φ : (∀ i, X i) → ℂ) (i₀ : ι)
    (h : ∀ i, i ≠ i₀ → ∃ (d : ℕ) (φ : Fin d → X i → ℂ), ∀ b : ∀ j, X j, ∃ c : Fin d → ℂ,
      ∀ t : X i, Φ (Function.update b i t) = ∑ k, c k * φ k t) :
    ∃ (m : ℕ) (coef : Fin m → ℂ) (β : Fin m → ι → ∀ j, X j),
      ∀ t : ∀ j, X j, Φ t = ∑ α, coef α * ∏ i, Φ (Function.update (β α i) i (t i))
```

### `Function.mul_pow_card_sub_one_eq_mul_prod_update_of_forall_exists_linearCombination_update_eq_zero`

`Thm_Function_mul_pow_card_sub_one_eq_mul_prod_update_of_forall_exists_linearCombination_update_eq_zero` — Separation of variables from pairwise dependence in all but one direction

```lean
theorem Function.mul_pow_card_sub_one_eq_mul_prod_update_of_forall_exists_linearCombination_update_eq_zero
    {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type}
    (Φ : (∀ i, X i) → ℂ) (i₀ : ι)
    (h : ∀ i, i ≠ i₀ → ∀ b b' : ∀ j, X j,
      ∃ c : ℂ × ℂ, c ≠ 0 ∧ ∀ t : X i, c.1 * Φ (Function.update b i t) + c.2 * Φ (Function.update b' i t) = 0)
    (b₀ t : ∀ j, X j) :
    Φ t * Φ b₀ ^ (Fintype.card ι - 1) =
      Φ (Function.update b₀ i₀ (t i₀)) * ∏ i ∈ Finset.univ.erase i₀, Φ (Function.update b₀ i (t i))
```

### `Function.orbitCensus_of_dihedralThree_relations`

`Thm_Function_orbitCensus_of_dihedralThree_relations` — Orbit census for a dihedral pair of order-two and order-three maps

```lean
theorem Function.orbitCensus_of_dihedralThree_relations
    {X : Type*} [Fintype X] [DecidableEq X] (a b : X → X)
    (ha : ∀ x, a (a x) = x) (hb : ∀ x, b (b (b x)) = x) (hab : ∀ x, a (b x) = b (b (a x)))
    {ι : Type*} [DecidableEq ι] (c : X → ι)
    (hc : ∀ x y, c x = c y ↔
      (y = x ∨ y = a x ∨ y = b x ∨ y = b (b x) ∨ y = a (b x) ∨ y = a (b (b x))))
    (S : Finset ι) (hS : ∀ p, p ∈ S ↔ ∃ x, c x = p) :
    (∀ x, (Finset.univ.filter fun y => c y = c x).card = 1 ∨
        (Finset.univ.filter fun y => c y = c x).card = 2 ∨
        (Finset.univ.filter fun y => c y = c x).card = 3 ∨
        (Finset.univ.filter fun y => c y = c x).card = 6) ∧
    (S.filter fun p => (Finset.univ.filter fun y => c y = p).card = 1 ∨
        (Finset.univ.filter fun y => c y = p).card = 3).card =
      (Finset.univ.filter fun x => a x = x).card ∧
    (S.filter fun p => (Finset.univ.filter fun y => c y = p).card = 1).card +
        2 * (S.filter fun p => (Finset.univ.filter fun y => c y = p).card = 2).card =
      (Finset.univ.filter fun x => b x = x).card
```

## Ideal (4)

### `Ideal.existsUnique_sub_mem_and_eval_eq_zero_of_isUnit_derivative`

`Thm_Ideal_existsUnique_sub_mem_and_eval_eq_zero_of_isUnit_derivative` — Hensel's lemma along an adically complete ideal

```lean
theorem Ideal.existsUnique_sub_mem_and_eval_eq_zero_of_isUnit_derivative
    {W : Type*} [CommRing W] (I : Ideal W) [IsAdicComplete I W]
    (G : Polynomial W) (y₀ : W) (hG : G.eval y₀ ∈ I)
    (hG' : IsUnit ((Polynomial.derivative G).eval y₀)) :
    ∃! y : W, y - y₀ ∈ I ∧ G.eval y = 0
```

### `Ideal.exists_eq_smul_one_tmul_and_one_tmul_eq_zero_of_isLocalization`

`Thm_Ideal_exists_eq_smul_one_tmul_and_one_tmul_eq_zero_of_isLocalization` — Generators of K ⊗_P IP and vanishing on J· I

```lean
theorem Ideal.exists_eq_smul_one_tmul_and_one_tmul_eq_zero_of_isLocalization
    (R : Type) [CommRing R] {n : ℕ} (M : Submonoid (MvPolynomial (Fin n) R))
    (P : Type) [CommRing P] [Algebra (MvPolynomial (Fin n) R) P] [IsLocalization M P]
    (I J : Ideal (MvPolynomial (Fin n) R)) (𝔞 : Ideal P) (h𝔞 : 𝔞 = I.map (algebraMap (MvPolynomial (Fin n) R) P))
    (K : Type) [CommRing K] [Algebra P K] [Algebra (MvPolynomial (Fin n) R) K]
    [IsScalarTower (MvPolynomial (Fin n) R) P K]
    (hK : Function.Surjective (algebraMap (MvPolynomial (Fin n) R) K))
    (hJK : ∀ j ∈ J, algebraMap (MvPolynomial (Fin n) R) K j = 0) :
    (∀ z : K ⊗[P] ↥𝔞, ∃ (c : K) (a : MvPolynomial (Fin n) R) (ha : a ∈ I),
        z = c • ((1 : K) ⊗ₜ[P] (⟨algebraMap (MvPolynomial (Fin n) R) P a,
          h𝔞 ▸ Ideal.mem_map_of_mem (algebraMap (MvPolynomial (Fin n) R) P) ha⟩ : ↥𝔞))) ∧
    (∀ (a : MvPolynomial (Fin n) R) (ha : a ∈ J * I),
        ((1 : K) ⊗ₜ[P] (⟨algebraMap (MvPolynomial (Fin n) R) P a,
          h𝔞 ▸ Ideal.mem_map_of_mem (algebraMap (MvPolynomial (Fin n) R) P) (Ideal.mul_le_right ha)⟩ : ↥𝔞) : K ⊗[P] ↥𝔞) = 0)
```

### `Ideal.finite_quotient_of_isMaximal_of_finiteType_of_finite_quotient`

`Thm_Ideal_finite_quotient_of_isMaximal_of_finiteType_of_finite_quotient` — Finiteness of residue fields of finite-type algebras

```lean
theorem Ideal.finite_quotient_of_isMaximal_of_finiteType_of_finite_quotient
    (A : Type) [CommRing A] (𝔪 : Ideal A) [𝔪.IsMaximal] [Finite (A ⧸ 𝔪)]
    (B : Type) [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (𝔭 : Ideal B) [𝔭.IsMaximal] (h𝔪 : Ideal.map (algebraMap A B) 𝔪 ≤ 𝔭) :
    Finite (B ⧸ 𝔭)
```

### `Ideal.height_eq_one_of_isDiscreteValuationRing_localization_atPrime`

`Thm_Ideal_height_eq_one_of_isDiscreteValuationRing_localization_atPrime` — A prime with DVR localisation has height one

```lean
theorem Ideal.height_eq_one_of_isDiscreteValuationRing_localization_atPrime
    {R : Type*} [CommRing R] [IsDomain R] (p : Ideal R) [p.IsPrime]
    (h : IsDiscreteValuationRing (Localization.AtPrime p)) : p.height = 1
```

## Int (4)

### `Int.exists_modEq_and_modEq_and_isCoprime`

`Thm_Int_exists_modEq_and_modEq_and_isCoprime` — Unimodular pairs mod n lift to coprime integer pairs

```lean
theorem Int.exists_modEq_and_modEq_and_isCoprime {n c d : ℤ}
    (h : ∃ x y z : ℤ, x * c + y * d + z * n = 1) :
    ∃ c' d' : ℤ, c' ≡ c [ZMOD n] ∧ d' ≡ d [ZMOD n] ∧ IsCoprime c' d'
```

### `Int.exists_not_dvd_and_le_and_not_isSquare_and_forall_prime_of_sq_sub_four_mul_ne_zero`

`Thm_Int_exists_not_dvd_and_le_and_not_isSquare_and_forall_prime_of_sq_sub_four_mul_ne_zero` — Normalising a quadratic translate: non-square, primitive, prime to p

```lean
theorem Int.exists_not_dvd_and_le_and_not_isSquare_and_forall_prime_of_sq_sub_four_mul_ne_zero (t q : ℤ) (hD : t ^ 2 - 4 * q ≠ 0) (p : ℕ) [Fact p.Prime] (h : ∃ a₀ : ℤ, ¬ (p : ℤ) ∣ a₀ ^ 2 + t * a₀ + q) : ∃ a : ℤ, ¬ (p : ℤ) ∣ a ^ 2 + t * a + q ∧ 2 ≤ a ^ 2 + t * a + q ∧ ¬ IsSquare (a ^ 2 + t * a + q) ∧ ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ 2 * a + t → ¬ (ℓ : ℤ) ^ 2 ∣ a ^ 2 + t * a + q
```

### `Int.exists_pos_and_not_isSquare_sq_sub_mul_add_of_sq_lt_four_mul`

`Thm_Int_exists_pos_and_not_isSquare_sq_sub_mul_add_of_sq_lt_four_mul` — A non-square positive value of k²-tk+n

```lean
theorem Int.exists_pos_and_not_isSquare_sq_sub_mul_add_of_sq_lt_four_mul
    (t n : ℤ) (htn : t ^ 2 < 4 * n) :
    ∃ k : ℤ, 0 < k ^ 2 - t * k + n ∧ ¬ IsSquare (k ^ 2 - t * k + n)
```

### `Int.exists_squarefree_sq_add_mul_add_mul_sq_of_sq_lt_four_mul`

`Thm_Int_exists_squarefree_sq_add_mul_add_mul_sq_of_sq_lt_four_mul` — Positive-definite binary form represents a squarefree integer ≥ 2

```lean
theorem Int.exists_squarefree_sq_add_mul_add_mul_sq_of_sq_lt_four_mul (t n : ℤ) (h : t ^ 2 < 4 * n) :
    ∃ a b : ℤ, b ≠ 0 ∧ Squarefree (a ^ 2 + t * a * b + n * b ^ 2).toNat ∧
      2 ≤ (a ^ 2 + t * a * b + n * b ^ 2).toNat
```

## LinearIndependent (4)

### `LinearIndependent.exists_det_submatrix_ne_zero`

`Thm_LinearIndependent_exists_det_submatrix_ne_zero` — Linearly independent vectors in k^ι have a nonzero minor

```lean
theorem LinearIndependent.exists_det_submatrix_ne_zero
    {k : Type*} [Field k] {ι : Type*} {n : ℕ}
    (f : Fin n → ι → k) (hf : LinearIndependent k f) :
    ∃ s : Fin n → ι, Function.Injective s ∧ (Matrix.of fun l j => f j (s l)).det ≠ 0
```

### `LinearIndependent.linearMap_baseChange_of_int`

`Thm_LinearIndependent_linearMap_baseChange_of_int` — Base change to a characteristic-zero field preserves independence of endomorphisms

```lean
theorem LinearIndependent.linearMap_baseChange_of_int (K : Type) [Field K] [CharZero K]
    (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ] {ι : Type}
    (f : ι → Module.End ℤ Λ) (hf : LinearIndependent ℤ f) :
    LinearIndependent K (fun i => ((f i).baseChange K : Module.End K (K ⊗[ℤ] Λ)))
```

### `LinearIndependent.map_of_finrank_le_relfinrank_closure`

`Thm_LinearIndependent_map_of_finrank_le_relfinrank_closure` — Linear disjointness ascends a finite extension under a degree bound

```lean
theorem LinearIndependent.map_of_finrank_le_relfinrank_closure
    (k : Type) [Field k]
    (E E' : Type) [Field E] [Field E'] [Algebra k E] [Algebra k E'] [Algebra E E']
    [IsScalarTower k E E'] [Module.Finite E E']
    (C Ω : Type) [Field C] [Field Ω] [Algebra k C] [Algebra C Ω] [Algebra k Ω] [IsScalarTower k C Ω]
    (ι : E →+* Ω) (ι' : E' →+* Ω)
    (hιk : ∀ z : k, ι (algebraMap k E z) = algebraMap C Ω (algebraMap k C z))
    (hι' : ∀ x : E, ι' (algebraMap E E' x) = ι x)
    (h1 : ∀ t : Finset E, LinearIndependent k (fun x : t => (x : E)) →
      LinearIndependent C (fun x : t => ι (x : E)))
    (h2 : Module.finrank E E' ≤
      Subfield.relfinrank (Subfield.closure (Set.range (algebraMap C Ω) ∪ Set.range ι))
        (Subfield.closure (Set.range (algebraMap C Ω) ∪ Set.range ι'))) :
    ∀ t : Finset E', LinearIndependent k (fun x : t => (x : E')) →
      LinearIndependent C (fun x : t => ι' (x : E'))
```

### `LinearIndependent.of_forall_mem_span_exists_sum_zsmul_eq`

`Thm_LinearIndependent_of_forall_mem_span_exists_sum_zsmul_eq` — ℤ-generators of a full lattice are ℝ-independent

```lean
theorem LinearIndependent.of_forall_mem_span_exists_sum_zsmul_eq {V : Type*} [AddCommGroup V] [Module ℝ V]
    {k : ℕ} (b₀ : Module.Basis (Fin k) ℝ V) (v : Fin k → V)
    (hgen : ∀ x ∈ Submodule.span ℤ (Set.range b₀), ∃ n : Fin k → ℤ, (∑ i, n i • v i) = x) :
    LinearIndependent ℝ v
```

## Monoid (4)

### `Monoid.CoprodI.exists_addMonoidHom_conj_pow_minimalPeriod_eq_of_finsum_eq_zero`

`Thm_Monoid_CoprodI_exists_addMonoidHom_conj_pow_minimalPeriod_eq_of_finsum_eq_zero` — Sum-zero cusp functions arise from characters of H

```lean
theorem Monoid.CoprodI.exists_addMonoidHom_conj_pow_minimalPeriod_eq_of_finsum_eq_zero
    (t : Monoid.CoprodI (fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))))
    (ht : t = Monoid.CoprodI.of (M := fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))) (i := 0)
                (Multiplicative.ofAdd 1) *
              Monoid.CoprodI.of (M := fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))) (i := 1)
                (Multiplicative.ofAdd 1))
    (H : Subgroup (Monoid.CoprodI (fun i : Fin 2 => Multiplicative (ZMod (i.val + 2)))))
    [H.FiniteIndex] (R : Type) [AddCommGroup R]
    (a : MulAction.orbitRel.Quotient (Subgroup.zpowers t)
          (Monoid.CoprodI (fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))) ⧸ H) → R)
    (ha : ∑ᶠ c, a c = 0) :
    ∃ φ : Additive H →+ R,
      ∀ (g : Monoid.CoprodI (fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))))
        (hg : g⁻¹ * t ^ Function.minimalPeriod (fun x => t • x)
                (g : Monoid.CoprodI (fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))) ⧸ H) * g ∈ H),
        φ (Additive.ofMul ⟨_, hg⟩)
          = a (Quotient.mk (MulAction.orbitRel (Subgroup.zpowers t) _)
              (g : Monoid.CoprodI (fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))) ⧸ H))
```

### `Monoid.CoprodI.finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one`

`Thm_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one` — Kurosh-type bound for subgroups of a free product

```lean
theorem Monoid.CoprodI.finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one
    {G : Fin 2 → Type*} [∀ i, Group (G i)]
    (H : Subgroup (Monoid.CoprodI G)) [H.FiniteIndex] (K : Type) [Field K]
    (hK : ∀ i, (Nat.card (G i) : K) ≠ 0) :
    Module.finrank K (Additive H →+ K)
      + Nat.card (MulAction.orbitRel.Quotient H
          (Monoid.CoprodI G ⧸ (Monoid.CoprodI.of (M := G) (i := 0)).range))
      + Nat.card (MulAction.orbitRel.Quotient H
          (Monoid.CoprodI G ⧸ (Monoid.CoprodI.of (M := G) (i := 1)).range))
      ≤ H.index + 1
```

### `Monoid.CoprodI.isTree_cosetGraph`

`Thm_Monoid_CoprodI_isTree_cosetGraph` — The coset graph of a free product of two groups is a tree

```lean
theorem Monoid.CoprodI.isTree_cosetGraph {G : Fin 2 → Type*} [∀ i, Group (G i)] :
    (SimpleGraph.fromRel fun v w : (i : Fin 2) × (Monoid.CoprodI G ⧸ (Monoid.CoprodI.of (M := G) (i := i)).range) =>
        v.1 ≠ w.1 ∧ ∃ g : Monoid.CoprodI G,
          v.2 = (QuotientGroup.mk g : Monoid.CoprodI G ⧸ (Monoid.CoprodI.of (M := G) (i := v.1)).range) ∧
          w.2 = (QuotientGroup.mk g : Monoid.CoprodI G ⧸ (Monoid.CoprodI.of (M := G) (i := w.1)).range)).IsTree
```

### `Monoid.CoprodI.nonempty_freeGroupBasis_fin_kuroshRank`

`Thm_Monoid_CoprodI_nonempty_freeGroupBasis_fin_kuroshRank` — Freeness of torsion-free finite-index subgroups of G₀ * G₁

```lean
theorem Monoid.CoprodI.nonempty_freeGroupBasis_fin_kuroshRank {G : Fin 2 → Type*} [∀ i, Group (G i)] [∀ i, Finite (G i)]
    (H : Subgroup (Monoid.CoprodI G)) [H.FiniteIndex]
    (hH : ∀ (i : Fin 2) (g : Monoid.CoprodI G) (x : G i), g⁻¹ * Monoid.CoprodI.of x * g ∈ H → x = 1) :
    Nonempty (FreeGroupBasis
      (Fin (1 + H.index - H.index / Nat.card (G 0) - H.index / Nat.card (G 1))) H)
```

## SetLike (4)

### `SetLike.GradedMonoid.eq_zero_of_mem_two_of_map_eq_add_of_kunneth_injective`

`Thm_SetLike_GradedMonoid_eq_zero_of_mem_two_of_map_eq_add_of_kunneth_injective` — Primitive degree-two elements vanish under an injective Künneth map

```lean
theorem SetLike.GradedMonoid.eq_zero_of_mem_two_of_map_eq_add_of_kunneth_injective
    {k : Type u} [Field k] {H : Type u} [Ring H] [Algebra k H]
    {H' : Type u} [Ring H'] [Algebra k H']
    (𝒜 : ℕ → Submodule k H) [SetLike.GradedMonoid 𝒜] (p₁ p₂ m : H →ₐ[k] H')
    (hK : Function.Injective (DirectSum.toModule k (ℕ × ℕ) H' fun ab : ℕ × ℕ =>
      LinearMap.mul' k H' ∘ₗ
        TensorProduct.map (p₁.toLinearMap ∘ₗ (𝒜 ab.1).subtype) (p₂.toLinearMap ∘ₗ (𝒜 ab.2).subtype)))
    (hanti : ∀ x ∈ 𝒜 1, ∀ y ∈ 𝒜 1, p₂ x * p₁ y = -(p₁ y * p₂ x))
    (hcomm : ∀ x ∈ 𝒜 2, ∀ y ∈ 𝒜 1, p₂ x * p₁ y = p₁ y * p₂ x)
    (hm : ∀ y ∈ 𝒜 1, m y = p₁ y + p₂ y)
    {d : ℕ} (a : Fin d → H) (ha : ∀ i, a i ∈ 𝒜 1) (hli : LinearIndependent k a)
    (hd : ∀ n : ℕ, d < n → 𝒜 n = ⊥)
    (x : H) (hx : x ∈ 𝒜 2) (hmx : m x = p₁ x + p₂ x) :
    x = 0
```

### `SetLike.GradedMonoid.exists_forall_mem_two_eq_smul_mul_of_finrank_two_add_one_eq_of_kunneth_injective`

`Thm_SetLike_GradedMonoid_exists_forall_mem_two_eq_smul_mul_of_finrank_two_add_one_eq_of_kunneth_injective` — Degree two spanned by one product of degree-one elements

```lean
theorem SetLike.GradedMonoid.exists_forall_mem_two_eq_smul_mul_of_finrank_two_add_one_eq_of_kunneth_injective
    {k : Type u} [Field k] {H : Type u} [Ring H] [Algebra k H]
    {H' : Type u} [Ring H'] [Algebra k H']
    (𝒜 : ℕ → Submodule k H) [SetLike.GradedMonoid 𝒜] (p₁ p₂ m : H →ₐ[k] H')
    (hK : Function.Injective (DirectSum.toModule k (ℕ × ℕ) H' fun ab : ℕ × ℕ =>
      LinearMap.mul' k H' ∘ₗ
        TensorProduct.map (p₁.toLinearMap ∘ₗ (𝒜 ab.1).subtype) (p₂.toLinearMap ∘ₗ (𝒜 ab.2).subtype)))
    (hanti : ∀ x ∈ 𝒜 1, ∀ y ∈ 𝒜 1, p₂ x * p₁ y = -(p₁ y * p₂ x))
    (hm : ∀ x ∈ 𝒜 1, m x = p₁ x + p₂ x)
    (h3 : 𝒜 3 = ⊥) [Module.Finite k ↥(𝒜 2)]
    (hdim : Module.finrank k ↥(𝒜 2) + 1 = Module.finrank k ↥(𝒜 1)) :
    ∃ a ∈ 𝒜 1, ∃ b ∈ 𝒜 1, ∀ x ∈ 𝒜 2, ∃ c : k, x = c • (a * b)
```

### `SetLike.GradedMonoid.listProd_ne_zero_of_linearIndependent_of_kunneth_injective`

`Thm_SetLike_GradedMonoid_listProd_ne_zero_of_linearIndependent_of_kunneth_injective` — Products of independent degree-one elements are non-zero

```lean
theorem SetLike.GradedMonoid.listProd_ne_zero_of_linearIndependent_of_kunneth_injective
    {k : Type u} [Field k] {H : Type u} [Ring H] [Algebra k H] [Nontrivial H]
    {H' : Type u} [Ring H'] [Algebra k H']
    (𝒜 : ℕ → Submodule k H) [SetLike.GradedMonoid 𝒜] (p₁ p₂ m : H →ₐ[k] H')
    (hK : Function.Injective (DirectSum.toModule k (ℕ × ℕ) H' fun ab : ℕ × ℕ =>
      LinearMap.mul' k H' ∘ₗ
        TensorProduct.map (p₁.toLinearMap ∘ₗ (𝒜 ab.1).subtype) (p₂.toLinearMap ∘ₗ (𝒜 ab.2).subtype)))
    (hanti : ∀ x ∈ 𝒜 1, ∀ y ∈ 𝒜 1, p₂ x * p₁ y = -(p₁ y * p₂ x))
    (hm : ∀ x ∈ 𝒜 1, m x = p₁ x + p₂ x)
    {n : ℕ} (x : Fin n → H) (hx : ∀ i, x i ∈ 𝒜 1) (hli : LinearIndependent k x) :
    (List.ofFn x).prod ≠ 0
```

### `SetLike.GradedMonoid.rank_le_of_eq_bot_of_kunneth_injective`

`Thm_SetLike_GradedMonoid_rank_le_of_eq_bot_of_kunneth_injective` — Degree-one rank bound from an injective Künneth map

```lean
theorem SetLike.GradedMonoid.rank_le_of_eq_bot_of_kunneth_injective
    {k : Type u} [Field k] {H : Type u} [Ring H] [Algebra k H]
    {H' : Type u} [Ring H'] [Algebra k H']
    (𝒜 : ℕ → Submodule k H) [SetLike.GradedMonoid 𝒜] (p₁ p₂ m : H →ₐ[k] H')
    (hK : Function.Injective (DirectSum.toModule k (ℕ × ℕ) H' fun ab : ℕ × ℕ =>
      LinearMap.mul' k H' ∘ₗ
        TensorProduct.map (p₁.toLinearMap ∘ₗ (𝒜 ab.1).subtype) (p₂.toLinearMap ∘ₗ (𝒜 ab.2).subtype)))
    (hanti : ∀ x ∈ 𝒜 1, ∀ y ∈ 𝒜 1, p₂ x * p₁ y = -(p₁ y * p₂ x))
    (hm : ∀ x ∈ 𝒜 1, m x = p₁ x + p₂ x)
    {d : ℕ} (hd : 𝒜 (d + 1) = ⊥) :
    Module.rank k ↥(𝒜 1) ≤ d
```

## AdicCompletion (3)

### `AdicCompletion.bijective_of_forall_val_apply_eq_mk_apply`

`Thm_AdicCompletion_bijective_of_forall_val_apply_eq_mk_apply` — Adic completion of a Hom module between finite modules

```lean
theorem AdicCompletion.bijective_of_forall_val_apply_eq_mk_apply
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Finite A M] [Module.Finite A N]
    (θ : AdicCompletion I (M →ₗ[A] N) →ₗ[A] (M →ₗ[A] AdicCompletion I N))
    (hθ : ∀ (x : AdicCompletion I (M →ₗ[A] N)) (n : ℕ) (g : M →ₗ[A] N),
      Submodule.Quotient.mk g = x.val n →
        ∀ m : M, (θ x m).val n = Submodule.Quotient.mk (g m)) :
    Function.Bijective θ
```

### `AdicCompletion.exists_linearMap_forall_val_apply_eq_mk_apply`

`Thm_AdicCompletion_exists_linearMap_forall_val_apply_eq_mk_apply` — A comparison map widehatHom_A(M,N)toHom_A(M,widehat N)

```lean
theorem AdicCompletion.exists_linearMap_forall_val_apply_eq_mk_apply
    {A : Type u} [CommRing A] (I : Ideal A)
    (M N : Type u) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] :
    ∃ θ : AdicCompletion I (M →ₗ[A] N) →ₗ[A] (M →ₗ[A] AdicCompletion I N),
      ∀ (x : AdicCompletion I (M →ₗ[A] N)) (n : ℕ) (g : M →ₗ[A] N),
        Submodule.Quotient.mk g = x.val n →
          ∀ m : M, (θ x m).val n = Submodule.Quotient.mk (g m)
```

### `AdicCompletion.map_ker_subtype_injective_and_range_eq_ker_map`

`Thm_AdicCompletion_map_ker_subtype_injective_and_range_eq_ker_map` — Exactness of I-adic completion on kernels of maps of finite modules

```lean
theorem AdicCompletion.map_ker_subtype_injective_and_range_eq_ker_map
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    {M N : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] (ρ : M →ₗ[R] N) :
    Function.Injective (AdicCompletion.map I (LinearMap.ker ρ).subtype) ∧
      LinearMap.range (AdicCompletion.map I (LinearMap.ker ρ).subtype) =
        LinearMap.ker (AdicCompletion.map I ρ)
```

## CochainCx (3)

### `CochainCx.Bounded.exists_contractible_levelwise_equiv_prod`

`Thm_CochainCx_Bounded_exists_contractible_levelwise_equiv_prod` — Levelwise splitting of a bounded complex over a field

```lean
theorem CochainCx.Bounded.exists_contractible_levelwise_equiv_prod
    {k : Type u} [Field k] (C : CochainCx.Bounded k) :
    ∃ (E : CochainCx.Bounded k) (σ : ∀ p : ℕ, E.X (p + 1) →ₗ[k] E.X p)
      (_ : ∀ x : E.X 0, σ 0 (E.d 0 x) = x)
      (_ : ∀ (p : ℕ) (x : E.X (p + 1)), σ (p + 1) (E.d (p + 1) x) + E.d p (σ p x) = x)
      (e : ∀ p : ℕ, C.X p ≃ₗ[k] (C.H p × E.X p)),
      ∀ (p : ℕ) (x : C.X p), e (p + 1) (C.d p x) = (0, E.d p (e p x).2)
```

### `CochainCx.Bounded.exists_kunneth_toModule_HTot_tensor_injective`

`Thm_CochainCx_Bounded_exists_kunneth_toModule_HTot_tensor_injective` — Injective Künneth map into total cohomology over a field

```lean
theorem CochainCx.Bounded.exists_kunneth_toModule_HTot_tensor_injective
    {k : Type u} [Field k] (C D : CochainCx.Bounded k) (n : ℕ) :
    ∃ κ : ∀ i : DoubleComplex.Diag n, (C.H i.1.1 ⊗[k] D.H i.1.2) →ₗ[k] DoubleComplex.HTot (C.tensor D) n,
      (∀ (i : DoubleComplex.Diag n) (x : ↥(LinearMap.ker (C.d i.1.1))) (y : ↥(LinearMap.ker (D.d i.1.2))),
        ∃ hz : (Pi.single i (x.1 ⊗ₜ[k] y.1 : (C.tensor D).C i.1.1 i.1.2) : DoubleComplex.Tot (C.tensor D) n) ∈
            LinearMap.ker (DoubleComplex.dTot (C.tensor D) n),
          κ i (Submodule.Quotient.mk x ⊗ₜ[k] Submodule.Quotient.mk y) = Submodule.Quotient.mk ⟨_, hz⟩) ∧
      Function.Injective (DirectSum.toModule k (DoubleComplex.Diag n) (DoubleComplex.HTot (C.tensor D) n) κ)
```

### `CochainCx.Bounded.finrank_HTot_tensor_eq_sum_mul`

`Thm_CochainCx_Bounded_finrank_HTot_tensor_eq_sum_mul` — Künneth dimension formula over a field for bounded cochain complexes

```lean
theorem CochainCx.Bounded.finrank_HTot_tensor_eq_sum_mul
    {k : Type u} [Field k] (C D : CochainCx.Bounded k)
    (hC : ∀ p, Module.Finite k (C.H p)) (hD : ∀ q, Module.Finite k (D.H q)) (n : ℕ) :
    Module.Finite k (DoubleComplex.HTot (C.tensor D) n) ∧
      Module.finrank k (DoubleComplex.HTot (C.tensor D) n) =
        ∑ i ∈ Finset.range (n + 1), C.hfinrank i * D.hfinrank (n - i)
```

## Fin (3)

### `Fin.exists_chain_append`

`Thm_Fin_exists_chain_append` — Concatenation of finite S-chains

```lean
theorem Fin.exists_chain_append {α : Type*} (S : α → α → Prop) {a b c : α}
    (h₁ : ∃ (n : ℕ) (f : Fin (n + 1) → α), f 0 = a ∧ f (Fin.last n) = b ∧
      ∀ i : Fin n, S (f i.castSucc) (f i.succ))
    (h₂ : ∃ (n : ℕ) (f : Fin (n + 1) → α), f 0 = b ∧ f (Fin.last n) = c ∧
      ∀ i : Fin n, S (f i.castSucc) (f i.succ)) :
    ∃ (n : ℕ) (f : Fin (n + 1) → α), f 0 = a ∧ f (Fin.last n) = c ∧
      ∀ i : Fin n, S (f i.castSucc) (f i.succ)
```

### `Fin.exists_forall_sub_sub_modEq_of_forall_flow_sum_mul_modEq_zero`

`Thm_Fin_exists_forall_sub_sub_modEq_of_forall_flow_sum_mul_modEq_zero` — Edge functions pairing to zero with all flows are coboundaries mod q

```lean
theorem Fin.exists_forall_sub_sub_modEq_of_forall_flow_sum_mul_modEq_zero
    (n m : ℕ) (src tgt : Fin m → Fin n) (q : ℤ) (τ : Fin m → ℤ)
    (hτ : ∀ ε : Fin m → ℤ,
      (∀ i : Fin n, (∑ e, if src e = i then ε e else 0) = (∑ e, if tgt e = i then ε e else 0)) →
      (∑ e, ε e * τ e) ≡ 0 [ZMOD q]) :
    ∃ φ : Fin n → ℤ, ∀ e : Fin m, τ e ≡ φ (tgt e) - φ (src e) [ZMOD q]
```

### `Fin.exists_forall_vertexLaw_and_edgeLaw_pow_of_pow_add_of_modEq_of_forall_flow_sum_mul_eq`

`Thm_Fin_exists_forall_vertexLaw_and_edgeLaw_pow_of_pow_add_of_modEq_of_forall_flow_sum_mul_eq` — Uniform ℓ-power bound for integral tropical principality

```lean
theorem Fin.exists_forall_vertexLaw_and_edgeLaw_pow_of_pow_add_of_modEq_of_forall_flow_sum_mul_eq
    (n m : ℕ) (src tgt : Fin m → Fin n) (w : Fin m → ℕ) (hw : ∀ e, 0 < w e) (ℓ : ℕ) (hℓ : 1 < ℓ) :
    ∃ N : ℕ, ∀ (k : ℕ) (d : Fin n → ℤ) (M τ : Fin m → ℤ) (φ : Fin n → ℤ) (σ' : Fin m → ℤ),
      (∀ e : Fin m, τ e ≡ φ (tgt e) - φ (src e) [ZMOD ((ℓ : ℤ) ^ (k + N))]) →
      (∀ i : Fin n, (ℓ : ℤ) ^ (k + N) * d i + (∑ e, if src e = i then σ' e else 0) +
          (∑ e, if tgt e = i then (ℓ : ℤ) ^ (k + N) * M e - σ' e else 0) = 0) →
      (∀ ε : Fin m → ℤ,
        (∀ i : Fin n, (∑ e, if src e = i then ε e else 0) = (∑ e, if tgt e = i then ε e else 0)) →
        (∑ e, ε e * ((ℓ : ℤ) ^ (k + N) * τ e)) =
          ∑ e, ε e * ((ℓ : ℤ) ^ (k + N) * (w e : ℤ) * ((ℓ : ℤ) ^ (k + N) * M e - σ' e))) →
      ∃ (σ : Fin m → ℤ) (α : Fin n → ℤ),
        (∀ i : Fin n, (ℓ : ℤ) ^ N * d i + (∑ e, if src e = i then σ e else 0) +
            (∑ e, if tgt e = i then (ℓ : ℤ) ^ N * M e - σ e else 0) = 0) ∧
        (∀ e : Fin m, α (src e) + (ℓ : ℤ) ^ N * τ e =
            α (tgt e) + (ℓ : ℤ) ^ (k + N) * (w e : ℤ) * ((ℓ : ℤ) ^ N * M e - σ e))
```

## IsAddCyclic (3)

### `IsAddCyclic.ncard_setOf_nsmul_eq_zero_and_ne_zero_of_prime_dvd_card`

`Thm_IsAddCyclic_ncard_setOf_nsmul_eq_zero_and_ne_zero_of_prime_dvd_card` — Non-zero ℓ-torsion in a cyclic group has ℓ-1 elements

```lean
theorem IsAddCyclic.ncard_setOf_nsmul_eq_zero_and_ne_zero_of_prime_dvd_card
    (D : Type) [AddCommGroup D] [IsAddCyclic D] (m : ℕ) (hm : Nat.card D = m) (hm0 : m ≠ 0)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓm : ℓ ∣ m) :
    {x : D | ℓ • x = 0 ∧ x ≠ 0}.ncard = ℓ - 1
```

### `IsAddCyclic.of_card_torsion_le_of_exponent_dvd_pow`

`Thm_IsAddCyclic_of_card_torsion_le_of_exponent_dvd_pow` — Finite abelian p-group with socle of order ≤ p is cyclic

```lean
theorem IsAddCyclic.of_card_torsion_le_of_exponent_dvd_pow
    {G : Type*} [AddCommGroup G] [Finite G] {p : ℕ} (hp : p.Prime) (m : ℕ)
    (hexp : ∀ x : G, p ^ m • x = 0)
    (hsocle : Nat.card {x : G // p • x = 0} ≤ p) :
    IsAddCyclic G ∧ Nat.card G ∣ p ^ m
```

### `IsAddCyclic.of_squarefree_natCard`

`Thm_IsAddCyclic_of_squarefree_natCard` — Abelian groups of squarefree order are cyclic

```lean
theorem IsAddCyclic.of_squarefree_natCard
    {A : Type*} [AddCommGroup A] (hA : Squarefree (Nat.card A)) : IsAddCyclic A
```

## IsIntegrallyClosed (3)

### `IsIntegrallyClosed.height_eq_one_of_mem_associatedPrimes`

`Thm_IsIntegrallyClosed_height_eq_one_of_mem_associatedPrimes` — Associated primes of a nonzero principal ideal have height one

```lean
theorem IsIntegrallyClosed.height_eq_one_of_mem_associatedPrimes
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    {x : B} (hx : x ≠ 0) (P : Ideal B) [P.IsPrime]
    (hP : P ∈ associatedPrimes B (B ⧸ Ideal.span {x})) : P.height = 1
```

### `IsIntegrallyClosed.isDiscreteValuationRing_localization_of_mem_associatedPrimes`

`Thm_IsIntegrallyClosed_isDiscreteValuationRing_localization_of_mem_associatedPrimes` — Associated primes of a principal ideal give discrete valuation rings

```lean
theorem IsIntegrallyClosed.isDiscreteValuationRing_localization_of_mem_associatedPrimes
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    {x : B} (hx : x ≠ 0) (P : Ideal B) [P.IsPrime]
    (hP : P ∈ associatedPrimes B (B ⧸ Ideal.span {x})) :
    IsDiscreteValuationRing (Localization.AtPrime P)
```

### `IsIntegrallyClosed.isDiscreteValuationRing_of_maximalIdeal_mem_associatedPrimes`

`Thm_IsIntegrallyClosed_isDiscreteValuationRing_of_maximalIdeal_mem_associatedPrimes` — Normal Noetherian local domain with depth one is a DVR

```lean
theorem IsIntegrallyClosed.isDiscreteValuationRing_of_maximalIdeal_mem_associatedPrimes
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B] [IsLocalRing B]
    {x : B} (hx : x ≠ 0)
    (h : IsLocalRing.maximalIdeal B ∈ associatedPrimes B (B ⧸ Ideal.span {x})) :
    IsDiscreteValuationRing B
```

## IsLocallyConstant (3)

### `IsLocallyConstant.exists_isOpen_one_mem_forall_mul_eq_of_hasCompactSupport`

`Thm_IsLocallyConstant_exists_isOpen_one_mem_forall_mul_eq_of_hasCompactSupport` — Uniform local constancy of compactly supported locally constant functions

```lean
theorem IsLocallyConstant.exists_isOpen_one_mem_forall_mul_eq_of_hasCompactSupport
    {G M : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Zero M]
    (Φ : G → M) (hlc : IsLocallyConstant Φ) (hcs : HasCompactSupport Φ) :
    ∃ W : Set G, IsOpen W ∧ (1 : G) ∈ W ∧
      ∀ g : G, ∀ w ∈ W, Φ (g * w) = Φ g ∧ Φ (w * g) = Φ g
```

### `IsLocallyConstant.exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport`

`Thm_IsLocallyConstant_exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport` — Uniform two-sided invariance of compactly supported locally constant functions

```lean
theorem IsLocallyConstant.exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Y : Type*} [Zero Y]
    {f : G → Y} (hf : IsLocallyConstant f) (hsupp : HasCompactSupport f) :
    ∃ V ∈ nhds (1 : G), ∀ u ∈ V, ∀ u' ∈ V, ∀ g : G, f (u * g * u') = f g
```

### `IsLocallyConstant.isLocallyConstant_fun_mul_apply_mul_of_hasCompactSupport`

`Thm_IsLocallyConstant_isLocallyConstant_fun_mul_apply_mul_of_hasCompactSupport` — Two-sided slice families of compactly supported locally constant functions

```lean
theorem IsLocallyConstant.isLocallyConstant_fun_mul_apply_mul_of_hasCompactSupport
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Y : Type*} [Zero Y]
    {f : G → Y} (hf : IsLocallyConstant f) (hsupp : HasCompactSupport f) {S : Type*} (n : S → G) :
    IsLocallyConstant (fun kk : G × G => fun s => f (kk.1 * n s * kk.2))
```

## Manifold (3)

### `Manifold.exists_forall_eventuallyEq_const_of_meromorphicOrderAt_nonneg`

`Thm_Manifold_exists_forall_eventuallyEq_const_of_meromorphicOrderAt_nonneg` — Liouville's theorem on a compact Riemann surface

```lean
theorem Manifold.exists_forall_eventuallyEq_const_of_meromorphicOrderAt_nonneg
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) ω M]
    [CompactSpace M] [ConnectedSpace M]
    (g : M → ℂ)
    (hg : ∀ x : M, MeromorphicAt (fun z : ℂ => g ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
      (extChartAt 𝓘(ℂ, ℂ) x x))
    (hg0 : ∀ x : M, 0 ≤ meromorphicOrderAt (fun z : ℂ => g ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
      (extChartAt 𝓘(ℂ, ℂ) x x)) :
    ∃ C : ℂ, ∀ x : M, (fun z : ℂ => g ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
      =ᶠ[𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x)] fun _ => C
```

### `Manifold.exists_ne_zero_and_sum_mul_eventuallyEq_zero_of_degree_lt_card`

`Thm_Manifold_exists_ne_zero_and_sum_mul_eventuallyEq_zero_of_degree_lt_card` — Chartwise bound dim L(D)≤ deg D+1 on a compact Riemann surface

```lean
theorem Manifold.exists_ne_zero_and_sum_mul_eventuallyEq_zero_of_degree_lt_card
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) ω M]
    [CompactSpace M] [ConnectedSpace M]
    (D : M →₀ ℕ) {ι : Type*} [Fintype ι] (ψ : ι → M → ℂ)
    (hψ : ∀ i x, MeromorphicAt (fun z : ℂ => ψ i ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
      (extChartAt 𝓘(ℂ, ℂ) x x))
    (hord : ∀ i x, ((-(D x : ℤ) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (fun z : ℂ => ψ i ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) (extChartAt 𝓘(ℂ, ℂ) x x))
    (hcard : (D.sum fun _ n => n) + 1 < Fintype.card ι) :
    ∃ c : ι → ℂ, c ≠ 0 ∧ ∀ x : M, (fun z : ℂ => ∑ i, c i * ψ i ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
      =ᶠ[𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x)] 0
```

### `Manifold.forall_eq_zero_or_forall_eventually_ne_zero_of_analyticAt_extChartAt_of_isConnected`

`Thm_Manifold_forall_eq_zero_or_forall_eventually_ne_zero_of_analyticAt_extChartAt_of_isConnected` — Identity principle for chartwise analytic functions on a connected set

```lean
theorem Manifold.forall_eq_zero_or_forall_eventually_ne_zero_of_analyticAt_extChartAt_of_isConnected
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) ω M] [T2Space M]
    {W : Set M} (hW : IsOpen W) (hWc : IsConnected W) (g : M → ℂ)
    (hg : ∀ x ∈ W, AnalyticAt ℂ (fun z : ℂ => g ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) (extChartAt 𝓘(ℂ, ℂ) x x)) :
    (∀ x ∈ W, g x = 0) ∨ (∀ x ∈ W, ∀ᶠ y in 𝓝[≠] x, g y ≠ 0)
```

## ModularCurve (3)

### `ModularCurve.SerreImage.contains_SL2`

`Thm_ModularCurve_SerreImage_contains_SL2` — Irreducible subgroups with a unipotent element contain SL₂(𝔽ₚ)

```lean
theorem ModularCurve.SerreImage.contains_SL2 {p : ℕ} [Fact p.Prime]
    (H : Subgroup (GL (Fin 2) (ZMod p)))
    (hirr : ∀ v : Fin 2 → ZMod p, v ≠ 0 → ∃ g ∈ H, ∀ c : ZMod p,
      ((g : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)).mulVec v ≠ c • v)
    (hunip : ∃ u ∈ H, ((u : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1) ^ 2 = 0 ∧ u ≠ 1) :
    (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := ZMod p)).range ≤ H
```

### `ModularCurve.closure_elemSet_eq_top`

`Thm_ModularCurve_closure_elemSet_eq_top` — Transvections generate SL₂(ℤ/Nℤ)

```lean
theorem ModularCurve.closure_elemSet_eq_top (N : ℕ) [NeZero N] :
    Subgroup.closure (ModularCurve.elemSet (ZMod N)) = ⊤
```

### `ModularCurve.surjective_specialLinearGroup_map_zmod`

`Thm_ModularCurve_surjective_specialLinearGroup_map_zmod` — Surjectivity of reduction SL₂(ℤ)toSL₂(ℤ/N)

```lean
theorem ModularCurve.surjective_specialLinearGroup_map_zmod (N : ℕ) [NeZero N] :
    Function.Surjective
      (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N)))
```

## QuadraticForm (3)

### `QuadraticForm.exists_ternary_isotropic_mul_of_exists_of_exists`

`Thm_QuadraticForm_exists_ternary_isotropic_mul_of_exists_of_exists` — Multiplicativity of isotropy for z²-tx²-uy²

```lean
theorem QuadraticForm.exists_ternary_isotropic_mul_of_exists_of_exists
    (K : Type) [Field K] (t u u' : K)
    (h : ∃ z x y : K, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - t * x ^ 2 - u * y ^ 2 = 0)
    (h' : ∃ z x y : K, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - t * x ^ 2 - u' * y ^ 2 = 0) :
    ∃ z x y : K, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - t * x ^ 2 - (u * u') * y ^ 2 = 0
```

### `QuadraticForm.forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero`

`Thm_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero` — Isotropic ternary form -ax²-by²+abz² is universal

```lean
theorem QuadraticForm.forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero
    (F : Type) [Field F] [CharZero F] (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hiso : ∃ x y z : F, ¬ (x = 0 ∧ y = 0 ∧ z = 0) ∧ -a * x ^ 2 - b * y ^ 2 + a * b * z ^ 2 = 0)
    (c : F) :
    ∃ x y z : F, -a * x ^ 2 - b * y ^ 2 + a * b * z ^ 2 = c
```

### `QuadraticForm.forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero`

`Thm_QuadraticForm_forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero` — Anisotropy of a quaternary norm form versus its ternary subform

```lean
theorem QuadraticForm.forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero
    (K : Type) [Field K] (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∀ x₀ x₁ x₂ x₃ : K, x₀ ^ 2 - a * x₁ ^ 2 - b * x₂ ^ 2 + a * b * x₃ ^ 2 = 0 →
        x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0) ↔
      ∀ z x y : K, z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0 → z = 0 ∧ x = 0 ∧ y = 0
```

## QuotSMulTop (3)

### `QuotSMulTop.exists_basis_lift`

`Thm_QuotSMulTop_exists_basis_lift` — Bases lift along a regular element of the maximal ideal

```lean
theorem QuotSMulTop.exists_basis_lift {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M] (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular M x) {ι : Type*} [Fintype ι] (b : Module.Basis ι (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) :
    ∃ b' : Module.Basis ι R M,
      ∀ i, (Submodule.Quotient.mk (b' i) : QuotSMulTop x M) = b i
```

### `QuotSMulTop.linearIndependent_of_quotientMk_linearIndependent`

`Thm_QuotSMulTop_linearIndependent_of_quotientMk_linearIndependent` — Lifting linear independence across M → M/xM for regular x

```lean
theorem QuotSMulTop.linearIndependent_of_quotientMk_linearIndependent {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [IsLocalRing R] [IsNoetherianRing R] (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular M x) {ι : Type*} [Fintype ι] (m : ι → M) (hli : LinearIndependent (R ⧸ Ideal.span {x}) (fun i => (Submodule.Quotient.mk (m i) : QuotSMulTop x M))) :
    LinearIndependent R m
```

### `QuotSMulTop.span_eq_top_of_span_quotientMk_eq_top`

`Thm_QuotSMulTop_span_eq_top_of_span_quotientMk_eq_top` — Nakayama lifting of generators along M → M/xM

```lean
theorem QuotSMulTop.span_eq_top_of_span_quotientMk_eq_top {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [IsLocalRing R] [Module.Finite R M] (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) {ι : Type*} (m : ι → M) (hspan : Submodule.span (R ⧸ Ideal.span {x}) (Set.range fun i => (Submodule.Quotient.mk (m i) : QuotSMulTop x M)) = ⊤) :
    Submodule.span R (Set.range m) = ⊤
```

## TaylorWiles (3)

### `TaylorWiles.exists_isEigenIdempotent_of_isUnit`

`Thm_TaylorWiles_exists_isEigenIdempotent_of_isUnit` — Unit root separation yields an eigen-idempotent for a 2× 2 matrix

```lean
theorem TaylorWiles.exists_isEigenIdempotent_of_isUnit {A : Type u} [CommRing A] {M : Matrix (Fin 2) (Fin 2) A} {a b : A}
    (htr : M.trace = a + b) (hdet : M.det = a * b) (hu : IsUnit (a - b)) :
    ∃ e, TaylorWiles.IsEigenIdempotent M a b e
```

### `TaylorWiles.isEigenIdempotent_smul_sub`

`Thm_TaylorWiles_isEigenIdempotent_smul_sub` — The idempotent v(M-b) for a split 2× 2 matrix

```lean
theorem TaylorWiles.isEigenIdempotent_smul_sub {A : Type u} [CommRing A] {M : Matrix (Fin 2) (Fin 2) A} {a b v : A}
    (htr : M.trace = a + b) (hdet : M.det = a * b) (hv : v * (a - b) = 1) :
    TaylorWiles.IsEigenIdempotent M a b (v • (M - b • (1 : Matrix (Fin 2) (Fin 2) A)))
```

### `TaylorWiles.tameDescentChar_comp_eq`

`Thm_TaylorWiles_tameDescentChar_comp_eq` — Descended character satisfies ξ(π g)=χ(g)

```lean
theorem TaylorWiles.tameDescentChar_comp_eq {G : Type u} {Δ : Type v} {A : Type w} [Group G] [Group Δ] [CommRing A]
    (π : G →* Δ) (hπ : Function.Surjective π) (χ : G →* Aˣ)
    (hχ : ∀ g ∈ π.ker, χ g = 1) (g : G) :
    TaylorWiles.tameDescentChar π hπ χ hχ (π g) = χ g
```

## exists (3)

### `exists_completeOrthogonalIdempotents_mul_eq_pow_mul_of_pow_eq_one_of_forall_isUnit_one_sub_pow`

`Thm_exists_completeOrthogonalIdempotents_mul_eq_pow_mul_of_pow_eq_one_of_forall_isUnit_one_sub_pow` — Lagrange idempotents for a root of unity over a commutative ring

```lean
theorem exists_completeOrthogonalIdempotents_mul_eq_pow_mul_of_pow_eq_one_of_forall_isUnit_one_sub_pow
    (R : Type u) [CommRing R] (N : ℕ) (hd : IsUnit ((N + 1 : ℕ) : R))
    (ζ : R) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (ω : R) (hω : ω ^ (N + 1) = 1) :
    ∃ e : Fin (N + 1) → R, CompleteOrthogonalIdempotents e ∧ ∀ k : Fin (N + 1), ω * e k = ζ ^ (k : ℕ) * e k
```

### `exists_contDiff_even_sub_comp_neg_eq_two_mul_smul`

`Thm_exists_contDiff_even_sub_comp_neg_eq_two_mul_smul` — Smooth even Hadamard factorisation of the odd part

```lean
theorem exists_contDiff_even_sub_comp_neg_eq_two_mul_smul
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (B : E × ℝ → F) (hB : ContDiff ℝ (⊤ : ℕ∞) B) :
    ∃ Q : E × ℝ → F, ContDiff ℝ (⊤ : ℕ∞) Q ∧ (∀ (e : E) (ρ : ℝ), Q (e, -ρ) = Q (e, ρ)) ∧
      ∀ (e : E) (ρ : ℝ), B (e, ρ) - B (e, -ρ) = (2 * ρ) • Q (e, ρ)
```

### `exists_polynomial_eq_on_arithProg`

`Thm_exists_polynomial_eq_on_arithProg` — Integer-valued sequences near polynomial branches are polynomial on progressions

```lean
theorem exists_polynomial_eq_on_arithProg {n w L m₀ D : ℕ} (hD : 0 < D) (μ : ℂ) (P : Fin n → Polynomial ℂ) (hP : ∀ i, (P i).natDegree ≤ w) (x : ℕ → ℚ) (hint : ∀ m, m₀ ≤ m → ∃ z : ℤ, (D : ℚ) * x m = z) (hnear : ∀ m, m₀ ≤ m → ∃ i, ‖(x m : ℂ) - (P i).eval (μ * m)‖ < 1 / ((D : ℝ) * 2 ^ (w + 1))) : ∃ a b : ℕ, 0 < a ∧ m₀ ≤ b ∧ ∃ G : Polynomial ℚ, G.natDegree ≤ w ∧ ∀ j < L, x (b + a * j) = G.eval (j : ℚ)
```

## CharacterModule (2)

### `CharacterModule.natCard_eq_of_finite`

`Thm_CharacterModule_natCard_eq_of_finite` — Character group of a finite abelian group has the same order

```lean
theorem CharacterModule.natCard_eq_of_finite (M : Type*) [AddCommGroup M] [Finite M] :
    Nat.card (CharacterModule M) = Nat.card M
```

### `CharacterModule.natCard_quotient_ideal_smul_top_eq_natCard_torsionBySet`

`Thm_CharacterModule_natCard_quotient_ideal_smul_top_eq_natCard_torsionBySet` — Character counting: #(G^∨/bG^∨)=#G[b] for finitely generated b

```lean
theorem CharacterModule.natCard_quotient_ideal_smul_top_eq_natCard_torsionBySet
    (A : Type*) [CommRing A] (G : Type*) [AddCommGroup G] [Module A G]
    (s : Set A) (hs : s.Finite) (hfin : Finite ↥(Submodule.torsionBySet A G s)) :
    Nat.card (CharacterModule G ⧸ (Ideal.span s • (⊤ : Submodule A (CharacterModule G))))
      = Nat.card ↥(Submodule.torsionBySet A G s)
```

## CommGroup (2)

### `CommGroup.exists_forall_monoidHom_exists_apply_eq_mul_inv_mul_inv_of_symm_of_cocycle`

`Thm_CommGroup_exists_forall_monoidHom_exists_apply_eq_mul_inv_mul_inv_of_symm_of_cocycle` — Symmetric cocycles on a finite abelian group split after adjoining roots

```lean
theorem CommGroup.exists_forall_monoidHom_exists_apply_eq_mul_inv_mul_inv_of_symm_of_cocycle
    {K : Type u} [AddCommGroup K] [Finite K] {A : Type v} [CommGroup A] (c : K → K → A)
    (hsymm : ∀ k k', c k k' = c k' k) (hcoc : ∀ k k' k'', c k k' * c (k + k') k'' = c k' k'' * c k (k' + k'')) :
    ∃ (m : ℕ) (a : Fin m → A) (n : Fin m → ℕ), (∀ i, 0 < n i ∧ n i ∣ Nat.card K) ∧
      ∀ (A' : Type v) [CommGroup A'] (φ : A →* A'), (∀ i, ∃ α : A', α ^ (n i) = φ (a i)) →
        ∃ b : K → A', ∀ k k', φ (c k k') = b (k + k') * (b k)⁻¹ * (b k')⁻¹
```

### `CommGroup.index_range_powMonoidHom_eq_pow_finrank`

`Thm_CommGroup_index_range_powMonoidHom_eq_pow_finrank` — Index of n-th powers in a finitely generated torsion-free abelian group

```lean
theorem CommGroup.index_range_powMonoidHom_eq_pow_finrank {F : Type*} [CommGroup F] [Group.FG F]
    (htf : ∀ (x : F) (m : ℕ), 0 < m → x ^ m = 1 → x = 1) {n : ℕ} (hn : 0 < n) :
    (powMonoidHom n : F →* F).range.index = n ^ Module.finrank ℤ (Additive F)
```

## ContinuousMap (2)

### `ContinuousMap.ae_eq_zero_of_forall_mem_starSubalgebra_integral_mul_eq_zero`

`Thm_ContinuousMap_ae_eq_zero_of_forall_mem_starSubalgebra_integral_mul_eq_zero` — Vanishing a.e. against a point-separating star subalgebra

```lean
theorem ContinuousMap.ae_eq_zero_of_forall_mem_starSubalgebra_integral_mul_eq_zero
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (A : StarSubalgebra ℂ C(X, ℂ)) (hA : A.SeparatesPoints)
    (β : C(X, ℂ))
    (h : ∀ f ∈ A, ∫ x, f x * β x ∂μ = 0) :
    (β : X → ℂ) =ᵐ[μ] 0
```

### `ContinuousMap.exists_continuous_monoidHom_forall_sum_eq_zero_of_compactSpace`

`Thm_ContinuousMap_exists_continuous_monoidHom_forall_sum_eq_zero_of_compactSpace` — Characters inherit translation relations of a nonzero continuous function

```lean
theorem ContinuousMap.exists_continuous_monoidHom_forall_sum_eq_zero_of_compactSpace
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (f : C(G, ℂ)) (hf : f ≠ 0) (R : Set (G →₀ ℂ))
    (hR : ∀ r ∈ R, ∀ x : G, (r.sum fun g c => c * f (x * g)) = 0) :
    ∃ χ : G →* ℂˣ, Continuous χ ∧ ∀ r ∈ R, (r.sum fun g c => c * ((χ g : ℂˣ) : ℂ)) = 0
```

## Finite (2)

### `Finite.exists_isUnit_prod_pow_apply_eq_of_isReduced_of_prime`

`Thm_Finite_exists_isUnit_prod_pow_apply_eq_of_isReduced_of_prime` — Norm surjectivity for prime-order automorphisms of finite reduced rings

```lean
theorem Finite.exists_isUnit_prod_pow_apply_eq_of_isReduced_of_prime
    {R : Type*} [CommRing R] [Finite R] [IsReduced R]
    (τ : R ≃+* R) (ℓ : ℕ) (hℓ : ℓ.Prime) (hτℓ : τ ^ ℓ = 1)
    (hmax : ∀ m : Ideal R, m.IsMaximal → (∀ x ∈ m, τ x ∈ m) → ∃ x, τ x - x ∉ m)
    (c : R) (hc : IsUnit c) (hτc : τ c = c) :
    ∃ u : R, IsUnit u ∧ ∏ i ∈ Finset.range ℓ, (τ ^ i) u = c
```

### `Finite.exists_sum_pow_apply_eq_of_isReduced_of_prime`

`Thm_Finite_exists_sum_pow_apply_eq_of_isReduced_of_prime` — Surjectivity of the trace of a prime-order ring automorphism

```lean
theorem Finite.exists_sum_pow_apply_eq_of_isReduced_of_prime
    {R : Type*} [CommRing R] [Finite R] [IsReduced R]
    (τ : R ≃+* R) (ℓ : ℕ) (hℓ : ℓ.Prime) (hτℓ : τ ^ ℓ = 1)
    (hmax : ∀ m : Ideal R, m.IsMaximal → (∀ x ∈ m, τ x ∈ m) → ∃ x, τ x - x ∉ m)
    (c : R) (hτc : τ c = c) :
    ∃ u : R, ∑ i ∈ Finset.range ℓ, (τ ^ i) u = c
```

## FiniteField (2)

### `FiniteField.exists_forall_affineMap_apply_ne_zero_of_forall_lt`

`Thm_FiniteField_exists_forall_affineMap_apply_ne_zero_of_forall_lt` — Row-by-row avoidance of affine conditions over a finite field

```lean
theorem FiniteField.exists_forall_affineMap_apply_ne_zero_of_forall_lt
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] {s : ℕ} {n : Fin s → ℕ}
    {ι : Fin s → Type*} [∀ i, Fintype (ι i)]
    {V : ∀ i, ι i → Type*} [∀ i j, AddCommGroup (V i j)] [∀ i j, Module 𝔽 (V i j)]
    (φ : ∀ i, (∀ i' : Fin s, Fin (n i') → 𝔽) → ∀ j : ι i, (Fin (n i) → 𝔽) →ᵃ[𝔽] V i j)
    (hdep : ∀ i (x x' : ∀ i' : Fin s, Fin (n i') → 𝔽), (∀ i', i' < i → x i' = x' i') → φ i x = φ i x')
    (hφ : ∀ i x j, ∃ y, φ i x j y ≠ 0)
    (hm : ∀ i, Fintype.card (ι i) < Fintype.card 𝔽) :
    ∃ x : ∀ i : Fin s, Fin (n i) → 𝔽, ∀ i j, φ i x j (x i) ≠ 0
```

### `FiniteField.exists_forall_affineMap_ne_zero`

`Thm_FiniteField_exists_forall_affineMap_ne_zero` — Fewer than q affine conditions on 𝔽ⁿ are simultaneously avoidable

```lean
theorem FiniteField.exists_forall_affineMap_ne_zero
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] {n : ℕ} {ι : Type*} [Fintype ι]
    {V : ι → Type*} [∀ j, AddCommGroup (V j)] [∀ j, Module 𝔽 (V j)]
    (φ : ∀ j, (Fin n → 𝔽) →ᵃ[𝔽] V j) (hφ : ∀ j, ∃ x, φ j x ≠ 0)
    (hm : Fintype.card ι < Fintype.card 𝔽) :
    ∃ x, ∀ j, φ j x ≠ 0
```

## Finset (2)

### `Finset.exists_mem_and_not_mem_and_isUnit_sub_mul_of_card_eq_of_prime`

`Thm_Finset_exists_mem_and_not_mem_and_isUnit_sub_mul_of_card_eq_of_prime` — A q-point subset of the box misses an invertible completion

```lean
theorem Finset.exists_mem_and_not_mem_and_isUnit_sub_mul_of_card_eq_of_prime
    (q : ℕ) [Fact q.Prime] (S : Finset (ℕ × ℕ)) (hS : S ⊆ Finset.range q ×ˢ Finset.range q)
    (hcard : S.card = q) :
    ∃ a b c d : ℕ, (a, b) ∈ S ∧ c < q ∧ d < q ∧ (c, d) ∉ S ∧
      IsUnit (((a * d : ℤ) - (b * c : ℤ) : ℤ) : ZMod q)
```

### `Finset.sum_neg_one_pow_mul_sum_strictMono_sum_ite_eq_sum`

`Thm_Finset_sum_neg_one_pow_mul_sum_strictMono_sum_ite_eq_sum` — Alternating sum over ordered chains recovers the total sum

```lean
theorem Finset.sum_neg_one_pow_mul_sum_strictMono_sum_ite_eq_sum
    {ι : Type u} [Fintype ι] [LinearOrder ι] {β : Type v} (T : Finset β) (a : β → ℤ)
    (mem : ι → β → Prop) (hcov : ∀ y ∈ T, ∃ i, mem i y) (N : ℕ) (hN : Fintype.card ι ≤ N) :
    ∑ p ∈ Finset.range N, (-1 : ℤ) ^ p *
        ∑ s : {s : Fin (p + 1) → ι // StrictMono s}, ∑ y ∈ T, (if ∀ j, mem (s.1 j) y then a y else 0) =
      ∑ y ∈ T, a y
```

## LinearEquiv (2)

### `LinearEquiv.exists_equiv_forall_dual_eq_comp_symm_and_comp_eq_of_dual_equiv_forall_comp_eq`

`Thm_LinearEquiv_exists_equiv_forall_dual_eq_comp_symm_and_comp_eq_of_dual_equiv_forall_comp_eq` — Equivariant dual isomorphism descends to the modules

```lean
theorem LinearEquiv.exists_equiv_forall_dual_eq_comp_symm_and_comp_eq_of_dual_equiv_forall_comp_eq
    (R : Type*) [CommRing R] (k : Type*) [CommRing k] [Algebra R k]
    (Ω : Type*) [AddCommGroup Ω] [Module R Ω] [Module.Finite R Ω] [Module.Free R Ω]
    (S : Type*) [AddCommGroup S] [Module R S] [Module.Finite R S] [Module.Free R S]
    {ι : Type*} (a : ι → (Ω →ₗ[R] Ω)) (s : ι → (S →ₗ[R] S))
    (τ : Module.Dual R Ω ≃ₗ[R] Module.Dual R S)
    (hτ : ∀ (t : ι) (D : Module.Dual R Ω), τ (D ∘ₗ a t) = (τ D) ∘ₗ s t) :
    ∃ θ : Ω ≃ₗ[R] S,
      (∀ D : Module.Dual R Ω, τ D = D ∘ₗ (θ.symm : S →ₗ[R] Ω)) ∧
      (∀ t : ι, (θ : Ω →ₗ[R] S) ∘ₗ a t = s t ∘ₗ (θ : Ω →ₗ[R] S)) ∧
      ∃ Ξ : k ⊗[R] Ω ≃ₗ[k] k ⊗[R] S,
        (∀ (c : k) (x : Ω), Ξ (c ⊗ₜ x) = c ⊗ₜ θ x) ∧
        ∀ t : ι, (Ξ : k ⊗[R] Ω →ₗ[k] k ⊗[R] S) ∘ₗ (a t).baseChange k =
          (s t).baseChange k ∘ₗ (Ξ : k ⊗[R] Ω →ₗ[k] k ⊗[R] S)
```

### `LinearEquiv.exists_forall_finrank_inf_map_pow_add_finrank_inf_le`

`Thm_LinearEquiv_exists_forall_finrank_inf_map_pow_add_finrank_inf_le` — Eventual dimension inequality for φ-stable subspace pairs

```lean
theorem LinearEquiv.exists_forall_finrank_inf_map_pow_add_finrank_inf_le
    {k : Type*} [Field k] {W : Type*} [AddCommGroup W] [Module k W]
    (φ : W ≃ₗ[k] W) (P B P' B' : Submodule k W) (hPB : P ≤ B) (hP'B' : P' ≤ B')
    (hP : P.map (φ : W →ₗ[k] W) ≤ P) (hB : B.map (φ : W →ₗ[k] W) ≤ B)
    (hP' : P'.map (φ.symm : W →ₗ[k] W) ≤ P') (hB' : B'.map (φ.symm : W →ₗ[k] W) ≤ B')
    (hfin : ∀ M : ℕ, FiniteDimensional k ↥(B ⊓ B'.map ((φ : W →ₗ[k] W) ^ M)))
    (hgen : ∃ M₁ : ℕ, B ≤ ⨆ j : ℕ,
      (B ⊓ B'.map ((φ : W →ₗ[k] W) ^ M₁)).map ((φ : W →ₗ[k] W) ^ j))
    (hgen' : ∃ M₁ : ℕ, B' ≤ ⨆ j : ℕ,
      (B' ⊓ B.map ((φ.symm : W →ₗ[k] W) ^ M₁)).map ((φ.symm : W →ₗ[k] W) ^ j))
    (htor : ∀ y ∈ B, ∃ c : Polynomial k, c.Monic ∧
      Polynomial.aeval (φ : W →ₗ[k] W) c y ∈ P)
    (htor' : ∀ y ∈ B', ∃ c : Polynomial k, c.Monic ∧
      Polynomial.aeval (φ.symm : W →ₗ[k] W) c y ∈ P') :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      Module.finrank k ↥(P ⊓ P'.map ((φ : W →ₗ[k] W) ^ M)) + Module.finrank k ↥(B ⊓ B') ≤
        Module.finrank k ↥(B ⊓ B'.map ((φ : W →ₗ[k] W) ^ M)) +
          Module.finrank k ↥(P ⊓ P')
```

## Multiset (2)

### `Multiset.esymm_map_sub_esymm_map_mem_pow_succ`

`Thm_Multiset_esymm_map_sub_esymm_map_mem_pow_succ` — Elementary symmetric functions modulo powers of an ideal

```lean
theorem Multiset.esymm_map_sub_esymm_map_mem_pow_succ
    (A : Type) [CommRing A] (I : Ideal A) (ι : Type) (s : Finset ι) (y z : ι → A)
    (hz : ∀ i ∈ s, z i ∈ I) (hyz : ∀ i ∈ s, y i - z i ∈ I ^ 2) (k : ℕ) :
    (s.val.map y).esymm k - (s.val.map z).esymm k ∈ I ^ (k + 1)
```

### `Multiset.filter_ne_zero_eq_of_forall_prod_one_sub_pow_eq`

`Thm_Multiset_filter_ne_zero_eq_of_forall_prod_one_sub_pow_eq` — Rigidity of the products prod(1-zⁿ)

```lean
theorem Multiset.filter_ne_zero_eq_of_forall_prod_one_sub_pow_eq
    (s t : Multiset ℂ) (c : ℝ) (hc : 1 < c) (ht : ∀ z ∈ t, ‖z‖ = c)
    (h : ∀ n : ℕ, 0 < n →
      (s.map fun z => 1 - z ^ n).prod = (t.map fun z => 1 - z ^ n).prod) :
    s.filter (fun z => z ≠ 0) = t
```

## TrivSqZeroExt (2)

### `TrivSqZeroExt.isArtinianRing_and_exists_linearMap_range_eq_ker_fstHom_dualNumber`

`Thm_TrivSqZeroExt_isArtinianRing_and_exists_linearMap_range_eq_ker_fstHom_dualNumber` — Dual numbers k[ε] as a small extension of k

```lean
theorem TrivSqZeroExt.isArtinianRing_and_exists_linearMap_range_eq_ker_fstHom_dualNumber
    (k : Type) [Field k] :
    letI : Algebra (DualNumber k) k := (TrivSqZeroExt.fstHom k k k).toRingHom.toAlgebra
    IsArtinianRing (DualNumber k) ∧
    Function.Surjective (algebraMap (DualNumber k) k) ∧
    IsNilpotent (RingHom.ker (algebraMap (DualNumber k) k)) ∧
    RingHom.ker (algebraMap (DualNumber k) k) * maximalIdeal (DualNumber k) = ⊥ ∧
    RingHom.ker (algebraMap (DualNumber k) k) ≤ maximalIdeal (DualNumber k) ∧
    (∃ ι : ResidueField (DualNumber k) →ₗ[DualNumber k] DualNumber k,
      Function.Injective ι ∧
      LinearMap.range ι = Submodule.restrictScalars (DualNumber k) (RingHom.ker (algebraMap (DualNumber k) k))) ∧
    Function.Bijective ((residue (DualNumber k)).comp (algebraMap k (DualNumber k))) ∧
    (IsAlgClosed k → IsAlgClosed (ResidueField (DualNumber k)))
```

### `TrivSqZeroExt.isLocalRing`

`Thm_TrivSqZeroExt_isLocalRing` — Trivial square-zero extensions of local rings are local

```lean
theorem TrivSqZeroExt.isLocalRing {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module Rᵐᵒᵖ M] [IsCentralScalar R M] [IsLocalRing R] : IsLocalRing (TrivSqZeroExt R M)
```

## VectorFourier (2)

### `VectorFourier.ae_eq_zero_of_integrable_of_forall_fourierIntegral_eq_zero`

`Thm_VectorFourier_ae_eq_zero_of_integrable_of_forall_fourierIntegral_eq_zero` — Injectivity of the Fourier transform on integrable functions

```lean
theorem VectorFourier.ae_eq_zero_of_integrable_of_forall_fourierIntegral_eq_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (B : LinearMap.BilinForm ℝ V) (_hB : B.Nondegenerate)
    (f : V → ℂ) (_hf : Integrable f μ)
    (_h : ∀ w : V, VectorFourier.fourierIntegral 𝐞 μ B f w = 0) :
    f =ᵐ[μ] 0
```

### `VectorFourier.fourierIntegral_flip_fourierIntegral_eq`

`Thm_VectorFourier_fourierIntegral_flip_fourierIntegral_eq` — Fourier inversion for a nondegenerate pairing and Haar measure

```lean
theorem VectorFourier.fourierIntegral_flip_fourierIntegral_eq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure]
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ V)
    (f : 𝓢(V, ℂ)) (x : V) :
    VectorFourier.fourierIntegral 𝐞 μ B.flip (VectorFourier.fourierIntegral 𝐞 μ B f) x
      = ((μ.real (ZSpan.fundamentalDomain b)) ^ 2 / |(Matrix.of fun i j => B (b i) (b j)).det| : ℝ)
        * f (-x)
```

## AddCircle (1)

### `AddCircle.exists_eq_coe_div_of_nsmul_eq_zero_of_dvd`

`Thm_AddCircle_exists_eq_coe_div_of_nsmul_eq_zero_of_dvd` — Torsion points of ℚ/ℤ have denominator any multiple of the order

```lean
theorem AddCircle.exists_eq_coe_div_of_nsmul_eq_zero_of_dvd
    (t : AddCircle (1 : ℚ)) (n N : ℕ) (hN : 0 < N) (hnN : n ∣ N) (ht : n • t = 0) :
    ∃ a : ℤ, t = (((a : ℚ) / (N : ℚ) : ℚ) : AddCircle (1 : ℚ))
```

## AdjoinRoot (1)

### `AdjoinRoot.exists_isLocalRing_faithfullyFlat_residueField_algEquiv_of_irreducible_map`

`Thm_AdjoinRoot_exists_isLocalRing_faithfullyFlat_residueField_algEquiv_of_irreducible_map` — Adjoining a root with irreducible reduction over a local ring

```lean
theorem AdjoinRoot.exists_isLocalRing_faithfullyFlat_residueField_algEquiv_of_irreducible_map
    (R : Type u) [CommRing R] [IsLocalRing R]
    (f : R[X]) (hfm : f.Monic) [Fact (Irreducible (f.map (residue R)))] :
    ∃ (_ : IsLocalRing (AdjoinRoot f)) (_ : IsLocalHom (algebraMap R (AdjoinRoot f))),
      Module.Finite R (AdjoinRoot f) ∧ Module.Free R (AdjoinRoot f) ∧ Module.FaithfullyFlat R (AdjoinRoot f) ∧
      Ideal.map (algebraMap R (AdjoinRoot f)) (maximalIdeal R) = maximalIdeal (AdjoinRoot f) ∧
      Nonempty (ResidueField (AdjoinRoot f) ≃ₐ[ResidueField R] AdjoinRoot (f.map (residue R)))
```

## AlgebraicGeometry (1)

### `AlgebraicGeometry.HilbertFunctor.exists_linearEquiv_baseChange_piece_map`

`Thm_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map` — Base change of the graded pieces of a homogeneous ideal

```lean
theorem AlgebraicGeometry.HilbertFunctor.exists_linearEquiv_baseChange_piece_map
    (n : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal (MvPolynomial (Fin (n + 1)) A))
    (hI : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) :
    (∀ q ∈ I.map (MvPolynomial.map (algebraMap A B)), ∀ d : ℕ,
        homogeneousComponent d q ∈ I.map (MvPolynomial.map (algebraMap A B))) ∧
    ∀ d : ℕ, ∃ e : B ⊗[A] piece I d ≃ₗ[B] piece (I.map (MvPolynomial.map (algebraMap A B))) d,
      ∀ (p : MvPolynomial (Fin (n + 1)) A) (hp : p.IsHomogeneous d),
        e (1 ⊗ₜ[A] Submodule.Quotient.mk ⟨p, hp⟩) =
          Submodule.Quotient.mk ⟨MvPolynomial.map (algebraMap A B) p, hp.map (algebraMap A B)⟩
```

## BrauerNesbitt (1)

### `BrauerNesbitt.exists_linearEquiv_of_span_range_eq_top_of_trace_eq`

`Thm_BrauerNesbitt_exists_linearEquiv_of_span_range_eq_top_of_trace_eq` — Brauer–Nesbitt: equal traces and spanning image give isomorphism

```lean
theorem BrauerNesbitt.exists_linearEquiv_of_span_range_eq_top_of_trace_eq {k : Type*} {G : Type*}
  {V₁ : Type*} {V₂ : Type*} [Field k] [Monoid G] [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
  [AddCommGroup V₂] [Module k V₂] [FiniteDimensional k V₂] (ρ₁ : Representation k G V₁)
  (ρ₂ : Representation k G V₂) [Nontrivial V₁] (hspan₁ : Submodule.span k (Set.range ⇑ρ₁) = ⊤)
  (hspan₂ : Submodule.span k (Set.range ⇑ρ₂) = ⊤)
  (htr : ∀ (g : G), (LinearMap.trace k V₁) (ρ₁ g) = (LinearMap.trace k V₂) (ρ₂ g)) :
  ∃ e : V₁ ≃ₗ[k] V₂, ∀ (g : G) (v : V₁), e ((ρ₁ g) v) = (ρ₂ g) (e v)
```

## CoherentBaseChange (1)

### `CoherentBaseChange.FibreH0Family.isClosed_setOf_le_h0`

`Thm_CoherentBaseChange_FibreH0Family_isClosed_setOf_le_h0` — Upper semicontinuity of fibre h⁰ for a family of two-term complexes

```lean
theorem CoherentBaseChange.FibreH0Family.isClosed_setOf_le_h0 {T : Scheme.{u}}
    (F : FibreH0Family T) (n : ℕ) :
    IsClosed {t : T | n ≤ F.h0 t}
```

## CompleteOrthogonalIdempotents (1)

### `CompleteOrthogonalIdempotents.exists_forall_mul_eq_mul_pow_val_of_pow_eq_one_of_isUnit_one_sub_pow`

`Thm_CompleteOrthogonalIdempotents_exists_forall_mul_eq_mul_pow_val_of_pow_eq_one_of_isUnit_one_sub_pow` — Cyclotomic idempotents diagonalising a bimultiplicative pairing

```lean
theorem CompleteOrthogonalIdempotents.exists_forall_mul_eq_mul_pow_val_of_pow_eq_one_of_isUnit_one_sub_pow
    {K : Type*} [AddCommGroup K] [Fintype K] [DecidableEq K] {d : ℕ} [NeZero d]
    {R : Type*} [CommRing R] (hd : IsUnit ((d : ℕ) : R)) (ζ : R) (hζ : ζ ^ d = 1) (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j))
    (e : K → K → Rˣ) (hed : ∀ k k' : K, e k k' ^ d = 1)
    (he₁ : ∀ k₁ k₂ k' : K, e (k₁ + k₂) k' = e k₁ k' * e k₂ k') (he₂ : ∀ k k₁ k₂ : K, e k (k₁ + k₂) = e k k₁ * e k k₂)
    (hee : ∀ k : K, e k k = 1) :
    ∃ ε : (K → K → ZMod d) → R, CompleteOrthogonalIdempotents ε ∧
      (∀ (B : K → K → ZMod d) (k k' : K), ε B * (e k k' : R) = ε B * ζ ^ (B k k').val) ∧
      (∀ B : K → K → ZMod d, ε B ≠ 0 →
        (∀ k₁ k₂ k' : K, B (k₁ + k₂) k' = B k₁ k' + B k₂ k') ∧ (∀ k k₁ k₂ : K, B k (k₁ + k₂) = B k k₁ + B k k₂) ∧
        (∀ k : K, B k k = 0))
```

## DeligneSerre (1)

### `DeligneSerre.exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul`

`Thm_DeligneSerre_exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul` — Eigencharacter with prescribed minimal prime kernel

```lean
theorem DeligneSerre.exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul
    {K : Type*} [Field K] [IsAlgClosed K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {T : Type*} [CommRing T] [Module T V] [SMulCommClass T K V] [FaithfulSMul T V]
    {𝔭 : Ideal T} (h𝔭 : 𝔭 ∈ minimalPrimes T) :
    ∃ χ : T →+* K, RingHom.ker χ = 𝔭 ∧
      ∃ x : V, x ≠ 0 ∧ (∀ p ∈ 𝔭, p • x = 0) ∧ (∀ r : T, r • x = 0 → r ∈ 𝔭) ∧
        ∀ t : T, t • x = χ t • x
```

## Derivation (1)

### `Derivation.add_mulLeft_pow_char`

`Thm_Derivation_add_mulLeft_pow_char` — Hochschild's formula for (d+a)ᵖ in characteristic p

```lean
theorem Derivation.add_mulLeft_pow_char {R : Type u} {F : Type v} [CommRing R] [CommRing F]
    [Algebra R F] (p : ℕ) [Fact p.Prime] [CharP F p] (d : Derivation R F F) (a : F) :
    (d.toLinearMap + LinearMap.mulLeft R a) ^ p
      = d.toLinearMap ^ p + LinearMap.mulLeft R (a ^ p + (d.toLinearMap ^ (p - 1)) a)
```

## DirectSum (1)

### `DirectSum.toModule_injective_of_forall_diag_injective_of_isInternal`

`Thm_DirectSum_toModule_injective_of_forall_diag_injective_of_isInternal` — Bidegreewise injectivity from injectivity on each anti-diagonal

```lean
theorem DirectSum.toModule_injective_of_forall_diag_injective_of_isInternal
    {R : Type u} [CommRing R] {H' : Type u} [AddCommGroup H'] [Module R H']
    (𝒜' : ℕ → Submodule R H') (h𝒜' : DirectSum.IsInternal 𝒜')
    (M : ℕ × ℕ → Type u) [∀ ab, AddCommGroup (M ab)] [∀ ab, Module R (M ab)]
    (Ψ : ∀ ab : ℕ × ℕ, M ab →ₗ[R] H') (hΨ : ∀ (ab : ℕ × ℕ) (x : M ab), Ψ ab x ∈ 𝒜' (ab.1 + ab.2))
    (hinj : ∀ n : ℕ, Function.Injective (DirectSum.toModule R (DoubleComplex.Diag n) H' (fun i => Ψ i.1))) :
    Function.Injective (DirectSum.toModule R (ℕ × ℕ) H' Ψ)
```

## ENat (1)

### `ENat.sum_toNat_eq_sum_depth_and_finsum_eq_sum_depth`

`Thm_ENat_sum_toNat_eq_sum_depth_and_finsum_eq_sum_depth` — Regrouping a place sum and a prime finsum by depth

```lean
theorem ENat.sum_toNat_eq_sum_depth_and_finsum_eq_sum_depth
    {Pl Pr : Type*} (E r : ℕ)
    (Ttot : Finset Pl) (ordZ : Pl → ℤ)
    (dep : Pl → ℕ) (hdep : ∀ V ∈ Ttot, 1 ≤ dep V ∧ dep V + 1 ≤ r * E)
    (T : ℕ → Finset Pl) (hT : ∀ p V, V ∈ T p ↔ V ∈ Ttot ∧ dep V = p)
    (horiz : Pr → Prop) (rk : Pr → ℕ) (lenU mult : Pr → ℕ∞) (depQ : Pr → ℕ)
    (hdepQ : ∀ Q, horiz Q → mult Q ≠ 0 →
      1 ≤ depQ Q ∧ depQ Q + 1 ≤ r * E ∧ (r : ℕ∞) * lenU Q = ((depQ Q * rk Q : ℕ) : ℕ∞) ∧
        1 ≤ rk Q ∧ lenU Q ≠ ⊤)
    (hfin : {Q : Pr | horiz Q ∧ mult Q ≠ 0}.Finite) :
    ((∑ V ∈ Ttot, (ordZ V).toNat : ℕ) : ℕ∞) =
        ∑ p ∈ Finset.Icc 1 (r * E - 1), ((∑ V ∈ T p, (ordZ V).toNat : ℕ) : ℕ∞) ∧
    (∑ᶠ (Q : Pr) (_ : horiz Q), (rk Q : ℕ∞) * mult Q) =
        ∑ p ∈ Finset.Icc 1 (r * E - 1),
          ∑ᶠ (Q : Pr) (_ : horiz Q ∧ (r : ℕ∞) * lenU Q = ((p * rk Q : ℕ) : ℕ∞)), (rk Q : ℕ∞) * mult Q
```

## Equiv (1)

### `Equiv.Perm.exists_comp_succAbove_eq_succAbove_comp_and_sign_eq`

`Thm_Equiv_Perm_exists_comp_succAbove_eq_succAbove_comp_and_sign_eq` — Deleting a point from a permutation, with sign

```lean
theorem Equiv.Perm.exists_comp_succAbove_eq_succAbove_comp_and_sign_eq
    {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (j : Fin (n + 1)) :
    ∃ τ : Equiv.Perm (Fin n), (∀ k : Fin n, σ (j.succAbove k) = (σ j).succAbove (τ k)) ∧
      Equiv.Perm.sign σ = (-1) ^ ((j : ℕ) + ((σ j) : ℕ)) * Equiv.Perm.sign τ
```

## Finsupp (1)

### `Finsupp.card_le_macaulayPow_card_of_forall_sub_single_mem`

`Thm_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem` — Macaulay's bound for monomial sets one degree up

```lean
theorem Finsupp.card_le_macaulayPow_card_of_forall_sub_single_mem
    (n d : ℕ) (hd : 1 ≤ d) (B : Finset (Fin (n + 1) →₀ ℕ)) (hB : ∀ m ∈ B, m.degree = d)
    (C : Finset (Fin (n + 1) →₀ ℕ)) (hC : ∀ u ∈ C, u.degree = d + 1)
    (hCB : ∀ u ∈ C, ∀ i : Fin (n + 1), 1 ≤ u i → u - Finsupp.single i 1 ∈ B) :
    C.card ≤ Nat.macaulayPow d B.card
```

## GradedAlgebra (1)

### `GradedAlgebra.bijective_tensorProduct_lift_of_forall_isBaseChange`

`Thm_GradedAlgebra_bijective_tensorProduct_lift_of_forall_isBaseChange` — Degreewise base change detects isomorphism of graded algebras

```lean
theorem GradedAlgebra.bijective_tensorProduct_lift_of_forall_isBaseChange
    {S : Type u} [CommRing S] (T : Type u) [CommRing T] [Algebra S T]
    (A : Type u) [CommRing A] [Algebra S A] (𝓐 : ℕ → Submodule S A) [GradedAlgebra 𝓐]
    (B : Type u) [CommRing B] [Algebra T B] [Algebra S B] [IsScalarTower S T B]
    (𝓑 : ℕ → Submodule T B) [GradedAlgebra 𝓑]
    (ϑ : A →ₐ[S] B) (hϑdeg : ∀ n, ∀ x ∈ 𝓐 n, ϑ x ∈ 𝓑 n)
    (hbc : ∀ n, IsBaseChange T ((ϑ.toLinearMap.restrict (p := 𝓐 n) (q := (𝓑 n).restrictScalars S) (hϑdeg n))
      : 𝓐 n →ₗ[S] (𝓑 n).restrictScalars S)) :
    Function.Bijective
      (Algebra.TensorProduct.lift ϑ (IsScalarTower.toAlgHom S T B) (fun _ _ => Commute.all _ _) : A ⊗[S] T →ₐ[S] B)
```

## Homeomorph (1)

### `Homeomorph.exists_sheet_decomposition`

`Thm_Homeomorph_exists_sheet_decomposition` — Sheets of a trivialised map over a smaller open set

```lean
theorem Homeomorph.exists_sheet_decomposition {E X I : Type*} [TopologicalSpace E]
    [TopologicalSpace X] [TopologicalSpace I] [DiscreteTopology I] {f : E → X} {U : Set X}
    {Ω : Set E} (hpre : IsOpen Ω) (H : Ω ≃ₜ U × I) (hH : ∀ x, ((H x).1 : X) = f x)
    {V : Set X} (hV : IsOpen V) (hVU : V ⊆ U) [Nonempty Ω] :
    ∃ ζ : I → OpenPartialHomeomorph E X,
      (∀ i, (ζ i).target = V) ∧
      (∀ i, ∀ e ∈ (ζ i).source, e ∈ Ω ∧ ζ i e = f e) ∧
      (∀ i, ∀ z ∈ V, (ζ i).symm z ∈ Ω ∧ f ((ζ i).symm z) = z) ∧
      (Pairwise fun i j => Disjoint (ζ i).source (ζ j).source) ∧
      (∀ e : E, e ∈ Ω → f e ∈ V → ∃ i, e ∈ (ζ i).source)
```

## IncidenceSystem (1)

### `IncidenceSystem.Data.isUnit_det_jacobian_iff`

`Thm_IncidenceSystem_Data_isUnit_det_jacobian_iff` — Unit Jacobian criterion for the incidence system

```lean
theorem IncidenceSystem.Data.isUnit_det_jacobian_iff
    {g e m' : ℕ} {A : Type*} [CommRing A] (D : IncidenceSystem.Data g e m' A) (pt : Var g e m' → A)
    (htri : ∀ i (j j' : Fin e), j < j' → MvPolynomial.pderiv (some j') (D.G i j) = 0)
    (hc : ∀ k, pt (Var.c k) = 0)
    (hσ : ∀ i r, pt (Var.σ none i r) = if (r : ℕ) = 0 then 1 else 0)
    (hp : ∀ i, D.p none i = (MvPolynomial.X none - MvPolynomial.C (pt (Var.u i))) ^ (m' + 1))
    (hs : ∀ i, D.s none i = 1)
    (hG : ∀ i j, IsUnit (D.dG pt i j)) (hsv : ∀ k i, IsUnit (D.sVal pt k i)) :
    IsUnit (D.jacobian pt).det ↔ IsUnit (((m' + 1 : ℕ) : A) ^ g) ∧ IsUnit (D.tcMatrix pt).det
```

## InnerProductSpace (1)

### `InnerProductSpace.exists_mem_norm_sub_lt_of_exists_mem_span_orbit_of_average`

`Thm_InnerProductSpace_exists_mem_norm_sub_lt_of_exists_mem_span_orbit_of_average` — Averaging recovers a vector of a cyclic span

```lean
theorem InnerProductSpace.exists_mem_norm_sub_lt_of_exists_mem_span_orbit_of_average
    {G : Type*} [Group G] {L : Type*} [AddCommGroup L] [Module ℂ L]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : G →* (L →ₗ[ℂ] L)) (S : Submodule ℂ L) (hS : ∀ x : G, ∀ f ∈ S, ρ x f ∈ S)
    (ι : L → H)
    (hι : ∀ (a b : ℂ) (f g : L), f ∈ S → g ∈ S → ι (a • f + b • g) = a • ι f + b • ι g)
    (c : G → ℝ) (hc : ∀ x, 0 < c x)
    (hρ : ∀ x : G, ∀ f ∈ S, ‖ι (ρ x f)‖ ^ 2 = c x * ‖ι f‖ ^ 2)
    (P : L → Prop) (E : L → L)
    (hE : ∀ (a b : ℂ) (f g : L), f ∈ S → g ∈ S → E (a • f + b • g) = a • E f + b • E g)
    (hEP : ∀ f ∈ S, P (E f))
    (hEinner : ∀ f ∈ S, ∀ g ∈ S, P g → ⟪ι (E f), ι g⟫_ℂ = ⟪ι f, ι g⟫_ℂ)
    (φ φ' : L) (hφ : φ ∈ S) (hPφ : P φ) (hφ' : φ' ∈ S)
    (hspan : ∀ ε : ℝ, 0 < ε →
      ∃ v ∈ Submodule.span ℂ (Set.range fun x : G => ρ x φ), ‖ι φ' - ι v‖ < ε)
    (W : Submodule ℂ L) (hWS : W ≤ S)
    (hWφ' : W ≤ Submodule.span ℂ (Set.range fun x : G => ρ x φ'))
    (hWρ : ∀ x : G, ∀ w ∈ W, ρ x w ∈ W) (hWE : ∀ w ∈ W, E w ∈ W)
    (hEφ' : ∀ x : G, E (ρ x φ') ∈ W) :
    ∀ ε : ℝ, 0 < ε → ∃ w ∈ W, ‖ι φ' - ι w‖ < ε
```

## IsBaseChange (1)

### `IsBaseChange.exists_dual_comp_eq_algebraMap_and_sum_smul_eq`

`Thm_IsBaseChange_exists_dual_comp_eq_algebraMap_and_sum_smul_eq` — Dual families extend along a base change

```lean
theorem IsBaseChange.exists_dual_comp_eq_algebraMap_and_sum_smul_eq
    {A : Type u} [CommRing A] {A' : Type v} [CommRing A'] [Algebra A A']
    {M : Type w} [AddCommGroup M] [Module A M]
    {M' : Type w'} [AddCommGroup M'] [Module A M'] [Module A' M'] [IsScalarTower A A' M']
    (f : M →ₗ[A] M') (hf : IsBaseChange A' f)
    {n : ℕ} (x : Fin n → M) (φ : Fin n → (M →ₗ[A] A)) (hxφ : ∀ m : M, ∑ i, φ i m • x i = m) :
    ∃ φ' : Fin n → (M' →ₗ[A'] A'),
      (∀ (i : Fin n) (m : M), φ' i (f m) = algebraMap A A' (φ i m)) ∧
        ∀ m' : M', ∑ i, φ' i m' • f (x i) = m'
```

## IsFreeGroup (1)

### `IsFreeGroup.surjective_transfer_and_transfer_eq_one_iff_mem_closure`

`Thm_IsFreeGroup_surjective_transfer_and_transfer_eq_one_iff_mem_closure` — Transfer from a finite-index normal subgroup of a free group

```lean
theorem IsFreeGroup.surjective_transfer_and_transfer_eq_one_iff_mem_closure
    {F : Type*} [Group F] [IsFreeGroup F] (R : Subgroup F) [R.Normal] [R.FiniteIndex]
    (hR : ∀ x y : F, x * y * x⁻¹ * y⁻¹ ∈ R) (A : Type*) [CommGroup A] :
    Function.Surjective (fun χ : ↥R →* A => MonoidHom.transfer χ) ∧
    ∀ χ : ↥R →* A, MonoidHom.transfer χ = 1 ↔
      χ ∈ Subgroup.closure {ψ : ↥R →* A | ∃ (g : F) (χ' : ↥R →* A),
        ψ = (χ'.comp (MulAut.conjNormal g : MulAut ↥R).toMonoidHom) / χ'}
```

## IsLocalizedModule (1)

### `IsLocalizedModule.existsUnique_forall_comp_eq_of_span_eq_top`

`Thm_IsLocalizedModule_existsUnique_forall_comp_eq_of_span_eq_top` — Uniqueness of the Zariski glue of localised modules

```lean
theorem IsLocalizedModule.existsUnique_forall_comp_eq_of_span_eq_top
    {B : Type u} [CommRing B] {k : ℕ} (f : Fin k → B) (hf : Ideal.span (Set.range f) = ⊤)
    (M : Fin k → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module B (M i)]
    (M₂ : Fin k → Fin k → Type u) [∀ i j, AddCommGroup (M₂ i j)] [∀ i j, Module B (M₂ i j)]
    (ρl : ∀ i j, M i →ₗ[B] M₂ i j) (ρr : ∀ i j, M j →ₗ[B] M₂ i j)
    (hρr : ∀ i j, IsLocalizedModule (Submonoid.powers (f i)) (ρr i j))
    (N : Type u) [AddCommGroup N] [Module B N] (π : ∀ i, N →ₗ[B] M i)
    (hπ : ∀ i, IsLocalizedModule (Submonoid.powers (f i)) (π i))
    (hπc : ∀ i j, ρl i j ∘ₗ π i = ρr i j ∘ₗ π j)
    (T : Type u) [AddCommGroup T] [Module B T] (g : ∀ i, T →ₗ[B] M i)
    (hg : ∀ i j, ρl i j ∘ₗ g i = ρr i j ∘ₗ g j) :
    ∃! G : T →ₗ[B] N, ∀ i, π i ∘ₗ G = g i
```

## IsOpen (1)

### `IsOpen.exists_numberField_ker_restrictNormalHom_le`

`Thm_IsOpen_exists_numberField_ker_restrictNormalHom_le` — Open subgroups of Gal(ℚ̄/ℚ) contain a finite-level kernel

```lean
theorem IsOpen.exists_numberField_ker_restrictNormalHom_le
    {H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
    (hH : IsOpen (H : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))) :
    ∃ (F : Type) (_ : Field F) (_ : NumberField F) (_ : IsGalois ℚ F)
      (_ : Algebra F (AlgebraicClosure ℚ)) (_ : IsScalarTower ℚ F (AlgebraicClosure ℚ)),
      (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ H
```

## IsPreconnected (1)

### `IsPreconnected.exists_forall_eq_sum_zsmul_of_continuousOn_of_linearIndependent`

`Thm_IsPreconnected_exists_forall_eq_sum_zsmul_of_continuousOn_of_linearIndependent` — Integer coordinates in a varying frame are locally constant

```lean
theorem IsPreconnected.exists_forall_eq_sum_zsmul_of_continuousOn_of_linearIndependent
    {X : Type*} [TopologicalSpace X] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {k : ℕ} {S : Set X} (hS : IsPreconnected S)
    (v : Fin k → X → V) (hv : ∀ i, ContinuousOn (v i) S)
    (hlin : ∀ z ∈ S, LinearIndependent ℝ (fun i => v i z))
    (x : X → V) (hx : ContinuousOn x S)
    (hmem : ∀ z ∈ S, ∃ n : Fin k → ℤ, x z = ∑ i, n i • v i z) :
    ∃ n : Fin k → ℤ, ∀ z ∈ S, x z = ∑ i, n i • v i z
```

## IsSMulRegular (1)

### `IsSMulRegular.tensorProduct_of_flat_quotSMulTop`

`Thm_IsSMulRegular_tensorProduct_of_flat_quotSMulTop` — Regularity of t on M ⊗_A B from flatness of B/tB

```lean
theorem IsSMulRegular.tensorProduct_of_flat_quotSMulTop
    {A : Type u} [CommRing A] (t : A) {B : Type v} [AddCommGroup B] [Module A B]
    {M : Type w} [AddCommGroup M] [Module A M]
    (htA : IsSMulRegular A t) (htB : IsSMulRegular B t) (htM : IsSMulRegular M t)
    [Module.Flat (A ⧸ Ideal.span {t}) (QuotSMulTop t B)] :
    IsSMulRegular (M ⊗[A] B) t
```

## LinearAlgebra (1)

### `LinearAlgebra.exists_eigenvector_add_image_sum_sq_of_skew_of_posDef_hermitian`

`Thm_LinearAlgebra_exists_eigenvector_add_image_sum_sq_of_skew_of_posDef_hermitian` — Eigenvector plus image decomposition for a sum of squares of skew operators

```lean
theorem LinearAlgebra.exists_eigenvector_add_image_sum_sq_of_skew_of_posDef_hermitian
    (V : Type*) [AddCommGroup V] [Module ℂ V] (M₀ : Submodule ℂ V) [Module.Finite ℂ M₀]
    (B : V → V → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w ∈ M₀, ∀ w' ∈ M₀, B w' w = (starRingEnd ℂ) (B w w'))
    (hpos : ∀ w ∈ M₀, w ≠ 0 → 0 < (B w w).re)
    (ι : Type*) [Fintype ι] (θ : ι → (V →ₗ[ℂ] V))
    (hθM : ∀ i : ι, ∀ w ∈ M₀, θ i w ∈ M₀)
    (hskew : ∀ i : ι, ∀ w ∈ M₀, ∀ w' ∈ M₀, B (θ i w) w' = -B w (θ i w'))
    (c : ℂ) (z : V) (hz : z ∈ M₀) :
    ∃ k ∈ M₀, ∃ x ∈ M₀, (∑ i : ι, θ i * θ i) k = c • k ∧ z = k + ((∑ i : ι, θ i * θ i) x - c • x)
```

## Localization (1)

### `Localization.localRingHom_surjective_and_ker_eq_map_of_surjective`

`Thm_Localization_localRingHom_surjective_and_ker_eq_map_of_surjective` — Localisation at a prime of a surjective ring map

```lean
theorem Localization.localRingHom_surjective_and_ker_eq_map_of_surjective
    {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Surjective f)
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] (hpq : p = Ideal.comap f q) :
    Function.Surjective (Localization.localRingHom p q f hpq) ∧
      RingHom.ker (Localization.localRingHom p q f hpq) =
        Ideal.map (algebraMap A (Localization.AtPrime p)) (RingHom.ker f)
```

## ModularGroup (1)

### `ModularGroup.exists_mulEquiv_freeProduct_quotient_center`

`Thm_ModularGroup_exists_mulEquiv_freeProduct_quotient_center` — PSL₂(ℤ) is the free product C₂ * C₃

```lean
theorem ModularGroup.exists_mulEquiv_freeProduct_quotient_center :
    ∃ e : Monoid.CoprodI (fun i : Fin 2 => Multiplicative (ZMod (i.val + 2)))
        ≃* Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) ℤ),
      e (Monoid.CoprodI.of (M := fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))) (i := 0)
          (Multiplicative.ofAdd 1)) = QuotientGroup.mk ModularGroup.S ∧
      e (Monoid.CoprodI.of (M := fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))) (i := 1)
          (Multiplicative.ofAdd 1)) = QuotientGroup.mk (ModularGroup.S * ModularGroup.T)
```

## MvPowerSeries (1)

### `MvPowerSeries.ringKrullDim_fin_eq_of_isDiscreteValuationRing`

`Thm_MvPowerSeries_ringKrullDim_fin_eq_of_isDiscreteValuationRing` — Krull dimension of 𝒪[[X₁,…,Xₙ]] over a discrete valuation ring

```lean
theorem MvPowerSeries.ringKrullDim_fin_eq_of_isDiscreteValuationRing
    (𝓞 : Type*) [CommRing 𝓞] [IsDomain 𝓞] [IsDiscreteValuationRing 𝓞] (n : ℕ) :
    ringKrullDim (MvPowerSeries (Fin n) 𝓞) = ((n + 1 : ℕ) : WithBot ℕ∞)
```

## NumberField (1)

### `NumberField.finrank_eq_one_of_forall_isUnramifiedAt`

`Thm_NumberField_finrank_eq_one_of_forall_isUnramifiedAt` — An everywhere-unramified number field is ℚ

```lean
theorem NumberField.finrank_eq_one_of_forall_isUnramifiedAt
    (K : Type*) [Field K] [NumberField K]
    (H : ∀ (P : Ideal (𝓞 K)) [P.IsMaximal], Algebra.IsUnramifiedAt ℤ P) :
    Module.finrank ℚ K = 1
```

## Orthonormal (1)

### `Orthonormal.hasSum_inner_smul_map_of_map_eq_zero_of_forall_inner_eq_zero`

`Thm_Orthonormal_hasSum_inner_smul_map_of_map_eq_zero_of_forall_inner_eq_zero` — Orthonormal expansion passes through a vanishing continuous operator

```lean
theorem Orthonormal.hasSum_inner_smul_map_of_map_eq_zero_of_forall_inner_eq_zero
    {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {ι : Type*} (b : ι → E) (hb : Orthonormal 𝕜 b) (T : E →L[𝕜] F)
    (hT : ∀ v : E, (∀ i, ⟪b i, v⟫_𝕜 = 0) → T v = 0) (u : E) :
    HasSum (fun i => ⟪b i, u⟫_𝕜 • T (b i)) (T u)
```

## QuotientGroup (1)

### `QuotientGroup.eq_one_of_pow_char_pow_eq_one_pi_units_quotient_constRange`

`Thm_QuotientGroup_eq_one_of_pow_char_pow_eq_one_pi_units_quotient_constRange` — No p-power torsion in (K^×)^s/Δ K^× in characteristic p

```lean
theorem QuotientGroup.eq_one_of_pow_char_pow_eq_one_pi_units_quotient_constRange
    (K : Type u) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (n s : ℕ)
    (ξ : (Fin s → Kˣ) ⧸ (Pi.constMonoidHom (Fin s) Kˣ).range) (hξ : ξ ^ (p ^ n) = 1) : ξ = 1
```

## RestrictedProduct (1)

### `RestrictedProduct.measurable_iff_forall_measurable_apply`

`Thm_RestrictedProduct_measurable_iff_forall_measurable_apply` — Measurability into a restricted product is coordinatewise

```lean
theorem RestrictedProduct.measurable_iff_forall_measurable_apply
    {ι : Type*} [Countable ι] {R : ι → Type*}
    [∀ i, TopologicalSpace (R i)] [∀ i, SecondCountableTopology (R i)]
    [∀ i, MeasurableSpace (R i)] [∀ i, BorelSpace (R i)]
    {A : (i : ι) → Set (R i)} (hA : ∀ i, MeasurableSet (A i))
    [MeasurableSpace (Πʳ i, [R i, A i])] [BorelSpace (Πʳ i, [R i, A i])]
    {X : Type*} [MeasurableSpace X] (f : X → Πʳ i, [R i, A i]) :
    Measurable f ↔ ∀ i, Measurable fun x => f x i
```

## RingHom (1)

### `RingHom.exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed`

`Thm_RingHom_exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed` — Extending a character along an integral extension into an algebraically closed field

```lean
theorem RingHom.exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed {A B K : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B] [Field K] [IsAlgClosed K] (χ : A →+* K) (hker : RingHom.ker (algebraMap A B) ≤ RingHom.ker χ) : ∃ ψ : B →+* K, ψ.comp (algebraMap A B) = χ
```

## RingTheory (1)

### `RingTheory.Sequence.IsWeaklyRegular.isZero_tor_one_quotient_ofList`

`Thm_RingTheory_Sequence_IsWeaklyRegular_isZero_tor_one_quotient_ofList` — Vanishing of Tor₁(R/(x₁,…,xₙ),M) for weakly regular sequences

```lean
theorem RingTheory.Sequence.IsWeaklyRegular.isZero_tor_one_quotient_ofList
    {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
    {rs : List R} (hM : RingTheory.Sequence.IsWeaklyRegular M rs) :
    IsZero (((Tor (ModuleCat.{u} R) 1).obj (ModuleCat.of R (R ⧸ Ideal.ofList rs))).obj
      (ModuleCat.of R M))
```

## Set (1)

### `Set.ncard_pairing_annihilator_mul_ncard_eq_ncard_mul_ncard_radical`

`Thm_Set_ncard_pairing_annihilator_mul_ncard_eq_ncard_mul_ncard_radical` — Annihilator count for a bimultiplicative pairing

```lean
theorem Set.ncard_pairing_annihilator_mul_ncard_eq_ncard_mul_ncard_radical
    {J J' : Type} [AddCommGroup J] [AddCommGroup J'] {L : Type} [Field L] [CharZero L]
    (A : Set J) (X' : Set J') (hA : A.Finite) (hX' : X'.Finite)
    (hA0 : (0 : J) ∈ A) (hAadd : ∀ x ∈ A, ∀ y ∈ A, x + y ∈ A) (hAneg : ∀ x ∈ A, -x ∈ A)
    (hX'0 : (0 : J') ∈ X') (hX'add : ∀ x ∈ X', ∀ y ∈ X', x + y ∈ X') (hX'neg : ∀ x ∈ X', -x ∈ X')
    (B : J → J' → L)
    (hBl : ∀ a ∈ A, ∀ a' ∈ A, ∀ y ∈ X', B (a + a') y = B a y * B a' y)
    (hBr : ∀ a ∈ A, ∀ y ∈ X', ∀ y' ∈ X', B a (y + y') = B a y * B a y') :
    Set.ncard {y : J' | y ∈ X' ∧ ∀ a ∈ A, B a y = 1} * Set.ncard A =
      Set.ncard X' * Set.ncard {a : J | a ∈ A ∧ ∀ y ∈ X', B a y = 1}
```

## SimpleGraph (1)

### `SimpleGraph.exists_walkConnected_transversal_of_preconnected`

`Thm_SimpleGraph_exists_walkConnected_transversal_of_preconnected` — Walk-connected orbit transversal in a preconnected graph

```lean
theorem SimpleGraph.exists_walkConnected_transversal_of_preconnected {V : Type*} {T : SimpleGraph V} {Γ : Type*} [Group Γ] [MulAction Γ V]
    (hsmul : ∀ (γ : Γ) {v w : V}, T.Adj v w → T.Adj (γ • v) (γ • w))
    (hpre : T.Preconnected) (v₀ : V) :
    ∃ D : Set V, v₀ ∈ D ∧
      (∀ v ∈ D, ∀ w ∈ D, ∃ p : T.Walk v w, ∀ x ∈ p.support, x ∈ D) ∧
      (∀ v ∈ D, ∀ w ∈ D, v ∈ MulAction.orbit Γ w → v = w) ∧
      (∀ u : V, ∃ v ∈ D, v ∈ MulAction.orbit Γ u)
```

## Sobolev (1)

### `Sobolev.exists_forall_norm_le_mul_sum_sqrt_integral_norm_iteratedFDeriv_sq_of_contDiff_box`

`Thm_Sobolev_exists_forall_norm_le_mul_sum_sqrt_integral_norm_iteratedFDeriv_sq_of_contDiff_box` — Sobolev bound on a cube: sup norm by L² derivatives

```lean
theorem Sobolev.exists_forall_norm_le_mul_sum_sqrt_integral_norm_iteratedFDeriv_sq_of_contDiff_box
    (n : ℕ) (ℓ : ℝ) (hℓ : 0 < ℓ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (a : Fin n → ℝ) (f : (Fin n → ℝ) → ℂ), ContDiff ℝ n f →
      ∀ x : Fin n → ℝ, (∀ i, x i ∈ Set.Icc (a i) (a i + ℓ)) →
        ‖f x‖ ≤ c * ∑ k ∈ Finset.range (n + 1),
          Real.sqrt (∫ y in Set.pi Set.univ (fun i => Set.Icc (a i) (a i + ℓ)), ‖iteratedFDeriv ℝ k f y‖ ^ 2)
```

## Subalgebra (1)

### `Subalgebra.isIntegrallyClosed_adjoin_singleton_of_transcendental`

`Thm_Subalgebra_isIntegrallyClosed_adjoin_singleton_of_transcendental` — L[x] is integrally closed for x transcendental

```lean
theorem Subalgebra.isIntegrallyClosed_adjoin_singleton_of_transcendental
    {L : Type*} [Field L] {F : Type*} [CommRing F] [IsDomain F] [Algebra L F]
    (x : F) (hxL : Transcendental L x) :
    IsIntegrallyClosed (Algebra.adjoin L ({x} : Set F))
```

## Subring (1)

### `Subring.exists_isLocalRing_isNoetherianRing_faithfullyFlat_of_directed_of_flat_of_map_maximalIdeal_eq`

`Thm_Subring_exists_isLocalRing_isNoetherianRing_faithfullyFlat_of_directed_of_flat_of_map_maximalIdeal_eq` — Directed union of Noetherian local rings along flat inclusions

```lean
theorem Subring.exists_isLocalRing_isNoetherianRing_faithfullyFlat_of_directed_of_flat_of_map_maximalIdeal_eq
    (A : Type u) [CommRing A] {ι : Type v} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (S : ι → Subring A) (hS : Monotone S) (hcov : ∀ x : A, ∃ i, x ∈ S i)
    [∀ i, IsLocalRing (S i)] [∀ i, IsNoetherianRing (S i)]
    (hflat : ∀ ⦃i j : ι⦄ (h : i ≤ j), (Subring.inclusion (hS h)).Flat)
    (hmax : ∀ ⦃i j : ι⦄ (h : i ≤ j),
      Ideal.map (Subring.inclusion (hS h)) (maximalIdeal (S i)) = maximalIdeal (S j)) :
    ∃ _ : IsLocalRing A, IsNoetherianRing A ∧
      ∀ i, Module.FaithfullyFlat (S i) A ∧
        Ideal.map (algebraMap (S i) A) (maximalIdeal (S i)) = maximalIdeal A
```

## Summable (1)

### `Summable.exists_forall_tsum_prod_inv_one_add_abs_linearMap_intCast_sub_sq_le_of_injective`

`Thm_Summable_exists_forall_tsum_prod_inv_one_add_abs_linearMap_intCast_sub_sq_le_of_injective` — Uniform bound for shifted lattice sums of prod(1+|xᵢ|)⁻²

```lean
theorem Summable.exists_forall_tsum_prod_inv_one_add_abs_linearMap_intCast_sub_sq_le_of_injective
    (a r : ℕ) (A : (Fin a → ℝ) →ₗ[ℝ] (Fin r → ℝ)) (hA : Function.Injective A) :
    ∃ K : ℝ, ∀ t : Fin r → ℝ,
      Summable (fun k : Fin a → ℤ => ∏ i, (1 + |A (fun j => (k j : ℝ)) i - t i|)⁻¹ ^ 2) ∧
      ∑' k : Fin a → ℤ, ∏ i, (1 + |A (fun j => (k j : ℝ)) i - t i|)⁻¹ ^ 2 ≤ K
```

## TopCat (1)

### `TopCat.Sheaf.isIso_of_isIso_app_of_isBasis`

`Thm_TopCat_Sheaf_isIso_of_isIso_app_of_isBasis` — Sheaf morphism is an isomorphism if it is on a basis

```lean
theorem TopCat.Sheaf.isIso_of_isIso_app_of_isBasis {C : Type u} [Category.{v} C] {X : TopCat.{w}}
    {ι : Type u'} {B : ι → Opens X} (hB : Opens.IsBasis (Set.range B)) {F G : TopCat.Sheaf C X} (φ : F ⟶ G)
    (h : ∀ i, IsIso (φ.1.app (op (B i)))) : IsIso φ
```

## TopologicalSpace (1)

### `TopologicalSpace.NoetherianSpace.isClopen_of_stableUnderSpecialization_of_stableUnderGeneralization`

`Thm_TopologicalSpace_NoetherianSpace_isClopen_of_stableUnderSpecialization_of_stableUnderGeneralization` — Specialisation- and generalisation-stable subsets of noetherian sober spaces are clopen

```lean
theorem TopologicalSpace.NoetherianSpace.isClopen_of_stableUnderSpecialization_of_stableUnderGeneralization
    {X : Type u} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] [QuasiSober X] {s : Set X}
    (h₁ : StableUnderSpecialization s) (h₂ : StableUnderGeneralization s) : IsClopen s
```

## Topology (1)

### `Topology.IsConstructible.mem_of_mem_closure_of_forall_specializes`

`Thm_Topology_IsConstructible_mem_of_mem_closure_of_forall_specializes` — Constructible sets contain points of the closure generising them

```lean
theorem Topology.IsConstructible.mem_of_mem_closure_of_forall_specializes
    {X : Type u} [TopologicalSpace X] {s : Set X} (hs : Topology.IsConstructible s)
    {x : X} (hx : x ∈ closure s) (hgen : ∀ y ∈ s, x ⤳ y) : x ∈ s
```

## Tuple (1)

### `Tuple.succAbove_sort_comp_succAbove_eq`

`Thm_Tuple_succAbove_sort_comp_succAbove_eq` — Sorting commutes with deleting one entry

```lean
theorem Tuple.succAbove_sort_comp_succAbove_eq
    {n : ℕ} {ι : Type*} [LinearOrder ι] (u : Fin (n + 1) → ι) (hu : Function.Injective u) (i : Fin (n + 1)) (k : Fin n) :
    i.succAbove (Tuple.sort (u ∘ i.succAbove) k) = Tuple.sort u (((Tuple.sort u).symm i).succAbove k)
```

## UnitAddTorus (1)

### `UnitAddTorus.exists_isProbabilityMeasure_annihilator_integral_prod_fourier`

`Thm_UnitAddTorus_exists_isProbabilityMeasure_annihilator_integral_prod_fourier` — Haar probability measure on the annihilator of Q⊆ℤᵈ

```lean
theorem UnitAddTorus.exists_isProbabilityMeasure_annihilator_integral_prod_fourier
    (d : ℕ) (Q : AddSubgroup (Fin d → ℤ)) :
    ∃ m : Measure (Fin d → AddCircle (1 : ℝ)), IsProbabilityMeasure m ∧
      m {θ : Fin d → AddCircle (1 : ℝ) | ∀ q ∈ Q, (∏ i, fourier (q i) (θ i)) = 1}ᶜ = 0 ∧
      (∀ n : Fin d → ℤ, n ∈ Q → ∫ θ, (∏ i, fourier (n i) (θ i)) ∂m = 1) ∧
      (∀ n : Fin d → ℤ, n ∉ Q → ∫ θ, (∏ i, fourier (n i) (θ i)) ∂m = 0) ∧
      ({θ : Fin d → AddCircle (1 : ℝ) | ∀ q ∈ Q, (∏ i, fourier (q i) (θ i)) = 1}.Infinite →
        ∀ θ : Fin d → AddCircle (1 : ℝ), m {θ} = 0)
```

## WittVector (1)

### `WittVector.exists_isDiscreteValuationRing_charZero_residueField_ringEquiv_and_sq_eq_of_isAlgClosed`

`Thm_WittVector_exists_isDiscreteValuationRing_charZero_residueField_ringEquiv_and_sq_eq_of_isAlgClosed` — Existence of W(k) and a ramified quadratic extension W(k)[√ p]

```lean
theorem WittVector.exists_isDiscreteValuationRing_charZero_residueField_ringEquiv_and_sq_eq_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharP k p] :
    ∃ (Onr : Type) (_ : CommRing Onr) (_ : IsDomain Onr) (_ : IsDiscreteValuationRing Onr) (_ : CharZero Onr)
      (_ : Algebra ℤ_[p] Onr)
      (_ : IsAdicComplete (Ideal.span {algebraMap ℤ_[p] Onr (p : ℤ_[p])}) Onr)
      (_ : (Ideal.span {algebraMap ℤ_[p] Onr (p : ℤ_[p])}).IsMaximal)
      (e : IsLocalRing.ResidueField Onr ≃+* k)
      (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O') (_ : CharZero O')
      (_ : Algebra Onr O') (_ : IsAdicComplete (IsLocalRing.maximalIdeal O') O')
      (ϖ' : O') (_ : ϖ' ∈ IsLocalRing.maximalIdeal O') (_ : ϖ' * ϖ' = algebraMap Onr O' ((p : ℕ) : Onr))
      (φ' : O' →+* k),
      Function.Surjective φ' ∧ φ'.comp (algebraMap Onr O') = (e : IsLocalRing.ResidueField Onr →+* k).comp (IsLocalRing.residue Onr)
```

## contDiff (1)

### `contDiff_iteratedDeriv_slice_and_norm_iteratedFDeriv_le_norm_iteratedFDeriv_add`

`Thm_contDiff_iteratedDeriv_slice_and_norm_iteratedFDeriv_le_norm_iteratedFDeriv_add` — Smoothness and derivative bound for x-derivative slices

```lean
theorem contDiff_iteratedDeriv_slice_and_norm_iteratedFDeriv_le_norm_iteratedFDeriv_add
    {n : ℕ} (Φ : ℝ × (Fin n → ℝ) → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (j : ℕ) (x : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y' : Fin n → ℝ => iteratedDeriv j (fun t : ℝ => Φ (t, y')) x) ∧
    ∀ (N : ℕ) (y : Fin n → ℝ),
      ‖iteratedFDeriv ℝ N (fun y' : Fin n → ℝ => iteratedDeriv j (fun t : ℝ => Φ (t, y')) x) y‖ ≤
        ‖iteratedFDeriv ℝ (N + j) Φ (x, y)‖
```

## integralClosure (1)

### `integralClosure.exists_complex_ringEquiv_apply_eq`

`Thm_integralClosure_exists_complex_ringEquiv_apply_eq` — Two maps from the algebraic integers differ by a ℂ-automorphism

```lean
theorem integralClosure.exists_complex_ringEquiv_apply_eq (k : Type*) [Field k]
    (φ ψ : integralClosure ℤ ℂ →+* k) :
    ∃ σ : ℂ ≃+* ℂ, ∀ x y : integralClosure ℤ ℂ, (y : ℂ) = σ (x : ℂ) → φ x = ψ y
```

## iteratedFDeriv (1)

### `iteratedFDeriv_smul_comp_apply_append_inl_inr`

`Thm_iteratedFDeriv_smul_comp_apply_append_inl_inr` — Separated-variables product rule on tangential and normal slots

```lean
theorem iteratedFDeriv_smul_comp_apply_append_inl_inr
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (A : E → F) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (j l : ℕ) (e : E) (ρ : ℝ) (u : Fin j → E) :
    iteratedFDeriv ℝ (j + l) (fun p : E × ℝ => φ p.2 • A p.1) (e, ρ)
        (Fin.append (fun i => ((u i, 0) : E × ℝ)) (fun _ : Fin l => ((0, 1) : E × ℝ))) =
      iteratedDeriv l φ ρ • iteratedFDeriv ℝ j A e u
```

## iteratedFDerivWithin (1)

### `iteratedFDerivWithin_comp_equivPerm_of_contDiffOn_of_convex`

`Thm_iteratedFDerivWithin_comp_equivPerm_of_contDiffOn_of_convex` — Symmetry of iterated derivatives within a convex set

```lean
theorem iteratedFDerivWithin_comp_equivPerm_of_contDiffOn_of_convex
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (hs : Convex ℝ s) (hs' : (interior s).Nonempty)
    {n : ℕ} {f : E → F} (hf : ContDiffOn ℝ n f s) {x : E} (hx : x ∈ s)
    (σ : Equiv.Perm (Fin n)) (v : Fin n → E) :
    iteratedFDerivWithin ℝ n f s x (v ∘ σ) = iteratedFDerivWithin ℝ n f s x v
```
