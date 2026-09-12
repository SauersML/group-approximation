import GroupApproximation.Algebra.FiniteResidual

/-!
# Finite-target rigidity of a quotient by a subgroup of the finite residual

Section 48 of the ascending-HNN dossier, in its abstract group-theoretic form.

A surjection `q : W →* P` whose kernel lies inside `finiteResidual W` cannot be detected by any
finite object.  The reason is a single containment: a finite-index subgroup of `W` contains the
whole finite residual, hence contains `ker q`, hence is a preimage.  The correspondence theorem
for a quotient normally applies only to the subgroups containing the kernel; here that condition
is automatic for *every* finite-index subgroup, normal or not, so the correspondence covers the
entire finite-index lattice.  Consequently `q` matches up finite-index subgroups on the two sides
in an inclusion-preserving, index-preserving, normality-preserving way, and every homomorphism
from `W` into a finite group descends uniquely along `q`.  The two groups therefore have the same
finite-index subgroups, the same subgroup-counting sequences, the same finite quotients and the
same finite permutation actions, while `ker q` — possibly a large and interesting subgroup — is
invisible to all of it.

Mathlib has no profinite completion of an abstract group, so the completion-level assertions of
Theorem 48.2 and Proposition 48.5 are stated here one level down, at the finite quotients and
finite actions themselves: `existsUnique_descend` and `homEquiv` say that inflation along `q` is
a bijection on homomorphisms into any finite group, `equivariant_iff` supplies the morphism half
of the equivalence of finite-action categories, and `finiteResidual_eq_ker` identifies the kernel
with the closure of the identity in the profinite topology whenever the target is residually
finite.  This is exactly the finite data an inverse limit is built from, so no strength is lost;
only the limit itself is not formed.
-/

namespace GroupApproximation

namespace FiniteIndexRigidity

variable {W : Type*} [Group W] {P : Type*} [Group P] (q : W →* P)

/-! ## The kernel is contained in every finite-index subgroup -/

/-- The containment that drives the whole section: if the kernel of `q` lies in the finite
residual of `W`, then it lies in every finite-index subgroup of `W`, whether or not that subgroup
is normal.  Everything below is the correspondence theorem applied to this observation. -/
theorem ker_le_of_finiteIndex (hker : q.ker ≤ finiteResidual W) (L : Subgroup W)
    [L.FiniteIndex] : q.ker ≤ L := by
  rw [SetLike.le_def]
  intro x hx
  exact mem_finiteResidual_iff.mp (hker hx) L inferInstance

/-- A homomorphism into a finite group kills the finite residual, since its kernel already has
finite index. -/
theorem finiteResidual_le_ker {F : Type*} [Group F] [Finite F] (φ : W →* F) :
    finiteResidual W ≤ φ.ker := by
  rw [SetLike.le_def]
  intro x hx
  exact mem_finiteResidual_iff.mp hx φ.ker inferInstance

/-- Combining the two previous facts: the kernel of `q` is contained in the kernel of every
homomorphism from `W` to a finite group. -/
theorem ker_le_ker_of_finite (hker : q.ker ≤ finiteResidual W) {F : Type*} [Group F] [Finite F]
    (φ : W →* F) : q.ker ≤ φ.ker :=
  hker.trans (finiteResidual_le_ker φ)

/-! ## The finite-index lattices are identified -/

/-- Every finite-index subgroup of `W` is recovered from its image: this is the correspondence
theorem, licensed for a non-normal subgroup by `ker_le_of_finiteIndex`. -/
theorem comap_map_of_finiteIndex (hker : q.ker ≤ finiteResidual W) (L : Subgroup W)
    [L.FiniteIndex] : (L.map q).comap q = L :=
  Subgroup.comap_map_eq_self (ker_le_of_finiteIndex q hker L)

/-- Every subgroup of `P` is recovered from its preimage, by surjectivity alone. -/
theorem map_comap_of_surjective (hq : Function.Surjective q) (M : Subgroup P) :
    (M.comap q).map q = M :=
  Subgroup.map_comap_eq_self_of_surjective hq M

/-- Membership in the image of a finite-index subgroup is detected before pushing forward. -/
theorem mem_map_iff (hker : q.ker ≤ finiteResidual W) (L : Subgroup W) [L.FiniteIndex] (x : W) :
    q x ∈ L.map q ↔ x ∈ L := by
  constructor
  · intro h
    rwa [← comap_map_of_finiteIndex q hker L, Subgroup.mem_comap]
  · intro h
    exact Subgroup.mem_map_of_mem q h

/-- Taking preimages along a surjection preserves the index exactly. -/
theorem index_comap_eq (hq : Function.Surjective q) (M : Subgroup P) :
    (M.comap q).index = M.index :=
  M.index_comap_of_surjective hq

/-- Preimages of finite-index subgroups have finite index. -/
theorem finiteIndex_comap (hq : Function.Surjective q) (M : Subgroup P) [M.FiniteIndex] :
    (M.comap q).FiniteIndex := by
  refine ⟨?_⟩
  rw [index_comap_eq q hq M]
  exact Subgroup.FiniteIndex.index_ne_zero

/-- Equation (48.4): the image of a finite-index subgroup has the same index.  Concretely, the
quotient map induces a bijection of coset spaces `W / L → P / q(L)`. -/
theorem index_map_eq (hq : Function.Surjective q) (hker : q.ker ≤ finiteResidual W)
    (L : Subgroup W) [L.FiniteIndex] : (L.map q).index = L.index :=
  L.index_map_eq hq (ker_le_of_finiteIndex q hker L)

/-- Images of finite-index subgroups have finite index. -/
theorem finiteIndex_map (hq : Function.Surjective q) (hker : q.ker ≤ finiteResidual W)
    (L : Subgroup W) [L.FiniteIndex] : (L.map q).FiniteIndex := by
  refine ⟨?_⟩
  rw [index_map_eq q hq hker L]
  exact Subgroup.FiniteIndex.index_ne_zero

/-- **Theorem 48.1**, the bijection (48.2)–(48.3).  Pushing forward along `q` and pulling back
along `q` are mutually inverse bijections between the finite-index subgroups of `W` and those of
`P`.  Inclusion, index and normality are preserved by the lemmas that follow. -/
def latticeEquiv (hq : Function.Surjective q) (hker : q.ker ≤ finiteResidual W) :
    {L : Subgroup W // L.FiniteIndex} ≃ {M : Subgroup P // M.FiniteIndex} where
  toFun L := ⟨L.1.map q, by haveI := L.2; exact finiteIndex_map q hq hker L.1⟩
  invFun M := ⟨M.1.comap q, by haveI := M.2; exact finiteIndex_comap q hq M.1⟩
  left_inv L := by
    refine Subtype.ext ?_
    haveI := L.2
    exact comap_map_of_finiteIndex q hker L.1
  right_inv M := Subtype.ext (map_comap_of_surjective q hq M.1)

/-- The forward direction of `latticeEquiv` is the pushforward. -/
@[simp] theorem latticeEquiv_coe (hq : Function.Surjective q) (hker : q.ker ≤ finiteResidual W)
    (L : {L : Subgroup W // L.FiniteIndex}) : (latticeEquiv q hq hker L : Subgroup P) =
      L.1.map q :=
  rfl

/-- The inverse direction of `latticeEquiv` is the pullback. -/
@[simp] theorem latticeEquiv_symm_coe (hq : Function.Surjective q) (hker : q.ker ≤ finiteResidual W)
    (M : {M : Subgroup P // M.FiniteIndex}) :
    ((latticeEquiv q hq hker).symm M : Subgroup W) = M.1.comap q :=
  rfl

/-- The correspondence preserves inclusions in both directions. -/
theorem map_le_map_iff (hker : q.ker ≤ finiteResidual W) (L₁ L₂ : Subgroup W) [L₁.FiniteIndex]
    [L₂.FiniteIndex] : L₁.map q ≤ L₂.map q ↔ L₁ ≤ L₂ := by
  constructor
  · intro h
    have h' := Subgroup.comap_mono (f := q) h
    rwa [comap_map_of_finiteIndex q hker L₁, comap_map_of_finiteIndex q hker L₂] at h'
  · exact Subgroup.map_mono

/-- Pulling back along a surjection reflects and preserves inclusions. -/
theorem comap_le_comap_iff (hq : Function.Surjective q) (M₁ M₂ : Subgroup P) :
    M₁.comap q ≤ M₂.comap q ↔ M₁ ≤ M₂ :=
  Subgroup.comap_le_comap_of_surjective hq

/-- Equation (48.5): the correspondence preserves normality. -/
theorem normal_map_iff (hq : Function.Surjective q) (hker : q.ker ≤ finiteResidual W)
    (L : Subgroup W) [L.FiniteIndex] : (L.map q).Normal ↔ L.Normal := by
  constructor
  · intro h
    rw [← comap_map_of_finiteIndex q hker L]
    exact h.comap q
  · intro h
    exact h.map q hq

/-- Normality is likewise reflected by pullback along a surjection. -/
theorem normal_comap_iff (hq : Function.Surjective q) (M : Subgroup P) :
    (M.comap q).Normal ↔ M.Normal :=
  Subgroup.normal_comap_iff_of_surjective hq

/-- Every finite-index normal subgroup of `W` is the preimage of a finite-index normal subgroup
of `P`.  This is the statement that the profinite topology of `W` is pulled back from `P`: the two
neighbourhood bases of the identity correspond. -/
theorem exists_normal_comap_eq (hq : Function.Surjective q) (hker : q.ker ≤ finiteResidual W)
    (L : Subgroup W) [L.FiniteIndex] [L.Normal] :
    ∃ M : Subgroup P, M.Normal ∧ M.FiniteIndex ∧ M.comap q = L :=
  ⟨L.map q, Subgroup.Normal.map ‹L.Normal› q hq, finiteIndex_map q hq hker L,
    comap_map_of_finiteIndex q hker L⟩

/-- **Proposition 48.5**, equation (48.8): if the target is residually finite then the kernel is
exactly the finite residual, that is, exactly the closure of the identity in the profinite
topology.  So `P` is the Hausdorff reflection of `W` for that topology. -/
theorem finiteResidual_eq_ker (hker : q.ker ≤ finiteResidual W) (hP : IsResiduallyFinite P) :
    finiteResidual W = q.ker := by
  have hP' : finiteResidual P = ⊥ := hP
  refine le_antisymm ?_ hker
  rw [SetLike.le_def]
  intro x hx
  rw [MonoidHom.mem_ker]
  have h : q x ∈ finiteResidual P := map_finiteResidual_le q ⟨x, hx, rfl⟩
  rwa [hP', Subgroup.mem_bot] at h

/-! ## Subgroup growth -/

/-- **Corollary 48.4**, the bijection behind `a_n(W) = a_n(P)`: for each nonzero `n`, the
subgroups of index `n` correspond. -/
def indexEquiv (hq : Function.Surjective q) (hker : q.ker ≤ finiteResidual W) {n : ℕ}
    (hn : n ≠ 0) : {L : Subgroup W // L.index = n} ≃ {M : Subgroup P // M.index = n} where
  toFun L := ⟨L.1.map q, by
    haveI : L.1.FiniteIndex := ⟨by rw [L.2]; exact hn⟩
    rw [index_map_eq q hq hker L.1, L.2]⟩
  invFun M := ⟨M.1.comap q, by rw [index_comap_eq q hq M.1, M.2]⟩
  left_inv L := by
    refine Subtype.ext ?_
    haveI : L.1.FiniteIndex := ⟨by rw [L.2]; exact hn⟩
    exact comap_map_of_finiteIndex q hker L.1
  right_inv M := Subtype.ext (map_comap_of_surjective q hq M.1)

/-- The same bijection restricted to normal subgroups, which is the second half of (48.7). -/
def normalIndexEquiv (hq : Function.Surjective q) (hker : q.ker ≤ finiteResidual W) {n : ℕ}
    (hn : n ≠ 0) :
    {L : Subgroup W // L.index = n ∧ L.Normal} ≃ {M : Subgroup P // M.index = n ∧ M.Normal} where
  toFun L := ⟨L.1.map q, by
    haveI : L.1.FiniteIndex := ⟨by rw [L.2.1]; exact hn⟩
    exact ⟨by rw [index_map_eq q hq hker L.1, L.2.1], Subgroup.Normal.map L.2.2 q hq⟩⟩
  invFun M := ⟨M.1.comap q, by
    exact ⟨by rw [index_comap_eq q hq M.1, M.2.1], M.2.2.comap q⟩⟩
  left_inv L := by
    refine Subtype.ext ?_
    haveI : L.1.FiniteIndex := ⟨by rw [L.2.1]; exact hn⟩
    exact comap_map_of_finiteIndex q hker L.1
  right_inv M := Subtype.ext (map_comap_of_surjective q hq M.1)

/-- Equation (48.7) for all subgroups: the two groups have the same number of subgroups of each
finite index. -/
theorem card_index_eq (hq : Function.Surjective q) (hker : q.ker ≤ finiteResidual W) {n : ℕ}
    (hn : n ≠ 0) : Nat.card {L : Subgroup W // L.index = n} =
      Nat.card {M : Subgroup P // M.index = n} :=
  Nat.card_congr (indexEquiv q hq hker hn)

/-- Equation (48.7) for normal subgroups. -/
theorem card_normal_index_eq (hq : Function.Surjective q) (hker : q.ker ≤ finiteResidual W)
    {n : ℕ} (hn : n ≠ 0) : Nat.card {L : Subgroup W // L.index = n ∧ L.Normal} =
      Nat.card {M : Subgroup P // M.index = n ∧ M.Normal} :=
  Nat.card_congr (normalIndexEquiv q hq hker hn)

/-! ## Conjugacy classes of finite-index subgroups -/

/-- **Corollary 48.3**(2).  Two finite-index subgroups of `W` are conjugate exactly when their
images in `P` are, so the correspondence descends to conjugacy classes.  Conjugacy is written
out on elements to keep the statement free of the automorphism calculus. -/
theorem conj_mem_iff (hq : Function.Surjective q) (hker : q.ker ≤ finiteResidual W)
    (L₁ L₂ : Subgroup W) [L₁.FiniteIndex] [L₂.FiniteIndex] :
    (∃ w : W, ∀ x : W, x ∈ L₂ ↔ w * x * w⁻¹ ∈ L₁) ↔
      ∃ p : P, ∀ y : P, y ∈ L₂.map q ↔ p * y * p⁻¹ ∈ L₁.map q := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨q w, fun y => ?_⟩
    obtain ⟨x, rfl⟩ := hq y
    rw [mem_map_iff q hker L₂ x, show q w * q x * (q w)⁻¹ = q (w * x * w⁻¹) by simp,
      mem_map_iff q hker L₁]
    exact hw x
  · rintro ⟨p, hp⟩
    obtain ⟨w, rfl⟩ := hq p
    refine ⟨w, fun x => ?_⟩
    have h := hp (q x)
    rwa [mem_map_iff q hker L₂ x, show q w * q x * (q w)⁻¹ = q (w * x * w⁻¹) by simp,
      mem_map_iff q hker L₁] at h

/-! ## Finite quotients and finite actions -/

/-- Inflation along a surjection is injective on homomorphisms. -/
theorem comp_injective (hq : Function.Surjective q) {F : Type*} [Group F] :
    Function.Injective fun ψ : P →* F => ψ.comp q := by
  intro ψ₁ ψ₂ h
  ext p
  obtain ⟨w, rfl⟩ := hq p
  have h' := DFunLike.congr_fun h w
  simpa using h'

/-- Inflation along `q` is surjective onto the homomorphisms into any finite group: such a
homomorphism kills the finite residual, hence kills `ker q`, hence factors. -/
theorem comp_surjective (hq : Function.Surjective q) (hker : q.ker ≤ finiteResidual W)
    {F : Type*} [Group F] [Finite F] :
    Function.Surjective fun ψ : P →* F => ψ.comp q := fun φ =>
  ⟨q.liftOfSurjective hq ⟨φ, ker_le_ker_of_finite q hker φ⟩, q.liftOfRightInverse_comp _ _ _⟩

/-- **Theorem 48.2** at the level of finite quotients: precomposition with `q` is a bijection
`Hom(P, F) → Hom(W, F)` for every finite group `F`.  This is the finite data from which the
profinite completion is assembled, so it is the statement `Ŵ ≅ P̂` with the inverse limit left
unformed. -/
theorem comp_bijective (hq : Function.Surjective q) (hker : q.ker ≤ finiteResidual W)
    {F : Type*} [Group F] [Finite F] : Function.Bijective fun ψ : P →* F => ψ.comp q :=
  ⟨comp_injective q hq, comp_surjective q hq hker⟩

/-- The bijection of the previous theorem, packaged as an equivalence. -/
noncomputable def homEquiv (hq : Function.Surjective q) (hker : q.ker ≤ finiteResidual W)
    (F : Type*) [Group F] [Finite F] : (P →* F) ≃ (W →* F) :=
  Equiv.ofBijective _ (comp_bijective q hq hker)

/-- `homEquiv` is inflation along `q`. -/
@[simp] theorem homEquiv_apply (hq : Function.Surjective q) (hker : q.ker ≤ finiteResidual W)
    (F : Type*) [Group F] [Finite F] (ψ : P →* F) : homEquiv q hq hker F ψ = ψ.comp q :=
  rfl

/-- Every homomorphism from `W` to a finite group descends **uniquely** through `q`. -/
theorem existsUnique_descend (hq : Function.Surjective q) (hker : q.ker ≤ finiteResidual W)
    {F : Type*} [Group F] [Finite F] (φ : W →* F) : ∃! ψ : P →* F, ψ.comp q = φ := by
  obtain ⟨ψ, hψ⟩ := comp_surjective q hq hker φ
  exact ⟨ψ, hψ, fun ψ' hψ' => comp_injective q hq (hψ'.trans hψ.symm)⟩

/-- **Theorem 48.2** for actions: every action of `W` on a finite set, presented by its
permutation homomorphism, factors uniquely through `P`. -/
theorem existsUnique_descend_perm (hq : Function.Surjective q) (hker : q.ker ≤ finiteResidual W)
    {Ω : Type*} [Finite Ω] (ρ : W →* Equiv.Perm Ω) :
    ∃! ρ' : P →* Equiv.Perm Ω, ρ'.comp q = ρ :=
  existsUnique_descend q hq hker ρ

/-- The morphism half of the equivalence (48.6): a map between two descended finite actions is
`W`-equivariant if and only if it is `P`-equivariant.  Only surjectivity of `q` is used, so
inflation is fully faithful before any residual hypothesis enters. -/
theorem equivariant_iff (hq : Function.Surjective q) {Ω : Type*} {Λ : Type*}
    (ρ : P →* Equiv.Perm Ω) (σ : P →* Equiv.Perm Λ) (f : Ω → Λ) :
    (∀ w : W, ∀ x : Ω, f ((ρ.comp q) w x) = (σ.comp q) w (f x)) ↔
      ∀ p : P, ∀ x : Ω, f (ρ p x) = σ p (f x) := by
  constructor
  · intro h p x
    obtain ⟨w, rfl⟩ := hq p
    exact h w x
  · intro h w x
    exact h (q w) x

end FiniteIndexRigidity

end GroupApproximation
