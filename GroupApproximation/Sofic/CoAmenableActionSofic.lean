import GroupApproximation.Sofic.AmenableActionSofic
import GroupApproximation.Sofic.SoficActionChabauty

/-!
# Sections 30.6-30.7: strongly co-amenable subgroups and LERA groups

A subgroup `K ≤ G` is *strongly co-amenable* when `G / core_G(K)` is amenable.
The coset action `G ↷ G/K` then factors through that amenable quotient, so
Lemma 30.6 makes it sofic.  Feeding this into the Chabauty approximation step
already in the repository gives the transitive half of Theorem 30.7: if every
subgroup is approximable by strongly co-amenable subgroups — Gao's LERA
condition, which for a decreasing sequence is exactly Chabauty convergence —
then every transitive action of `G` is sofic.

Finite-index subgroups are strongly co-amenable and every subgroup of an
amenable group is, so both LERF groups and amenable groups are LERA.
-/

namespace GroupApproximation

universe u

variable {G : Type u} [Group G]

/-! ## Quotients of amenable groups -/

/-- Amenability passes to quotients: push the mean forward along the
projection. -/
theorem isAmenable_quotient (hG : Amenability.IsAmenable G) (N : Subgroup G)
    [N.Normal] : Amenability.IsAmenable (G ⧸ N) := by
  obtain ⟨m⟩ := hG
  refine ⟨{
    measure := fun A => m.measure ((QuotientGroup.mk' N) ⁻¹' A)
    nonneg := fun A => m.nonneg _
    measure_univ := by
      rw [Set.preimage_univ]
      exact m.measure_univ
    additive := ?_
    invariant := ?_ }⟩
  · intro A B hAB
    rw [Set.preimage_union]
    refine m.additive _ _ ?_
    rw [Set.disjoint_iff_inter_eq_empty] at hAB ⊢
    rw [← Set.preimage_inter, hAB, Set.preimage_empty]
  · intro q A
    induction q using QuotientGroup.induction_on with
    | _ g =>
      have hpre : (QuotientGroup.mk' N) ⁻¹'
          ((fun y => (QuotientGroup.mk g : G ⧸ N) * y) '' A)
          = (fun y => g * y) '' ((QuotientGroup.mk' N) ⁻¹' A) := by
        ext x
        simp only [Set.mem_preimage, Set.mem_image, ← QuotientGroup.mk'_apply]
        constructor
        · rintro ⟨a, ha, hax⟩
          refine ⟨g⁻¹ * x, ?_, by group⟩
          have hval : (QuotientGroup.mk' N) (g⁻¹ * x) = a := by
            rw [map_mul, map_inv, ← hax]
            group
          rw [hval]
          exact ha
        · rintro ⟨y, hy, rfl⟩
          exact ⟨(QuotientGroup.mk' N) y, hy, by rw [map_mul]⟩
      rw [hpre]
      exact m.invariant g _

/-! ## Actions with an amenable acting quotient -/

variable {X : Type u} [MulAction G X]

/-- **Lemma 30.6, factored form.**  If a normal subgroup acts trivially and the
quotient by it is amenable, the action is sofic. -/
theorem isSoficAction_of_amenable_quotient (N : Subgroup G) [N.Normal]
    (htriv : ∀ n ∈ N, ∀ x : X, n • x = x)
    (hQ : Amenability.IsAmenable (G ⧸ N)) : IsSoficAction G X := by
  refine AmenableActionSofic.isSoficAction_of_amenable_surjHom
    (QuotientGroup.mk' N) ?_ hQ ?_
  · intro q
    induction q using QuotientGroup.induction_on with
    | _ g => exact ⟨g, rfl⟩
  · intro g₁ g₂ hEq x
    have hmem : g₁⁻¹ * g₂ ∈ N := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hEq
      exact QuotientGroup.eq.mp hEq
    calc g₁ • x = g₁ • ((g₁⁻¹ * g₂) • x) := by rw [htriv _ hmem x]
      _ = (g₁ * (g₁⁻¹ * g₂)) • x := (mul_smul _ _ _).symm
      _ = g₂ • x := by group

/-! ## Strongly co-amenable subgroups -/

/-- A subgroup is **strongly co-amenable** when the quotient of the group by its
normal core is amenable. -/
def StronglyCoAmenable (K : Subgroup G) : Prop :=
  Amenability.IsAmenable (G ⧸ K.normalCore)

/-- The normal core acts trivially on the coset space. -/
theorem normalCore_smul_coset (K : Subgroup G) (n : G) (hn : n ∈ K.normalCore)
    (x : G ⧸ K) : n • x = x := by
  induction x using QuotientGroup.induction_on with
  | _ g =>
    rw [MulAction.Quotient.smul_mk, smul_eq_mul]
    refine QuotientGroup.eq.mpr ?_
    have hinv : n⁻¹ ∈ K.normalCore := K.normalCore.inv_mem hn
    have hconj : g⁻¹ * n⁻¹ * (g⁻¹)⁻¹ ∈ K.normalCore :=
      (inferInstance : (K.normalCore).Normal).conj_mem n⁻¹ hinv g⁻¹
    have hK : g⁻¹ * n⁻¹ * g ∈ K := by
      have hmem := K.normalCore_le hconj
      simpa using hmem
    simpa [mul_inv_rev, mul_assoc] using hK

/-- **Section 30.6.**  The coset action of a strongly co-amenable subgroup is
sofic. -/
theorem isSoficAction_quotient_of_stronglyCoAmenable (K : Subgroup G)
    (hK : StronglyCoAmenable K) : IsSoficAction G (G ⧸ K) :=
  isSoficAction_of_amenable_quotient K.normalCore
    (fun n hn x => normalCore_smul_coset K n hn x) hK

/-- The normal core of an intersection is the intersection of the normal
cores: the first half of the closure fact recorded in Section 30.6. -/
theorem normalCore_inf (K₁ K₂ : Subgroup G) :
    (K₁ ⊓ K₂).normalCore = K₁.normalCore ⊓ K₂.normalCore := by
  ext a
  constructor
  · intro h
    have h' : ∀ b : G, b * a * b⁻¹ ∈ K₁ ⊓ K₂ := h
    exact Subgroup.mem_inf.mpr ⟨fun b => (Subgroup.mem_inf.mp (h' b)).1,
      fun b => (Subgroup.mem_inf.mp (h' b)).2⟩
  · intro h
    obtain ⟨h₁, h₂⟩ := Subgroup.mem_inf.mp h
    have h₁' : ∀ b : G, b * a * b⁻¹ ∈ K₁ := h₁
    have h₂' : ∀ b : G, b * a * b⁻¹ ∈ K₂ := h₂
    exact fun b => Subgroup.mem_inf.mpr ⟨h₁' b, h₂' b⟩

/-- In an amenable group every subgroup is strongly co-amenable. -/
theorem stronglyCoAmenable_of_isAmenable (hG : Amenability.IsAmenable G)
    (K : Subgroup G) : StronglyCoAmenable K :=
  isAmenable_quotient hG K.normalCore

/-- Finite-index subgroups are strongly co-amenable: the normal core of a
finite-index subgroup again has finite index, and finite groups are
amenable. -/
theorem stronglyCoAmenable_of_finiteIndex (K : Subgroup G) [K.FiniteIndex] :
    StronglyCoAmenable K := by
  haveI : (K.normalCore).FiniteIndex := inferInstance
  haveI : Finite (G ⧸ K.normalCore) :=
    K.normalCore.finite_quotient_of_finiteIndex
  exact Amenability.isAmenable_of_finite (G ⧸ K.normalCore)

/-! ## LERA groups -/

/-- **Gao's LERA condition**, in the Chabauty form the approximation argument
uses: every subgroup is separated from any prescribed finite set of outside
elements by a strongly co-amenable overgroup.  A decreasing sequence of strongly
co-amenable subgroups with intersection `H`, as in the dossier's definition,
supplies exactly this. -/
def IsLERA (G : Type u) [Group G] : Prop :=
  ∀ (H : Subgroup G) (T : Finset G), ∃ K : Subgroup G, H ≤ K ∧
    (∀ g ∈ T, g ∉ H → g ∉ K) ∧ StronglyCoAmenable K

/-- **Theorem 30.7, transitive case.**  Every transitive action of a LERA group
is sofic. -/
theorem isSoficAction_quotient_of_isLERA (h : IsLERA G) (H : Subgroup G) :
    IsSoficAction G (G ⧸ H) :=
  isSoficAction_quotient_of_approximable H fun T => by
    obtain ⟨K, hHK, hsep, hK⟩ := h H T
    exact ⟨K, hHK, hsep, isSoficAction_quotient_of_stronglyCoAmenable K hK⟩

/-- Amenable groups are LERA: every subgroup is already strongly
co-amenable, so no approximation is needed. -/
theorem isLERA_of_isAmenable (hG : Amenability.IsAmenable G) : IsLERA G :=
  fun H _ => ⟨H, le_refl H, fun _ _ hgH => hgH,
    stronglyCoAmenable_of_isAmenable hG H⟩

end GroupApproximation
