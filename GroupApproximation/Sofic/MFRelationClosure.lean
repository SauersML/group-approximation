import GroupApproximation.Sofic.TorsionCompressionCollapse
import GroupApproximation.Algebra.CountableInstances

/-!
# The MF radical of relations as a closure operator

For a normal subgroup `N` of a countable group `G`, the MF closure of `N`
is the pullback of the literal genuine-corona MF radical of the quotient
`G ⧸ N`.  This file proves that the operation is an extensive, monotone,
idempotent closure operator on normal subgroups; that membership in the
closure is the semantic consequence relation — `x` lies in the closure of
`N` exactly when every corona representation killing `N` kills `x`; that
the fixed points are exactly the normal subgroups with CDE-operator-MF
quotient; that the quotient by any closure is MF; and that the closure of
any subgroup of the radical is the whole radical.

`IsSoundIterate` is the transfinite closure calculus on top of the
operator: subgroups reachable from the trivial subgroup by repeatedly
passing to any subgroup of the MF closure of an already-reached normal
stage — the pullback of any sound rule output in the quotient — and by
arbitrary unions.  Every sound iterate lies in the MF radical; a sound
iterate with MF quotient is exactly the radical; a full sound iterate
makes every homomorphism to an MF group trivial.
-/

namespace GroupApproximation

noncomputable section

universe u

variable {G : Type u} [Group G]

/- Quotients of countable groups are countable.  Proved once as
`GroupApproximation.CountableInstances.quotientCountable` and taken here with
the same `local` scope the mirrored copy had. -/
attribute [local instance] GroupApproximation.CountableInstances.quotientCountable

/-- The MF closure of a normal subgroup: the pullback of the literal
genuine-corona MF radical of the quotient. -/
def actualCoronaMFClosure (N : Subgroup G) [N.Normal] : Subgroup G :=
  (actualCoronaMFResidual (G ⧸ N)).comap (QuotientGroup.mk' N)

instance actualCoronaMFClosure_normal (N : Subgroup G) [N.Normal] :
    (actualCoronaMFClosure N).Normal :=
  actualCoronaMFResidual_normal.comap (QuotientGroup.mk' N)

/-- Semantic membership: `x` lies in the MF closure of `N` exactly when
every genuine-corona representation killing `N` kills `x`. -/
theorem mem_actualCoronaMFClosure_iff :
    ∀ {G : Type u} [Group G] {N : Subgroup G} [N.Normal] {x : G},
      x ∈ actualCoronaMFClosure N ↔
        ∀ (X : ℕ → FiniteModel), ∀ hX : ∀ n, 0 < Fintype.card (X n),
          letI : ∀ n, Nonempty (X n) :=
            fun n ↦ Fintype.card_pos_iff.mp (hX n)
          ∀ rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
            (∀ y ∈ N, rho y = 1) → rho x = 1 := by
  intro G _ N _ x
  constructor
  · intro hx X hX
    letI : ∀ n, Nonempty (X n) := fun n ↦ Fintype.card_pos_iff.mp (hX n)
    intro rho hkill
    have hker : N ≤ rho.ker := fun y hy ↦ MonoidHom.mem_ker.mpr (hkill y hy)
    have hq := (Subgroup.mem_comap.mp hx) X hX (QuotientGroup.lift N rho hker)
    simpa using hq
  · intro hx
    refine Subgroup.mem_comap.mpr ?_
    intro X hX
    letI : ∀ n, Nonempty (X n) := fun n ↦ Fintype.card_pos_iff.mp (hX n)
    intro sigma
    have hkill : ∀ y ∈ N, (sigma.comp (QuotientGroup.mk' N)) y = 1 := by
      intro y hy
      have h1 : (QuotientGroup.mk' N) y = 1 :=
        (QuotientGroup.eq_one_iff y).mpr hy
      rw [MonoidHom.comp_apply, h1, map_one]
    simpa using hx X hX (sigma.comp (QuotientGroup.mk' N)) hkill

/-- Extensive: the relations lie inside their own closure. -/
theorem le_actualCoronaMFClosure (N : Subgroup G) [N.Normal] :
    N ≤ actualCoronaMFClosure N := by
  intro y hy
  refine Subgroup.mem_comap.mpr ?_
  have h1 : (QuotientGroup.mk' N) y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
  rw [h1]
  exact one_mem _

/-- The MF radical lies inside the closure of every normal subgroup. -/
theorem actualCoronaMFResidual_le_actualCoronaMFClosure
    (N : Subgroup G) [N.Normal] :
    actualCoronaMFResidual G ≤ actualCoronaMFClosure N := by
  intro x hx
  rw [mem_actualCoronaMFClosure_iff]
  intro X hX
  letI : ∀ n, Nonempty (X n) := fun n ↦ Fintype.card_pos_iff.mp (hX n)
  intro rho _
  exact hx X hX rho

/-- Monotone: enlarging the relations enlarges the closure. -/
theorem actualCoronaMFClosure_mono {N₁ N₂ : Subgroup G} [N₁.Normal]
    [N₂.Normal] (h : N₁ ≤ N₂) :
    actualCoronaMFClosure N₁ ≤ actualCoronaMFClosure N₂ := by
  intro x hx
  rw [mem_actualCoronaMFClosure_iff] at hx ⊢
  intro X hX
  letI : ∀ n, Nonempty (X n) := fun n ↦ Fintype.card_pos_iff.mp (hX n)
  intro rho hkill
  exact hx X hX rho fun y hy ↦ hkill y (h hy)

/-- Idempotent: the closure is closed. -/
theorem actualCoronaMFClosure_idem (N : Subgroup G) [N.Normal] :
    actualCoronaMFClosure (actualCoronaMFClosure N) =
      actualCoronaMFClosure N := by
  refine le_antisymm ?_ (le_actualCoronaMFClosure _)
  intro x hx
  rw [mem_actualCoronaMFClosure_iff] at hx ⊢
  intro X hX
  letI : ∀ n, Nonempty (X n) := fun n ↦ Fintype.card_pos_iff.mp (hX n)
  intro rho hkill
  refine hx X hX rho ?_
  intro y hy
  rw [mem_actualCoronaMFClosure_iff] at hy
  exact hy X hX rho hkill

/-- The closure of a subgroup of the radical is the whole radical. -/
theorem actualCoronaMFClosure_eq_residual_of_le (N : Subgroup G) [N.Normal]
    (hN : N ≤ actualCoronaMFResidual G) :
    actualCoronaMFClosure N = actualCoronaMFResidual G := by
  have h :=
    TorsionCompressionCollapse.actualCoronaMFResidual_eq_comap_quotient N hN
  exact h.symm

/-- The fixed points of the closure operator are exactly the normal
subgroups with CDE-operator-MF quotient. -/
theorem actualCoronaMFClosure_eq_self_iff [Countable G] (N : Subgroup G)
    [N.Normal] :
    actualCoronaMFClosure N = N ↔ IsCDEOperatorMF (G ⧸ N) := by
  constructor
  · intro h
    have hmap : (actualCoronaMFClosure N).map (QuotientGroup.mk' N) =
        actualCoronaMFResidual (G ⧸ N) :=
      Subgroup.map_comap_eq_self_of_surjective
        (QuotientGroup.mk'_surjective N) _
    rw [h] at hmap
    have hbot : actualCoronaMFResidual (G ⧸ N) = ⊥ := by
      rw [← hmap]
      refine le_antisymm ?_ bot_le
      rintro _ ⟨x, hx, rfl⟩
      simpa [Subgroup.mem_bot] using (QuotientGroup.eq_one_iff x).mpr hx
    exact isCDEOperatorMF_iff_actualCoronaMFResidual_eq_bot.mpr hbot
  · intro h
    have hbot : actualCoronaMFResidual (G ⧸ N) = ⊥ :=
      isCDEOperatorMF_iff_actualCoronaMFResidual_eq_bot.mp h
    show (actualCoronaMFResidual (G ⧸ N)).comap (QuotientGroup.mk' N) = N
    rw [hbot]
    ext x
    simp

/-- The quotient by any MF closure is MF. -/
theorem isCDEOperatorMF_quotient_actualCoronaMFClosure [Countable G]
    (N : Subgroup G) [N.Normal] :
    IsCDEOperatorMF (G ⧸ actualCoronaMFClosure N) := by
  have hmap : (actualCoronaMFClosure N).map (QuotientGroup.mk' N) =
      actualCoronaMFResidual (G ⧸ N) :=
    Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective N) _
  haveI hnormal :
      ((actualCoronaMFClosure N).map (QuotientGroup.mk' N)).Normal := by
    rw [hmap]
    infer_instance
  let e₁ :=
    QuotientGroup.quotientQuotientEquivQuotient N (actualCoronaMFClosure N)
      (le_actualCoronaMFClosure N)
  let e₂ : ((G ⧸ N) ⧸ (actualCoronaMFClosure N).map (QuotientGroup.mk' N))
      ≃* ((G ⧸ N) ⧸ actualCoronaMFResidual (G ⧸ N)) :=
    QuotientGroup.quotientMulEquivOfEq hmap
  obtain ⟨d, hd, hmono, rho, hrho⟩ :=
    actualCoronaMFQuotient_isCDEOperatorMF (G := G ⧸ N)
  exact ⟨d, hd, hmono, rho.comp (e₂.toMonoidHom.comp e₁.symm.toMonoidHom),
    hrho.comp (e₂.injective.comp e₁.symm.injective)⟩

/-! ## The sound-iteration closure calculus -/

/-- Subgroups reachable from the trivial subgroup by iterating sound
radical rules and passing to arbitrary unions.  A sound rule applied over
an already-reached normal stage `N` may output any subgroup of the MF
closure of `N` — exactly the pullback of any subgroup of the MF radical of
`G ⧸ N`. -/
inductive IsSoundIterate : Subgroup G → Prop
  | bot : IsSoundIterate ⊥
  | closure_step (N M : Subgroup G) (hN : N.Normal)
      (hiter : IsSoundIterate N)
      (hM : M ≤ @actualCoronaMFClosure G _ N hN) : IsSoundIterate M
  | union (S : Set (Subgroup G)) (hS : ∀ N ∈ S, IsSoundIterate N) :
      IsSoundIterate (sSup S)

/-- **Soundness of the iteration.**  Every sound iterate lies in the
literal MF radical. -/
theorem IsSoundIterate.le_actualCoronaMFResidual {N : Subgroup G}
    (h : IsSoundIterate N) : N ≤ actualCoronaMFResidual G := by
  induction h with
  | bot => exact bot_le
  | closure_step N M hN hiter hM ih =>
      haveI := hN
      exact hM.trans (actualCoronaMFClosure_eq_residual_of_le N ih).le
  | union S hS ih => exact sSup_le ih

/-- **Completeness criterion.**  A sound iterate whose quotient is MF is
exactly the MF radical. -/
theorem IsSoundIterate.residual_eq_of_quotient_isCDEOperatorMF [Countable G]
    {N : Subgroup G} [N.Normal] (h : IsSoundIterate N)
    (hquot : IsCDEOperatorMF (G ⧸ N)) :
    actualCoronaMFResidual G = N := by
  refine le_antisymm ?_ h.le_actualCoronaMFResidual
  intro x hx
  have hres : (QuotientGroup.mk' N) x ∈ actualCoronaMFResidual (G ⧸ N) :=
    map_actualCoronaMFResidual_le (QuotientGroup.mk' N) ⟨x, hx, rfl⟩
  have hbot : actualCoronaMFResidual (G ⧸ N) = ⊥ :=
    isCDEOperatorMF_iff_actualCoronaMFResidual_eq_bot.mp hquot
  rw [hbot] at hres
  exact (QuotientGroup.eq_one_iff x).mp (Subgroup.mem_bot.mp hres)

/-- **Saturation.**  A full sound iterate makes the radical everything. -/
theorem IsSoundIterate.residual_eq_top
    (h : IsSoundIterate (⊤ : Subgroup G)) :
    actualCoronaMFResidual G = ⊤ :=
  top_unique h.le_actualCoronaMFResidual

/-! ## Manuscript wrappers -/

/-- Closed form of the manuscript's relation-closure proposition: the MF
closure is an extensive, monotone, idempotent closure operator on normal
subgroups; it is the pullback of the manuscript radical of the quotient;
its fixed points are exactly the normal subgroups with MF quotient; and
the quotient by any closure is MF. -/
theorem manuscriptRelationClosure :
    ∀ (G : Type u) [Group G] [Countable G] (N : Subgroup G) [N.Normal],
      (N ≤ actualCoronaMFClosure N) ∧
        actualCoronaMFClosure N =
          (manuscriptCoronaMFResidual (G ⧸ N)).comap
            (QuotientGroup.mk' N) ∧
        (∀ (M : Subgroup G) [M.Normal], N ≤ M →
          actualCoronaMFClosure N ≤ actualCoronaMFClosure M) ∧
        actualCoronaMFClosure (actualCoronaMFClosure N) =
          actualCoronaMFClosure N ∧
        (actualCoronaMFClosure N = N ↔ IsCDEOperatorMF (G ⧸ N)) ∧
        IsCDEOperatorMF (G ⧸ actualCoronaMFClosure N) := by
  intro G _ _ N _
  refine ⟨le_actualCoronaMFClosure N, ?_, ?_,
    actualCoronaMFClosure_idem N, actualCoronaMFClosure_eq_self_iff N,
    isCDEOperatorMF_quotient_actualCoronaMFClosure N⟩
  · show (actualCoronaMFResidual (G ⧸ N)).comap (QuotientGroup.mk' N) =
        (manuscriptCoronaMFResidual (G ⧸ N)).comap (QuotientGroup.mk' N)
    rw [manuscriptCoronaMFResidual_eq_actualCoronaMFResidual]
  · intro M _ hNM
    exact actualCoronaMFClosure_mono hNM

/-- Closed form of the sound-iteration closure: every sound iterate lies
in the manuscript MF radical; a sound iterate with MF quotient is exactly
the radical; a full sound iterate makes the radical everything. -/
theorem manuscriptSoundIterationClosure :
    ∀ (G : Type u) [Group G] [Countable G],
      (∀ N : Subgroup G, IsSoundIterate N →
        N ≤ manuscriptCoronaMFResidual G) ∧
        (∀ (N : Subgroup G) [N.Normal], IsSoundIterate N →
          IsCDEOperatorMF (G ⧸ N) → manuscriptCoronaMFResidual G = N) ∧
        (IsSoundIterate (⊤ : Subgroup G) →
          manuscriptCoronaMFResidual G = ⊤) := by
  intro G _ _
  refine ⟨?_, ?_, ?_⟩
  · intro N h
    rw [manuscriptCoronaMFResidual_eq_actualCoronaMFResidual]
    exact h.le_actualCoronaMFResidual
  · intro N _ h hquot
    rw [manuscriptCoronaMFResidual_eq_actualCoronaMFResidual]
    exact h.residual_eq_of_quotient_isCDEOperatorMF hquot
  · intro h
    rw [manuscriptCoronaMFResidual_eq_actualCoronaMFResidual]
    exact h.residual_eq_top

end

end GroupApproximation
