import GroupApproximation.Higman.PinchGraph
import GroupApproximation.Higman.BenignClosure

/-!
# The Higman rope trick

Higman's Lemma: for `N ⊴ F` with `F` finitely generated, `F ⧸ N` embeds in a
finitely presented group **iff** `N` is benign in `F`.  The easy direction is
`Higman.BenignWitness.ker`.  This file is the other one, the *rope trick*.

## The construction

Let `K` be a finitely presented overgroup of `F` and `L ≤ K` finitely
generated with `F ∩ L = N`.  Write `A ≤ K` for the image of `F`.

1. `Γ := K ∗_L t`, the HNN extension whose stable letter centralizes `L`.  It
   is finitely presented, and inside it `A ∩ Aᵗ = A ∩ L = N`.
2. `S := ⟨A, Aᵗ⟩ ≤ Γ`, and `τ : S → F ⧸ N` the homomorphism which is the
   quotient map on `A` and trivial on `Aᵗ` --- it exists by
   `Higman.Pinch.tauHom`, and that is exactly where the pinch machinery is
   used: `S` is the free product of `A` and `Aᵗ` amalgamated over `N`, and
   `τ` is the map that only such a decomposition can define.
3. `D := Γ × (F ⧸ N)`, and one more stable letter `e` conjugating `S × 1`
   onto the graph `{(s, τ s) : s ∈ S}`.  The resulting group is
   `RopeGroup`.

`F ⧸ N` sits inside `RopeGroup` as `1 × (F ⧸ N) ≤ D`, because the base of an
HNN extension embeds.  That is `quotient_injective` below.

## Why the result is finitely presented

`D` is not known to be finitely presented --- `F ⧸ N` is the group whose
presentation is the problem.  The trick is that the relations of `F ⧸ N`
become *derivable* from the finitely many relations of the rest.  Writing
`x̄` for the image of `x ∈ F` in `F ⧸ N`, the stable letter satisfies

    e · (ι x, 1) · e⁻¹ = (ι x, x̄),        e · ((ι x)ᵗ, 1) · e⁻¹ = ((ι x)ᵗ, 1),

and both are relations on *generators* of `F` only.  For `n ∈ N` we have
`ι n ∈ L`, so `(ι n)ᵗ = ι n` in `Γ`, and the two displayed relations then
force `(ι n, n̄) = (ι n, 1)`, that is `n̄ = 1`.  So every relation of `F ⧸ N`
follows from finitely many relations, and the group is finitely presented.
-/

namespace GroupApproximation
namespace Higman
namespace Rope

open HNNExtension

variable {F : Type} [Group F] {N : Subgroup F} [N.Normal] (w : BenignWitness N)

/-! ## 1.  The first extension -/

/-- The image of `F` in the finitely presented overgroup. -/
def Aemb : Subgroup w.K := (⊤ : Subgroup F).map w.emb

/-- The first HNN extension: the stable letter centralizes `L`. -/
abbrev Gamma : Type := CentHNN w.L

theorem isFinitelyPresented_gamma : Group.IsFinitelyPresented (Gamma w) :=
  isFinitelyPresented_centHNN w.L w.L_fg

/-- `F`, as a subgroup of the overgroup, is a copy of `F`. -/
noncomputable def aembEquiv : F ≃* ↥(Aemb w) :=
  (Subgroup.topEquiv (G := F)).symm.trans
    (Subgroup.equivMapOfInjective (⊤ : Subgroup F) w.emb w.emb_injective)

theorem coe_aembEquiv (x : F) : ((aembEquiv w x : ↥(Aemb w)) : w.K) = w.emb x := by
  show ((Subgroup.equivMapOfInjective (⊤ : Subgroup F) w.emb w.emb_injective)
    ((Subgroup.topEquiv (G := F)).symm x) : w.K) = _
  rw [Subgroup.coe_equivMapOfInjective_apply]
  rfl

/-- The value map: the quotient map `F → F ⧸ N`, read on the image of `F`. -/
noncomputable def phi : ↥(Aemb w) →* F ⧸ N :=
  (QuotientGroup.mk' N).comp (aembEquiv w).symm.toMonoidHom

theorem phi_apply (x : F) : phi w (aembEquiv w x) = QuotientGroup.mk' N x := by
  unfold phi
  rw [MonoidHom.comp_apply]
  congr 1
  exact (aembEquiv w).symm_apply_apply x

/-- **The value map kills what the pinch lemma needs it to kill.**  An element
of `F` whose image lies in `L` lies in `N`, by the defining property of the
benign witness, and the quotient map kills `N`. -/
theorem phi_kills (x : ↥(Aemb w)) (hx : (x : w.K) ∈ w.L) : phi w x = 1 := by
  obtain ⟨y, -, hy⟩ := x.2
  have hxy : (aembEquiv w y) = x := by
    refine Subtype.ext ?_
    rw [coe_aembEquiv]
    exact hy
  have hyN : y ∈ N := by
    have : y ∈ w.L.comap w.emb := by
      refine Subgroup.mem_comap.mpr ?_
      rw [hy]
      exact hx
    rwa [w.comap_eq] at this
  rw [← hxy, phi_apply]
  exact (QuotientGroup.eq_one_iff y).mpr hyN

/-! ## 2.  The subgroup `⟨A, Aᵗ⟩` and the homomorphism on it -/

/-- `⟨A, Aᵗ⟩`, the subgroup the last stable letter acts on. -/
abbrev Sub : Subgroup (Gamma w) :=
  Subgroup.closure (Pinch.genSet w.L (Aemb w) (Aemb w))

/-- **The homomorphism the rope trick runs on.**  The quotient map on `A`,
trivial on `Aᵗ`. -/
noncomputable def tau : ↥(Sub w) →* F ⧸ N :=
  Pinch.tauHom w.L (Aemb w) (phi w) (phi_kills w)

/-! ## 3.  The second extension -/

/-- The ambient of the last step. -/
abbrev Amb : Type := Gamma w × (F ⧸ N)

/-- `S × 1`. -/
def AeSub : Subgroup (Amb w) :=
  (Sub w).map (MonoidHom.inl (Gamma w) (F ⧸ N))

/-- The graph of `τ`. -/
noncomputable def BeSub : Subgroup (Amb w) :=
  Pinch.blockGraph w.L (Aemb w) (phi w)

/-- `S × 1` is a copy of `S`. -/
noncomputable def aeSubEquiv : ↥(Sub w) ≃* ↥(AeSub w) :=
  Subgroup.equivMapOfInjective (Sub w) (MonoidHom.inl (Gamma w) (F ⧸ N))
    (fun _ _ h => congrArg Prod.fst h)

/-- The identification the last stable letter realizes: `(s, 1) ↦ (s, τ s)`. -/
noncomputable def psi : ↥(AeSub w) ≃* ↥(BeSub w) :=
  (aeSubEquiv w).symm.trans
    (Pinch.graphEquiv w.L (Aemb w) (phi w) (phi_kills w)).symm

/-- **The group the rope trick builds.** -/
abbrev RopeGroup : Type := HNNExtension (Amb w) (AeSub w) (BeSub w) (psi w)

/-- The quotient sits inside it. -/
noncomputable def quotientEmb : (F ⧸ N) →* RopeGroup w :=
  (HNNExtension.of).comp (MonoidHom.inr (Gamma w) (F ⧸ N))

theorem quotientEmb_injective : Function.Injective (quotientEmb w) := by
  refine Function.Injective.comp ?_ ?_
  · exact HNNExtension.of_injective (φ := psi w)
  · intro x y hxy
    exact congrArg Prod.snd hxy

end Rope
end Higman
end GroupApproximation

namespace GroupApproximation
namespace Higman
namespace Rope

open HNNExtension
open scoped Monoid.Coprod

variable {F : Type} [Group F] {N : Subgroup F} [N.Normal] (w : BenignWitness N)

/-! ## 4.  The finitely presented candidate -/

/-- The manifestly finitely presented part: the first extension, the free
group of the quotient's generators before any relation is imposed, and the
last stable letter. -/
abbrev Pre : Type := Monoid.Coprod (Gamma w × F) (Multiplicative ℤ)

/-- The first extension, inside the candidate. -/
def preGamma : Gamma w →* Pre w :=
  (Monoid.Coprod.inl).comp (MonoidHom.inl (Gamma w) F)

/-- `F`, inside the candidate. -/
def preF : F →* Pre w :=
  (Monoid.Coprod.inl).comp (MonoidHom.inr (Gamma w) F)

/-- The last stable letter, inside the candidate. -/
def preE : Pre w := Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ℤ))

theorem preGamma_commute_preF (g : Gamma w) (x : F) :
    Commute (preGamma w g) (preF w x) := by
  unfold preGamma preF
  refine Commute.map ?_ _
  show ((g, (1 : F))) * ((1 : Gamma w), x) = ((1 : Gamma w), x) * (g, (1 : F))
  refine Prod.ext ?_ ?_
  · show g * 1 = 1 * g
    rw [mul_one, one_mul]
  · show (1 : F) * x = x * 1
    rw [mul_one, one_mul]

/-- The image of `x ∈ F` in the first extension. -/
def gammaOf (x : F) : Gamma w := HNNExtension.of (w.emb x)

/-- Its conjugate by the first stable letter. -/
def gammaConj (x : F) : Gamma w :=
  (HNNExtension.t : Gamma w)⁻¹ * HNNExtension.of (w.emb x) * HNNExtension.t

/-- The relator saying that the last stable letter sends `(ι x, 1)` to
`(ι x, x̄)`. -/
def relatorA (x : F) : Pre w :=
  preE w * preGamma w (gammaOf w x) * (preE w)⁻¹ *
    (preGamma w (gammaOf w x) * preF w x)⁻¹

/-- The relator saying that it fixes `((ι x)ᵗ, 1)`. -/
def relatorB (x : F) : Pre w :=
  preE w * preGamma w (gammaConj w x) * (preE w)⁻¹ *
    (preGamma w (gammaConj w x))⁻¹

/-- The finitely many relators, over a generating set of `F`. -/
def relators (SF : Set F) : Set (Pre w) :=
  relatorA w '' SF ∪ relatorB w '' SF

theorem relators_finite {SF : Set F} (hSF : SF.Finite) :
    (relators w SF).Finite :=
  (hSF.image _).union (hSF.image _)

/-- The candidate: finitely presented by construction. -/
abbrev Pres (SF : Set F) : Type :=
  Pre w ⧸ Subgroup.normalClosure (relators w SF)

/-- The quotient map onto the candidate. -/
def presMk (SF : Set F) : Pre w →* Pres w SF :=
  QuotientGroup.mk' _

theorem isFinitelyPresented_pres [Group.IsFinitelyPresented F] {SF : Set F}
    (hSF : SF.Finite) : Group.IsFinitelyPresented (Pres w SF) := by
  letI : Group.IsFinitelyPresented (Gamma w) := isFinitelyPresented_gamma w
  exact Group.IsFinitelyPresented.quotient _
    ⟨relators w SF, relators_finite w hSF, rfl⟩

/-! ## 5.  The relations hold on all of `F`, not just on the generators -/

theorem relatorA_mem (SF : Set F) {x : F} (hx : x ∈ SF) :
    relatorA w x ∈ Subgroup.normalClosure (relators w SF) :=
  Subgroup.subset_closure (Set.mem_of_mem_of_subset
    (Set.mem_image_of_mem _ hx) (fun _ h => Subgroup.subset_normalClosure (Or.inl h)))

theorem relatorB_mem (SF : Set F) {x : F} (hx : x ∈ SF) :
    relatorB w x ∈ Subgroup.normalClosure (relators w SF) :=
  Subgroup.subset_normalClosure (Or.inr (Set.mem_image_of_mem _ hx))

/-- In the candidate, the first relation holds for every element of `F`, not
only for the generators: both sides are homomorphisms in `x`, because the
image of the first extension commutes with the image of `F`. -/
theorem presMk_relA {SF : Set F} (hSF : Subgroup.closure SF = ⊤) (x : F) :
    presMk w SF (preE w) * presMk w SF (preGamma w (gammaOf w x)) *
        (presMk w SF (preE w))⁻¹
      = presMk w SF (preGamma w (gammaOf w x)) * presMk w SF (preF w x) := by
  set π := presMk w SF with hπ
  set f₁ : F →* Pres w SF :=
    { toFun := fun x => π (preE w) * π (preGamma w (gammaOf w x)) * (π (preE w))⁻¹
      map_one' := by
        unfold gammaOf
        rw [map_one, map_one, map_one, mul_one, mul_inv_cancel]
      map_mul' := by
        intro a b
        unfold gammaOf
        rw [map_mul, map_mul, map_mul, map_mul]
        group } with hf₁
  set f₂ : F →* Pres w SF :=
    { toFun := fun x => π (preGamma w (gammaOf w x)) * π (preF w x)
      map_one' := by
        unfold gammaOf
        rw [map_one, map_one, map_one, map_one, mul_one]
      map_mul' := by
        intro a b
        unfold gammaOf
        rw [map_mul, map_mul, map_mul, map_mul, map_mul, map_mul]
        have hcomm : Commute (π (preGamma w (HNNExtension.of (w.emb b))))
            (π (preF w a)) := (preGamma_commute_preF w _ a).map π
        calc
          π (preGamma w (HNNExtension.of (w.emb a))) *
              π (preGamma w (HNNExtension.of (w.emb b))) *
              (π (preF w a) * π (preF w b))
              = π (preGamma w (HNNExtension.of (w.emb a))) *
                  (π (preGamma w (HNNExtension.of (w.emb b))) * π (preF w a)) *
                  π (preF w b) := by group
          _ = π (preGamma w (HNNExtension.of (w.emb a))) *
                  (π (preF w a) * π (preGamma w (HNNExtension.of (w.emb b)))) *
                  π (preF w b) := by rw [hcomm.eq]
          _ = π (preGamma w (HNNExtension.of (w.emb a))) * π (preF w a) *
                  (π (preGamma w (HNNExtension.of (w.emb b))) * π (preF w b)) := by
                group } with hf₂
  have hgen : ∀ y ∈ SF, f₁ y = f₂ y := by
    intro y hy
    have hrel : π (relatorA w y) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (relatorA_mem w SF hy)
    unfold relatorA at hrel
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_mul] at hrel
    show π (preE w) * π (preGamma w (gammaOf w y)) * (π (preE w))⁻¹
      = π (preGamma w (gammaOf w y)) * π (preF w y)
    have := mul_inv_eq_one.mp hrel
    exact this
  have htop : f₁.eqLocus f₂ = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← hSF]
    refine (Subgroup.closure_le _).mpr ?_
    intro y hy
    exact hgen y hy
  have : x ∈ f₁.eqLocus f₂ := by
    rw [htop]
    exact Subgroup.mem_top x
  exact this

/-- The same for the second relation. -/
theorem presMk_relB {SF : Set F} (hSF : Subgroup.closure SF = ⊤) (x : F) :
    presMk w SF (preE w) * presMk w SF (preGamma w (gammaConj w x)) *
        (presMk w SF (preE w))⁻¹
      = presMk w SF (preGamma w (gammaConj w x)) := by
  set π := presMk w SF with hπ
  set g₁ : F →* Pres w SF :=
    { toFun := fun x => π (preE w) * π (preGamma w (gammaConj w x)) * (π (preE w))⁻¹
      map_one' := by
        unfold gammaConj
        rw [map_one]
        simp
      map_mul' := by
        intro a b
        unfold gammaConj
        rw [map_mul]
        have hsplit : (HNNExtension.t : Gamma w)⁻¹ *
            HNNExtension.of (w.emb a * w.emb b) * HNNExtension.t
            = ((HNNExtension.t : Gamma w)⁻¹ * HNNExtension.of (w.emb a) *
                HNNExtension.t) *
              ((HNNExtension.t : Gamma w)⁻¹ * HNNExtension.of (w.emb b) *
                HNNExtension.t) := by
          rw [map_mul]
          group
        rw [hsplit, map_mul, map_mul]
        group } with hg₁
  set g₂ : F →* Pres w SF :=
    { toFun := fun x => π (preGamma w (gammaConj w x))
      map_one' := by
        unfold gammaConj
        rw [map_one]
        simp
      map_mul' := by
        intro a b
        unfold gammaConj
        rw [map_mul]
        have hsplit : (HNNExtension.t : Gamma w)⁻¹ *
            HNNExtension.of (w.emb a * w.emb b) * HNNExtension.t
            = ((HNNExtension.t : Gamma w)⁻¹ * HNNExtension.of (w.emb a) *
                HNNExtension.t) *
              ((HNNExtension.t : Gamma w)⁻¹ * HNNExtension.of (w.emb b) *
                HNNExtension.t) := by
          rw [map_mul]
          group
        rw [hsplit, map_mul, map_mul] } with hg₂
  have hgen : ∀ y ∈ SF, g₁ y = g₂ y := by
    intro y hy
    have hrel : π (relatorB w y) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (relatorB_mem w SF hy)
    unfold relatorB at hrel
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at hrel
    show π (preE w) * π (preGamma w (gammaConj w y)) * (π (preE w))⁻¹
      = π (preGamma w (gammaConj w y))
    exact mul_inv_eq_one.mp hrel
  have htop : g₁.eqLocus g₂ = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← hSF]
    refine (Subgroup.closure_le _).mpr ?_
    intro y hy
    exact hgen y hy
  have : x ∈ g₁.eqLocus g₂ := by
    rw [htop]
    exact Subgroup.mem_top x
  exact this

/-- **The relations of the quotient are consequences.**  For `n ∈ N` the two
displayed relations have equal left-hand sides, because `ι n` lies in `L` and
so is fixed by the first stable letter; comparing right-hand sides kills
`n`. -/
theorem presMk_preF_eq_one {SF : Set F} (hSF : Subgroup.closure SF = ⊤)
    {n : F} (hn : n ∈ N) : presMk w SF (preF w n) = 1 := by
  have hnL : w.emb n ∈ w.L := by
    have : n ∈ w.L.comap w.emb := by
      rw [w.comap_eq]
      exact hn
    exact Subgroup.mem_comap.mp this
  have hfix : gammaConj w n = gammaOf w n := by
    unfold gammaConj gammaOf
    exact conj_eq_self_of_mem w.L hnL
  have hA := presMk_relA w hSF n
  have hB := presMk_relB w hSF n
  rw [hfix] at hB
  rw [hB] at hA
  have := mul_eq_left.mp hA.symm
  exact this

end Rope
end Higman
end GroupApproximation

namespace GroupApproximation
namespace Higman
namespace Rope

open HNNExtension
open scoped Monoid.Coprod

variable {F : Type} [Group F] {N : Subgroup F} [N.Normal] (w : BenignWitness N)

/-! ## 6.  What the last stable letter does -/

theorem gammaOf_mem_sub (x : F) : gammaOf w x ∈ Sub w :=
  Subgroup.subset_closure (Or.inl ⟨w.emb x, ⟨x, Subgroup.mem_top x, rfl⟩, rfl⟩)

theorem gammaConj_mem_sub (x : F) : gammaConj w x ∈ Sub w := by
  refine Subgroup.subset_closure (Or.inr ?_)
  refine ⟨HNNExtension.of (w.emb x), ⟨w.emb x, ⟨x, Subgroup.mem_top x, rfl⟩, rfl⟩, ?_⟩
  show _ * _ * _ = _
  rw [inv_inv]
  rfl

theorem pair_mem_ae (s : Gamma w) (hs : s ∈ Sub w) :
    ((s, (1 : F ⧸ N)) : Amb w) ∈ AeSub w :=
  ⟨s, hs, rfl⟩

/-- The underlying element of `graphEquiv` is the first coordinate. -/
theorem coe_graphEquiv (z : ↥(Pinch.blockGraph w.L (Aemb w) (phi w))) :
    ((Pinch.graphEquiv w.L (Aemb w) (phi w) (phi_kills w) z :
        ↥(Sub w)) : Gamma w) = (z : Gamma w × (F ⧸ N)).1 := rfl

/-- The underlying element of `aeSubEquiv` is the pair. -/
theorem coe_aeSubEquiv (s : ↥(Sub w)) :
    ((aeSubEquiv w s : ↥(AeSub w)) : Amb w) = ((s : Gamma w), 1) := by
  show ((Subgroup.equivMapOfInjective (Sub w)
    (MonoidHom.inl (Gamma w) (F ⧸ N)) _ s : ↥(AeSub w)) : Amb w) = _
  rw [Subgroup.coe_equivMapOfInjective_apply]
  rfl

/-- **The last stable letter, on the image of `F`.**  It attaches the class of
`x` in the second coordinate. -/
theorem coe_psi_of (x : F) :
    ((psi w ⟨((gammaOf w x, (1 : F ⧸ N)) : Amb w),
        pair_mem_ae w _ (gammaOf_mem_sub w x)⟩ : ↥(BeSub w)) : Amb w)
      = (gammaOf w x, QuotientGroup.mk' N x) := by
  have hpair : ((gammaOf w x, phi w (aembEquiv w x)) : Amb w)
      ∈ Pinch.blockGraph w.L (Aemb w) (phi w) := by
    have := Pinch.pair_mem_blockGraph w.L (Aemb w) (phi w) (aembEquiv w x)
    rwa [coe_aembEquiv] at this
  have hstep : (Pinch.graphEquiv w.L (Aemb w) (phi w) (phi_kills w))
      ⟨((gammaOf w x, phi w (aembEquiv w x)) : Amb w), hpair⟩
      = ⟨gammaOf w x, gammaOf_mem_sub w x⟩ := by
    refine Subtype.ext ?_
    rw [coe_graphEquiv]
  have hsymm : (Pinch.graphEquiv w.L (Aemb w) (phi w) (phi_kills w)).symm
      ⟨gammaOf w x, gammaOf_mem_sub w x⟩
      = ⟨((gammaOf w x, phi w (aembEquiv w x)) : Amb w), hpair⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact hstep.symm
  have hae : (aeSubEquiv w).symm ⟨((gammaOf w x, (1 : F ⧸ N)) : Amb w),
      pair_mem_ae w _ (gammaOf_mem_sub w x)⟩
      = ⟨gammaOf w x, gammaOf_mem_sub w x⟩ := by
    rw [MulEquiv.symm_apply_eq]
    refine Subtype.ext ?_
    rw [coe_aeSubEquiv]
  show ((Pinch.graphEquiv w.L (Aemb w) (phi w) (phi_kills w)).symm
    ((aeSubEquiv w).symm _) : Amb w) = _
  rw [hae, hsymm]
  show ((gammaOf w x, phi w (aembEquiv w x)) : Amb w) = _
  rw [phi_apply]

/-- **The last stable letter, on the conjugate.**  It fixes it. -/
theorem coe_psi_conj (x : F) :
    ((psi w ⟨((gammaConj w x, (1 : F ⧸ N)) : Amb w),
        pair_mem_ae w _ (gammaConj_mem_sub w x)⟩ : ↥(BeSub w)) : Amb w)
      = (gammaConj w x, 1) := by
  have hpair : ((gammaConj w x, (1 : F ⧸ N)) : Amb w)
      ∈ Pinch.blockGraph w.L (Aemb w) (phi w) := by
    have := Pinch.conj_pair_mem_blockGraph w.L (Aemb w) (phi w) (aembEquiv w x)
    rwa [coe_aembEquiv] at this
  have hstep : (Pinch.graphEquiv w.L (Aemb w) (phi w) (phi_kills w))
      ⟨((gammaConj w x, (1 : F ⧸ N)) : Amb w), hpair⟩
      = ⟨gammaConj w x, gammaConj_mem_sub w x⟩ := by
    refine Subtype.ext ?_
    rw [coe_graphEquiv]
  have hsymm : (Pinch.graphEquiv w.L (Aemb w) (phi w) (phi_kills w)).symm
      ⟨gammaConj w x, gammaConj_mem_sub w x⟩
      = ⟨((gammaConj w x, (1 : F ⧸ N)) : Amb w), hpair⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact hstep.symm
  have hae : (aeSubEquiv w).symm ⟨((gammaConj w x, (1 : F ⧸ N)) : Amb w),
      pair_mem_ae w _ (gammaConj_mem_sub w x)⟩
      = ⟨gammaConj w x, gammaConj_mem_sub w x⟩ := by
    rw [MulEquiv.symm_apply_eq]
    refine Subtype.ext ?_
    rw [coe_aeSubEquiv]
  show ((Pinch.graphEquiv w.L (Aemb w) (phi w) (phi_kills w)).symm
    ((aeSubEquiv w).symm _) : Amb w) = _
  rw [hae, hsymm]

end Rope
end Higman
end GroupApproximation

namespace GroupApproximation
namespace Higman
namespace Rope

open HNNExtension
open scoped Monoid.Coprod

variable {F : Type} [Group F] {N : Subgroup F} [N.Normal] (w : BenignWitness N)

/-! ## 7.  The candidate is the group -/

/-- The images of the two factors of the ambient direct product commute. -/
theorem inl_inr_commute (g : Gamma w) (x : F ⧸ N) :
    Commute ((HNNExtension.of : Amb w →* RopeGroup w) (g, 1))
      ((HNNExtension.of : Amb w →* RopeGroup w) (1, x)) := by
  refine Commute.map ?_ _
  show ((g, (1 : F ⧸ N)) : Amb w) * ((1 : Gamma w), x)
    = ((1 : Gamma w), x) * (g, (1 : F ⧸ N))
  refine Prod.ext ?_ ?_
  · show g * 1 = 1 * g
    rw [mul_one, one_mul]
  · show (1 : F ⧸ N) * x = x * 1
    rw [mul_one, one_mul]

/-- The map from the finitely presented candidate to the rope group. -/
noncomputable def toRope (SF : Set F) : Pres w SF →* RopeGroup w := by
  refine QuotientGroup.lift _
    (Monoid.Coprod.lift
      (MonoidHom.noncommCoprod
        ((HNNExtension.of : Amb w →* RopeGroup w).comp
          (MonoidHom.inl (Gamma w) (F ⧸ N)))
        ((HNNExtension.of : Amb w →* RopeGroup w).comp
          ((MonoidHom.inr (Gamma w) (F ⧸ N)).comp (QuotientGroup.mk' N)))
        (fun g x => inl_inr_commute w g (QuotientGroup.mk' N x)))
      (zpowersHom (RopeGroup w) (HNNExtension.t))) ?_
  refine Subgroup.normalClosure_le_normal ?_
  rintro _ (⟨x, -, rfl⟩ | ⟨x, -, rfl⟩)
  · -- the first relator
    have hconj := HNNExtension.equiv_eq_conj (φ := psi w)
      ⟨((gammaOf w x, (1 : F ⧸ N)) : Amb w), pair_mem_ae w _ (gammaOf_mem_sub w x)⟩
    rw [coe_psi_of] at hconj
    have hsplit : ((gammaOf w x, QuotientGroup.mk' N x) : Amb w)
        = ((gammaOf w x, (1 : F ⧸ N)) : Amb w) *
          (((1 : Gamma w), QuotientGroup.mk' N x) : Amb w) := by
      refine Prod.ext ?_ ?_
      · show _ = gammaOf w x * 1
        rw [mul_one]
      · show _ = 1 * QuotientGroup.mk' N x
        rw [one_mul]
    rw [hsplit, map_mul] at hconj
    show _ ∈ _
    refine MonoidHom.mem_ker.mpr ?_
    unfold relatorA
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_mul]
    show (HNNExtension.t : RopeGroup w) *
        (HNNExtension.of ((gammaOf w x, (1 : F ⧸ N)) : Amb w)) *
        (HNNExtension.t : RopeGroup w)⁻¹ *
        ((HNNExtension.of ((gammaOf w x, (1 : F ⧸ N)) : Amb w)) *
          (HNNExtension.of (((1 : Gamma w), QuotientGroup.mk' N x) : Amb w)))⁻¹ = 1
    rw [← hconj]
    exact mul_inv_cancel _
  · -- the second relator
    have hconj := HNNExtension.equiv_eq_conj (φ := psi w)
      ⟨((gammaConj w x, (1 : F ⧸ N)) : Amb w),
        pair_mem_ae w _ (gammaConj_mem_sub w x)⟩
    rw [coe_psi_conj] at hconj
    refine MonoidHom.mem_ker.mpr ?_
    unfold relatorB
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    show (HNNExtension.t : RopeGroup w) *
        (HNNExtension.of ((gammaConj w x, (1 : F ⧸ N)) : Amb w)) *
        (HNNExtension.t : RopeGroup w)⁻¹ *
        (HNNExtension.of ((gammaConj w x, (1 : F ⧸ N)) : Amb w))⁻¹ = 1
    rw [← hconj]
    exact mul_inv_cancel _

@[simp] theorem toRope_gamma (SF : Set F) (g : Gamma w) :
    toRope w SF (presMk w SF (preGamma w g))
      = (HNNExtension.of : Amb w →* RopeGroup w) (g, 1) := rfl

@[simp] theorem toRope_f (SF : Set F) (x : F) :
    toRope w SF (presMk w SF (preF w x))
      = (HNNExtension.of : Amb w →* RopeGroup w) (1, QuotientGroup.mk' N x) := rfl

@[simp] theorem toRope_e (SF : Set F) :
    toRope w SF (presMk w SF (preE w)) = (HNNExtension.t : RopeGroup w) := rfl

/-- The map to the candidate. -/
noncomputable def fromRope (SF : Set F) (hSF : Subgroup.closure SF = ⊤) :
    RopeGroup w →* Pres w SF := by
  refine HNNExtension.lift
    (MonoidHom.noncommCoprod ((presMk w SF).comp (preGamma w))
      (QuotientGroup.lift N ((presMk w SF).comp (preF w)) ?_)
      ?_)
    (presMk w SF (preE w)) ?_
  · intro n hn
    refine MonoidHom.mem_ker.mpr ?_
    exact presMk_preF_eq_one w hSF hn
  · intro g x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    show Commute (presMk w SF (preGamma w g)) _
    have : (QuotientGroup.lift N ((presMk w SF).comp (preF w)) _)
        (QuotientGroup.mk' N y) = presMk w SF (preF w y) := rfl
    rw [this]
    exact (preGamma_commute_preF w g y).map (presMk w SF)
  · -- the conjugation condition, checked on the generators of `S × 1`
    intro a
    sorry

end Rope
end Higman
end GroupApproximation
