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

omit [N.Normal] in
theorem isFinitelyPresented_gamma : Group.IsFinitelyPresented (Gamma w) :=
  isFinitelyPresented_centHNN w.L w.L_fg

/-- `F`, as a subgroup of the overgroup, is a copy of `F`. -/
noncomputable def aembEquiv : F ≃* ↥(Aemb w) :=
  (Subgroup.topEquiv (G := F)).symm.trans
    (Subgroup.equivMapOfInjective (⊤ : Subgroup F) w.emb w.emb_injective)

omit [N.Normal] in
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
  intro x y hxy
  have hpair : (((1 : Gamma w), x) : Amb w) = ((1, y) : Amb w) :=
    HNNExtension.of_injective (φ := psi w) hxy
  exact congrArg Prod.snd hpair

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

omit [N.Normal] in
theorem preGamma_commute_preF (g : Gamma w) (x : F) :
    Commute (preGamma w g) (preF w x) := by
  have h : Commute ((g, (1 : F)) : Gamma w × F) ((1, x) : Gamma w × F) := by
    refine Prod.ext ?_ ?_
    · show g * 1 = 1 * g
      rw [mul_one, one_mul]
    · show (1 : F) * x = x * 1
      rw [mul_one, one_mul]
  exact h.map (Monoid.Coprod.inl : Gamma w × F →* Pre w)

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

omit [N.Normal] in
theorem relators_finite {SF : Set F} (hSF : SF.Finite) :
    (relators w SF).Finite :=
  (hSF.image _).union (hSF.image _)

/-- The candidate: finitely presented by construction. -/
abbrev Pres (SF : Set F) : Type :=
  Pre w ⧸ Subgroup.normalClosure (relators w SF)

/-- The quotient map onto the candidate. -/
def presMk (SF : Set F) : Pre w →* Pres w SF :=
  QuotientGroup.mk' _

omit [N.Normal] in
theorem isFinitelyPresented_pres [Group.IsFinitelyPresented F] {SF : Set F}
    (hSF : SF.Finite) : Group.IsFinitelyPresented (Pres w SF) := by
  letI : Group.IsFinitelyPresented (Gamma w) := isFinitelyPresented_gamma w
  exact Group.IsFinitelyPresented.quotient _
    ⟨relators w SF, relators_finite w hSF, rfl⟩

/-! ## 5.  The relations hold on all of `F`, not just on the generators -/

omit [N.Normal] in
theorem relatorA_mem (SF : Set F) {x : F} (hx : x ∈ SF) :
    relatorA w x ∈ Subgroup.normalClosure (relators w SF) :=
  Subgroup.subset_normalClosure (Or.inl (Set.mem_image_of_mem _ hx))

omit [N.Normal] in
theorem relatorB_mem (SF : Set F) {x : F} (hx : x ∈ SF) :
    relatorB w x ∈ Subgroup.normalClosure (relators w SF) :=
  Subgroup.subset_normalClosure (Or.inr (Set.mem_image_of_mem _ hx))

omit [N.Normal] in
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
        simp
      map_mul' := by
        intro a b
        unfold gammaOf
        rw [map_mul, map_mul, map_mul, map_mul]
        group } with hf₁
  set f₂ : F →* Pres w SF :=
    { toFun := fun x => π (preGamma w (gammaOf w x)) * π (preF w x)
      map_one' := by
        unfold gammaOf
        simp
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

omit [N.Normal] in
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
        have hsplit : gammaConj w (a * b) = gammaConj w a * gammaConj w b := by
          unfold gammaConj
          rw [map_mul, map_mul]
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
        have hsplit : gammaConj w (a * b) = gammaConj w a * gammaConj w b := by
          unfold gammaConj
          rw [map_mul, map_mul]
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

omit [N.Normal] in
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

omit [N.Normal] in
theorem gammaOf_mem_sub (x : F) : gammaOf w x ∈ Sub w :=
  Subgroup.subset_closure (Or.inl ⟨w.emb x, ⟨x, Subgroup.mem_top x, rfl⟩, rfl⟩)

omit [N.Normal] in
theorem conjT_of_emb (x : F) :
    (conjT w.L) (HNNExtension.of (w.emb x)) = gammaConj w x := by
  rw [conjT_apply, inv_inv]
  rfl

omit [N.Normal] in
theorem gammaConj_mem_sub (x : F) : gammaConj w x ∈ Sub w := by
  refine Subgroup.subset_closure (Or.inr ?_)
  refine ⟨HNNExtension.of (w.emb x), ⟨w.emb x, ⟨x, Subgroup.mem_top x, rfl⟩, rfl⟩, ?_⟩
  exact conjT_of_emb w x

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

/-- The homomorphism on the free-product presentation before quotienting by
the two relator families. -/
noncomputable def ropePreMap : Pre w →* RopeGroup w :=
  Monoid.Coprod.lift
    (MonoidHom.noncommCoprod
      ((HNNExtension.of : Amb w →* RopeGroup w).comp
        (MonoidHom.inl (Gamma w) (F ⧸ N)))
      ((HNNExtension.of : Amb w →* RopeGroup w).comp
        ((MonoidHom.inr (Gamma w) (F ⧸ N)).comp (QuotientGroup.mk' N)))
      (fun g x => inl_inr_commute w g (QuotientGroup.mk' N x)))
    (zpowersHom (RopeGroup w) (HNNExtension.t))

@[simp] theorem ropePreMap_preGamma (g : Gamma w) :
    ropePreMap w (preGamma w g) =
      (HNNExtension.of : Amb w →* RopeGroup w) (g, 1) := by
  simp [ropePreMap, preGamma, MonoidHom.noncommCoprod_apply]
  exact map_one (HNNExtension.of : Amb w →* RopeGroup w)

@[simp] theorem ropePreMap_preF (x : F) :
    ropePreMap w (preF w x) =
      (HNNExtension.of : Amb w →* RopeGroup w) (1, QuotientGroup.mk' N x) := by
  simp [ropePreMap, preF, MonoidHom.noncommCoprod_apply]
  exact map_one (HNNExtension.of : Amb w →* RopeGroup w)

@[simp] theorem ropePreMap_preE :
    ropePreMap w (preE w) = (HNNExtension.t : RopeGroup w) := by
  rw [ropePreMap, preE, Monoid.Coprod.lift_apply_inr, zpowersHom_apply,
    toAdd_ofAdd, zpow_one]

/-- The map from the finitely presented candidate to the rope group. -/
noncomputable def toRope (SF : Set F) : Pres w SF →* RopeGroup w := by
  refine QuotientGroup.lift _
    (ropePreMap w) ?_
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
    rw [ropePreMap_preE, ropePreMap_preGamma, ropePreMap_preF]
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
    rw [ropePreMap_preE, ropePreMap_preGamma]
    show (HNNExtension.t : RopeGroup w) *
        (HNNExtension.of ((gammaConj w x, (1 : F ⧸ N)) : Amb w)) *
        (HNNExtension.t : RopeGroup w)⁻¹ *
        (HNNExtension.of ((gammaConj w x, (1 : F ⧸ N)) : Amb w))⁻¹ = 1
    rw [← hconj]
    exact mul_inv_cancel _

@[simp] theorem toRope_presMk (SF : Set F) (z : Pre w) :
    toRope w SF (presMk w SF z) = ropePreMap w z := by
  unfold toRope presMk
  rfl

@[simp] theorem toRope_gamma (SF : Set F) (g : Gamma w) :
    toRope w SF (presMk w SF (preGamma w g))
      = (HNNExtension.of : Amb w →* RopeGroup w) (g, 1) := by
  rw [toRope_presMk, ropePreMap_preGamma]

@[simp] theorem toRope_f (SF : Set F) (x : F) :
    toRope w SF (presMk w SF (preF w x))
      = (HNNExtension.of : Amb w →* RopeGroup w) (1, QuotientGroup.mk' N x) := by
  rw [toRope_presMk, ropePreMap_preF]

@[simp] theorem toRope_e (SF : Set F) :
    toRope w SF (presMk w SF (preE w)) = (HNNExtension.t : RopeGroup w) := by
  rw [toRope_presMk, ropePreMap_preE]

/-! ## 8.  The value map, computed on the generators -/

/-- The second coordinate of the image of `(s, 1)` is `τ s`; the first is `s`.
Both are immediate from the way `psi` was assembled. -/
theorem coe_psi_snd (s : Gamma w) (hs : s ∈ Sub w) :
    (((psi w ⟨((s, (1 : F ⧸ N)) : Amb w), pair_mem_ae w s hs⟩ :
        ↥(BeSub w)) : Amb w)).2 = tau w ⟨s, hs⟩ := by
  have hae : (aeSubEquiv w).symm ⟨((s, (1 : F ⧸ N)) : Amb w), pair_mem_ae w s hs⟩
      = ⟨s, hs⟩ := by
    rw [MulEquiv.symm_apply_eq]
    refine Subtype.ext ?_
    rw [coe_aeSubEquiv]
  show ((Pinch.graphEquiv w.L (Aemb w) (phi w) (phi_kills w)).symm
    ((aeSubEquiv w).symm _) : Amb w).2 = _
  rw [hae]
  rfl

theorem coe_psi_fst (s : Gamma w) (hs : s ∈ Sub w) :
    (((psi w ⟨((s, (1 : F ⧸ N)) : Amb w), pair_mem_ae w s hs⟩ :
        ↥(BeSub w)) : Amb w)).1 = s := by
  have hae : (aeSubEquiv w).symm ⟨((s, (1 : F ⧸ N)) : Amb w), pair_mem_ae w s hs⟩
      = ⟨s, hs⟩ := by
    rw [MulEquiv.symm_apply_eq]
    refine Subtype.ext ?_
    rw [coe_aeSubEquiv]
  have hgen := coe_graphEquiv w
    ((Pinch.graphEquiv w.L (Aemb w) (phi w) (phi_kills w)).symm ⟨s, hs⟩)
  rw [MulEquiv.apply_symm_apply] at hgen
  show ((Pinch.graphEquiv w.L (Aemb w) (phi w) (phi_kills w)).symm
    ((aeSubEquiv w).symm _) : Amb w).1 = _
  rw [hae]
  exact hgen.symm

/-- The image of `(s, 1)` under the last stable letter. -/
theorem coe_psi (s : Gamma w) (hs : s ∈ Sub w) :
    ((psi w ⟨((s, (1 : F ⧸ N)) : Amb w), pair_mem_ae w s hs⟩ :
        ↥(BeSub w)) : Amb w) = (s, tau w ⟨s, hs⟩) := by
  refine Prod.ext ?_ ?_
  · exact coe_psi_fst w s hs
  · exact coe_psi_snd w s hs

/-- `τ` is the quotient map on the image of `F`. -/
theorem tau_gammaOf (x : F) :
    tau w ⟨gammaOf w x, gammaOf_mem_sub w x⟩ = QuotientGroup.mk' N x := by
  have h₁ := coe_psi w (gammaOf w x) (gammaOf_mem_sub w x)
  have h₂ := coe_psi_of w x
  rw [h₁] at h₂
  exact congrArg Prod.snd h₂

/-- `τ` is trivial on the conjugate. -/
theorem tau_gammaConj (x : F) :
    tau w ⟨gammaConj w x, gammaConj_mem_sub w x⟩ = 1 := by
  have h₁ := coe_psi w (gammaConj w x) (gammaConj_mem_sub w x)
  have h₂ := coe_psi_conj w x
  rw [h₁] at h₂
  exact congrArg Prod.snd h₂

/-! ## 9.  The map to the candidate -/

variable (SF : Set F)

/-- The quotient-coordinate map into the finite presentation. -/
noncomputable def quotientMap (hSF : Subgroup.closure SF = ⊤) :
    (F ⧸ N) →* Pres w SF :=
  QuotientGroup.lift N ((presMk w SF).comp (preF w)) fun _n hn =>
    MonoidHom.mem_ker.mpr (presMk_preF_eq_one w hSF hn)

@[simp] theorem quotientMap_mk (hSF : Subgroup.closure SF = ⊤) (x : F) :
    quotientMap w SF hSF (QuotientGroup.mk' N x) = presMk w SF (preF w x) := rfl

/-- The base map of the last HNN extension, into the candidate. -/
noncomputable def baseMap (hSF : Subgroup.closure SF = ⊤) :
    Amb w →* Pres w SF := by
  refine MonoidHom.noncommCoprod ((presMk w SF).comp (preGamma w))
    (quotientMap w SF hSF) ?_
  · intro g x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    change Commute (presMk w SF (preGamma w g))
      (quotientMap w SF hSF (QuotientGroup.mk' N y))
    rw [quotientMap_mk]
    exact (preGamma_commute_preF w g y).map (presMk w SF)

@[simp] theorem baseMap_inl (hSF : Subgroup.closure SF = ⊤) (g : Gamma w) :
    baseMap w SF hSF (g, 1) = presMk w SF (preGamma w g) := by
  unfold baseMap
  rw [MonoidHom.noncommCoprod_apply]
  change presMk w SF (preGamma w g) * quotientMap w SF hSF 1 = _
  rw [map_one, mul_one]

@[simp] theorem baseMap_inr (hSF : Subgroup.closure SF = ⊤) (x : F) :
    baseMap w SF hSF (1, QuotientGroup.mk' N x) = presMk w SF (preF w x) := by
  unfold baseMap
  rw [MonoidHom.noncommCoprod_apply]
  change presMk w SF (preGamma w 1) *
    quotientMap w SF hSF (QuotientGroup.mk' N x) = _
  simp only [map_one, one_mul, quotientMap_mk]

theorem baseMap_pair (hSF : Subgroup.closure SF = ⊤) (g : Gamma w) (x : F) :
    baseMap w SF hSF (g, QuotientGroup.mk' N x)
      = presMk w SF (preGamma w g) * presMk w SF (preF w x) := by
  have hsplit : ((g, QuotientGroup.mk' N x) : Amb w)
      = ((g, (1 : F ⧸ N)) : Amb w) * (((1 : Gamma w), QuotientGroup.mk' N x) : Amb w) := by
    refine Prod.ext ?_ ?_
    · show _ = g * 1
      rw [mul_one]
    · show _ = 1 * QuotientGroup.mk' N x
      rw [one_mul]
  rw [hsplit, map_mul, baseMap_inl, baseMap_inr]

/-- Homomorphisms out of a generated subgroup agree everywhere once they agree
on the ambient generating set. -/
theorem hom_eq_on_closure {G P : Type*} [Group G] [Group P] (S : Set G)
    (f g : ↥(Subgroup.closure S) →* P)
    (h : ∀ y ∈ S, ∀ hy : y ∈ Subgroup.closure S,
      f ⟨y, hy⟩ = g ⟨y, hy⟩) : f = g := by
  ext y
  rcases y with ⟨y, hy⟩
  exact Subgroup.closure_induction
    (p := fun z hz => f ⟨z, hz⟩ = g ⟨z, hz⟩)
    (fun z hz => h z hz _) (map_one f ▸ map_one g ▸ rfl)
    (fun a b haS hbS ha hb => by
      change f (⟨a, haS⟩ * ⟨b, hbS⟩) = g (⟨a, haS⟩ * ⟨b, hbS⟩)
      rw [map_mul, map_mul, ha, hb])
    (fun a haS ha => by
      change f (⟨a, haS⟩⁻¹) = g (⟨a, haS⟩⁻¹)
      rw [map_inv, map_inv, ha]) hy

/-- **The conjugation condition, on `S`.**  Both sides are homomorphisms of
`s`, so it is enough to check the generators of `S`, and there it is exactly
the two families of relators. -/
theorem conj_baseMap (hSF : Subgroup.closure SF = ⊤) (s : ↥(Sub w)) :
    presMk w SF (preE w) * baseMap w SF hSF ((s : Gamma w), 1) *
        (presMk w SF (preE w))⁻¹
      = baseMap w SF hSF ((s : Gamma w), tau w s) := by
  set π := presMk w SF with hπ
  set v₁ : ↥(Sub w) →* Pres w SF :=
    { toFun := fun s => π (preE w) * baseMap w SF hSF ((s : Gamma w), 1) *
        (π (preE w))⁻¹
      map_one' := by
        show π (preE w) * baseMap w SF hSF ((1 : Gamma w), 1) * (π (preE w))⁻¹ = 1
        rw [show (((1 : Gamma w), (1 : F ⧸ N)) : Amb w) = 1 from rfl, map_one,
          mul_one, mul_inv_cancel]
      map_mul' := by
        intro a b
        show π (preE w) * baseMap w SF hSF (((a * b : ↥(Sub w)) : Gamma w), 1) *
            (π (preE w))⁻¹ = _
        have hmul : ((((a * b : ↥(Sub w)) : Gamma w), (1 : F ⧸ N)) : Amb w)
            = (((a : Gamma w), (1 : F ⧸ N)) : Amb w) *
              (((b : Gamma w), (1 : F ⧸ N)) : Amb w) := by
          refine Prod.ext rfl ?_
          show (1 : F ⧸ N) = 1 * 1
          rw [one_mul]
        rw [hmul, map_mul]
        group } with hv₁
  set v₂ : ↥(Sub w) →* Pres w SF :=
    { toFun := fun s => baseMap w SF hSF ((s : Gamma w), tau w s)
      map_one' := by
        show baseMap w SF hSF ((1 : Gamma w), tau w 1) = 1
        rw [map_one]
        rw [show (((1 : Gamma w), (1 : F ⧸ N)) : Amb w) = 1 from rfl, map_one]
      map_mul' := by
        intro a b
        show baseMap w SF hSF (((a * b : ↥(Sub w)) : Gamma w), tau w (a * b)) = _
        rw [map_mul]
        have hmul : ((((a * b : ↥(Sub w)) : Gamma w), tau w a * tau w b) : Amb w)
            = (((a : Gamma w), tau w a) : Amb w) *
              (((b : Gamma w), tau w b) : Amb w) := rfl
        rw [hmul, map_mul] } with hv₂
  have hgen : ∀ y ∈ Pinch.genSet w.L (Aemb w) (Aemb w),
      ∀ hy : y ∈ Sub w, v₁ ⟨y, hy⟩ = v₂ ⟨y, hy⟩ := by
    rintro y (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) hy
    · obtain ⟨z, -, rfl⟩ := hu
      have hy' : v₁ ⟨HNNExtension.of (w.emb z), hy⟩
          = π (preE w) * π (preGamma w (gammaOf w z)) * (π (preE w))⁻¹ := by
        show π (preE w) * baseMap w SF hSF (HNNExtension.of (w.emb z), 1) * _ = _
        rw [baseMap_inl]
        rfl
      have hy'' : v₂ ⟨HNNExtension.of (w.emb z), hy⟩
          = π (preGamma w (gammaOf w z)) * π (preF w z) := by
        show baseMap w SF hSF (HNNExtension.of (w.emb z), tau w _) = _
        have hτ : tau w ⟨HNNExtension.of (w.emb z), hy⟩ = QuotientGroup.mk' N z := by
          have := tau_gammaOf w z
          exact this
        rw [hτ, baseMap_pair]
        rfl
      rw [hy', hy'']
      exact presMk_relA w hSF z
    · obtain ⟨v, hv, rfl⟩ := hu
      obtain ⟨z, -, rfl⟩ := hv
      have hconj : (conjT w.L).toMonoidHom (HNNExtension.of (w.emb z)) =
          gammaConj w z := conjT_of_emb w z
      let hyc : gammaConj w z ∈ Sub w := gammaConj_mem_sub w z
      have hsub : (⟨(conjT w.L).toMonoidHom (HNNExtension.of (w.emb z)), hy⟩ :
          ↥(Sub w)) = ⟨gammaConj w z, hyc⟩ := Subtype.ext hconj
      rw [hsub]
      have hy' : v₁ ⟨gammaConj w z, hyc⟩
          = π (preE w) * π (preGamma w (gammaConj w z)) * (π (preE w))⁻¹ := by
        show π (preE w) * baseMap w SF hSF (_, 1) * _ = _
        rw [baseMap_inl]
      have hy'' : v₂ ⟨gammaConj w z, hyc⟩ = π (preGamma w (gammaConj w z)) := by
        show baseMap w SF hSF (_, tau w _) = _
        have hτ : tau w ⟨gammaConj w z, hyc⟩ = (1 : F ⧸ N) :=
          tau_gammaConj w z
        rw [hτ]
        rw [show (((gammaConj w z), (1 : F ⧸ N)) : Amb w) = ((gammaConj w z), 1) from rfl]
        rw [baseMap_inl]
      rw [hy', hy'']
      exact presMk_relB w hSF z
  have hv : v₁ = v₂ := hom_eq_on_closure _ v₁ v₂ hgen
  exact DFunLike.congr_fun hv s

/-! ## 10.  The two maps are inverse, and the conclusion -/

/-- The map from the rope group to the candidate. -/
noncomputable def fromRope (hSF : Subgroup.closure SF = ⊤) :
    RopeGroup w →* Pres w SF := by
  refine HNNExtension.lift (baseMap w SF hSF) (presMk w SF (preE w)) ?_
  intro a
  obtain ⟨s, hs, hsa⟩ := a.2
  have ha : a = ⟨((s, (1 : F ⧸ N)) : Amb w), pair_mem_ae w s hs⟩ :=
    Subtype.ext hsa.symm
  rw [ha]
  show presMk w SF (preE w) * baseMap w SF hSF ((s, (1 : F ⧸ N)) : Amb w)
    = baseMap w SF hSF
        ((psi w ⟨((s, (1 : F ⧸ N)) : Amb w), pair_mem_ae w s hs⟩ :
          ↥(BeSub w)) : Amb w) * presMk w SF (preE w)
  rw [coe_psi w s hs, ← conj_baseMap w SF hSF ⟨s, hs⟩]
  group

theorem fromRope_toRope (hSF : Subgroup.closure SF = ⊤) :
    (fromRope w SF hSF).comp (toRope w SF) = MonoidHom.id (Pres w SF) := by
  have hsurj : Function.Surjective (presMk w SF) := QuotientGroup.mk'_surjective _
  refine (MonoidHom.cancel_right hsurj).mp ?_
  refine Monoid.Coprod.hom_ext ?_ ?_
  · refine MonoidHom.ext fun z => ?_
    obtain ⟨g, x⟩ := z
    have hsplit : ((g, x) : Gamma w × F) = (g, (1 : F)) * ((1 : Gamma w), x) := by
      refine Prod.ext ?_ ?_
      · show g = g * 1
        rw [mul_one]
      · show x = 1 * x
        rw [one_mul]
    show (fromRope w SF hSF) (toRope w SF (presMk w SF (Monoid.Coprod.inl (g, x))))
      = presMk w SF (Monoid.Coprod.inl (g, x))
    rw [hsplit, map_mul, map_mul, map_mul, map_mul]
    have h₁ : (fromRope w SF hSF) (toRope w SF
        (presMk w SF (Monoid.Coprod.inl ((g, (1 : F)) : Gamma w × F))))
        = presMk w SF (preGamma w g) := by
      show (fromRope w SF hSF) (toRope w SF (presMk w SF (preGamma w g))) = _
      rw [toRope_gamma]
      show baseMap w SF hSF (g, 1) = _
      rw [baseMap_inl]
    have h₂ : (fromRope w SF hSF) (toRope w SF
        (presMk w SF (Monoid.Coprod.inl (((1 : Gamma w), x) : Gamma w × F))))
        = presMk w SF (preF w x) := by
      show (fromRope w SF hSF) (toRope w SF (presMk w SF (preF w x))) = _
      rw [toRope_f]
      show baseMap w SF hSF (1, QuotientGroup.mk' N x) = _
      rw [baseMap_inr]
    rw [h₁, h₂]
    rfl
  · refine MonoidHom.ext_mint ?_
    show (fromRope w SF hSF) (toRope w SF (presMk w SF (preE w)))
      = presMk w SF (preE w)
    rw [toRope_e]
    show HNNExtension.lift (baseMap w SF hSF) (presMk w SF (preE w)) _
      HNNExtension.t = _
    rw [HNNExtension.lift_t]

theorem toRope_injective (hSF : Subgroup.closure SF = ⊤) :
    Function.Injective (toRope w SF) := by
  intro x y hxy
  have h := congrArg (fun f : Pres w SF →* Pres w SF => f x) (fromRope_toRope w SF hSF)
  have h' := congrArg (fun f : Pres w SF →* Pres w SF => f y) (fromRope_toRope w SF hSF)
  show x = y
  calc x = (fromRope w SF hSF) (toRope w SF x) := h.symm
    _ = (fromRope w SF hSF) (toRope w SF y) := by rw [hxy]
    _ = y := h'

theorem toRope_surjective :
    Function.Surjective (toRope w SF) := by
  intro y
  induction y using HNNExtension.induction_on with
  | of g =>
      obtain ⟨g₁, g₂⟩ := g
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g₂
      refine ⟨presMk w SF (preGamma w g₁) * presMk w SF (preF w x), ?_⟩
      rw [map_mul, toRope_gamma, toRope_f, ← map_mul]
      congr 1
      refine Prod.ext ?_ ?_
      · show g₁ * 1 = g₁
        rw [mul_one]
      · show 1 * QuotientGroup.mk' N x = QuotientGroup.mk' N x
        rw [one_mul]
  | t => exact ⟨presMk w SF (preE w), toRope_e w SF⟩
  | mul a b ha hb =>
      obtain ⟨u, hu⟩ := ha
      obtain ⟨v, hv⟩ := hb
      exact ⟨u * v, by rw [map_mul, hu, hv]⟩
  | inv a ha =>
      obtain ⟨u, hu⟩ := ha
      exact ⟨u⁻¹, by rw [map_inv, hu]⟩

/-- **The candidate is the rope group.** -/
noncomputable def ropeEquiv (hSF : Subgroup.closure SF = ⊤) :
    Pres w SF ≃* RopeGroup w :=
  MulEquiv.ofBijective (toRope w SF)
    ⟨toRope_injective w SF hSF, toRope_surjective w SF⟩

/-- **The rope group is finitely presented.** -/
theorem isFinitelyPresented_ropeGroup [Group.IsFinitelyPresented F]
    (hSFfin : SF.Finite) (hSF : Subgroup.closure SF = ⊤) :
    Group.IsFinitelyPresented (RopeGroup w) := by
  letI : Group.IsFinitelyPresented (Pres w SF) := isFinitelyPresented_pres w hSFfin
  exact Group.IsFinitelyPresented.equiv (ropeEquiv w SF hSF)

end Rope

/-! ## The rope trick -/

/-- **Higman's Lemma, the hard direction: the rope trick.**  If `N` is benign
in a finitely generated, finitely presented group `F`, then `F ⧸ N` embeds in
a finitely presented group. -/
theorem fpOvergroup_of_benign {F : Type} [Group F] [Group.IsFinitelyPresented F]
    [Group.FG F] {N : Subgroup F} [N.Normal] (h : Benign N) :
    Nonempty (FPOvergroup (F ⧸ N)) := by
  obtain ⟨w⟩ := h
  obtain ⟨SF, hSF, hSFfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG F)
  letI : Group.IsFinitelyPresented (Rope.RopeGroup w) :=
    Rope.isFinitelyPresented_ropeGroup w SF hSFfin hSF
  exact ⟨{ K := Rope.RopeGroup w
           emb := Rope.quotientEmb w
           emb_injective := Rope.quotientEmb_injective w }⟩

end Higman
end GroupApproximation
