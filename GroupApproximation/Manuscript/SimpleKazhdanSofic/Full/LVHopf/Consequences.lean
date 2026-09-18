import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVHopf.Multiplier
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVSuperperfect.Superperfect

/-!
# Trivial Hopf multiplier and perfect central extensions (lane LVHopf, leaf T1b.iv)

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735.  The repository reaches this sentence
through `K₂(4, L_{𝔽₂}(1,2)) = ⊥` (Khanh arXiv:2609.08428, Thm 5.1).  That proof uses the binder
`hsp` (`LeavittK2.EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement`): every perfect
central extension of `Lˣ` is injective.  This file proves the Hopf-formula form of that step.

* `commutator_le_map_of_lift`: if `φ : F → E` lifts `f : F ↠ G` through a central extension
  `p : E ↠ G`, then `[E, E] ≤ φ [F, F]`.
* `injective_of_perfect_central_of_lift`, `injective_of_perfect_central_of_hopfMultiplierTrivial`:
  if `R ∩ [F,F] ≤ [F,R]` for a free presentation of `G`, then every perfect central extension of
  `G` is injective.  **A perfect central extension of a superperfect group is an isomorphism.**
* `perfectCentralExtension_injective_of_lift_id`: the leaf in exactly the form of
  `$FK/status/LVAssembly.md`, with the presentation `FreeGroup.lift id : FreeGroup G ↠ G`.
* `isSuperperfect_of_hopfMultiplierTrivial`:
  `HopfMultiplierTrivial G → LVSuperperfect.IsSuperperfect G`.
* `binaryLeavittUnits_superperfect_of_hopfMultiplierTrivial`: the literal body of `hsp` from
  `HopfMultiplierTrivial Lˣ`.
* Converse for perfect `G`: `hopfCover f = [F,F]/[F,R]` is a perfect central extension of `G`
  (`hopfCoverExtension`).  So `IsSuperperfect G → HopfMultiplierTrivial G`
  (`hopfMultiplierTrivial_of_isSuperperfect`), and `hopfMultiplierTrivial_iff_isSuperperfect` holds.
-/

namespace GroupApproximation.Full.LVHopf

open scoped commutatorElement

universe u v w

section Lift

variable {F : Type u} {E : Type v} {G : Type w} [Group F] [Group E] [Group G]

/-- If `φ : F → E` lifts a surjection `f : F ↠ G` through `p : E → G` with central kernel, then
`[E, E] ≤ φ [F, F]`.  Each `a ∈ E` is `φ x` times a central element, and the bracket ignores
central factors. -/
theorem commutator_le_map_of_lift (f : F →* G) (hf : Function.Surjective f) (p : E →* G)
    (hcent : p.ker ≤ Subgroup.center E) (φ : F →* E) (hφ : p.comp φ = f) :
    commutator E ≤ (commutator F).map φ := by
  have hdec : ∀ a : E, ∃ x : F, (φ x)⁻¹ * a ∈ Subgroup.center E := by
    intro a
    obtain ⟨x, hx⟩ := hf (p a)
    refine ⟨x, hcent ?_⟩
    have h1 : p (φ x) = f x := DFunLike.congr_fun hφ x
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1, hx, inv_mul_cancel]
  rw [_root_.commutator_def E, Subgroup.commutator_le]
  intro a _ b _
  obtain ⟨x, hx⟩ := hdec a
  obtain ⟨y, hy⟩ := hdec b
  have key : ⁅φ x * ((φ x)⁻¹ * a), φ y * ((φ y)⁻¹ * b)⁆ = ⁅φ x, φ y⁆ :=
    commutatorElement_mul_mul_of_mem_center _ _ _ _ hx hy
  rw [mul_inv_cancel_left, mul_inv_cancel_left] at key
  have hxy : ⁅x, y⁆ ∈ commutator F := by
    rw [_root_.commutator_def F]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
  have hmem : φ ⁅x, y⁆ ∈ (commutator F).map φ := Subgroup.mem_map_of_mem φ hxy
  rw [map_commutatorElement, ← key] at hmem
  exact hmem

/-- **Perfect central extensions are injective when the multiplier vanishes** (lift form).
Let `f : F ↠ G` satisfy `R ∩ [F,F] ≤ [F,R]` with `R = ker f`, and let `p : E → G` have central
kernel with `E` perfect.  If `f` lifts to `φ : F → E`, then `p` is injective.
(`simple_kazhdan_sofic_group.tex` l.733-735, binder `hsp`.) -/
theorem injective_of_perfect_central_of_lift (f : F →* G) (hf : Function.Surjective f)
    (hG : f.ker ⊓ commutator F ≤ ⁅(⊤ : Subgroup F), f.ker⁆) (p : E →* G)
    (hcent : p.ker ≤ Subgroup.center E) (hE : commutator E = ⊤) (φ : F →* E)
    (hφ : p.comp φ = f) : Function.Injective p := by
  have hbot : ⁅(⊤ : Subgroup E), p.ker⁆ = ⊥ :=
    Subgroup.commutator_top_left_eq_bot_iff_le_center.mpr hcent
  have hmap : ⁅(⊤ : Subgroup F), f.ker⁆.map φ ≤ ⁅(⊤ : Subgroup E), p.ker⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top
      (Subgroup.map_le_iff_le_comap.mpr (ker_le_comap_ker_of_comp_eq f p φ hφ))
  rw [← MonoidHom.ker_eq_bot_iff p, Subgroup.eq_bot_iff_forall]
  intro k hk
  have hk' : k ∈ commutator E := by
    rw [hE]
    exact Subgroup.mem_top k
  obtain ⟨x, hxc, rfl⟩ :=
    Subgroup.mem_map.mp (commutator_le_map_of_lift f hf p hcent φ hφ hk')
  have hfx : x ∈ f.ker := by
    have h1 : p (φ x) = f x := DFunLike.congr_fun hφ x
    rw [MonoidHom.mem_ker, ← h1]
    exact MonoidHom.mem_ker.mp hk
  have h2 : φ x ∈ ⁅(⊤ : Subgroup E), p.ker⁆ :=
    hmap (Subgroup.mem_map_of_mem φ (hG (Subgroup.mem_inf.mpr ⟨hfx, hxc⟩)))
  rw [hbot] at h2
  exact Subgroup.mem_bot.mp h2

end Lift

/-- **A perfect central extension of a group with trivial Hopf multiplier is an isomorphism.**
If a free presentation `f : FreeGroup β ↠ G` satisfies `R ∩ [F,F] ≤ [F,R]`, then every surjection
`p : E ↠ G` with central kernel and perfect `E` is injective.  (Hopf 1942; Milnor, *Introduction to
algebraic K-theory*, §5.  `simple_kazhdan_sofic_group.tex` l.733-735, binder `hsp`.) -/
theorem injective_of_perfect_central_of_hopfMultiplierTrivial {β : Type u} {E : Type v}
    {G : Type w} [Group E] [Group G] (f : FreeGroup β →* G) (hf : Function.Surjective f)
    (hG : f.ker ⊓ commutator (FreeGroup β) ≤ ⁅(⊤ : Subgroup (FreeGroup β)), f.ker⁆)
    (p : E →* G) (hp : Function.Surjective p) (hcent : p.ker ≤ Subgroup.center E)
    (hE : commutator E = ⊤) : Function.Injective p := by
  obtain ⟨φ, hφ⟩ := exists_freeGroup_lift f p hp
  exact injective_of_perfect_central_of_lift f hf hG p hcent hE φ hφ

/-- **Leaf T1b.iv in the form of `$FK/status/LVAssembly.md`.**  If
`ker (FreeGroup.lift id) ⊓ [F, F] ≤ [F, ker]` for `F = FreeGroup G`, then every perfect central
extension of `G` is injective.  (`simple_kazhdan_sofic_group.tex` l.733-735.) -/
theorem perfectCentralExtension_injective_of_lift_id {G : Type u} [Group G]
    (hG : (FreeGroup.lift (id : G → G)).ker ⊓ commutator (FreeGroup G) ≤
      ⁅(⊤ : Subgroup (FreeGroup G)), (FreeGroup.lift (id : G → G)).ker⁆)
    {E : Type v} [Group E] (P : GroupApproximation.CentralExtension E G)
    (hE : commutator E = ⊤) : Function.Injective P.projection :=
  injective_of_perfect_central_of_hopfMultiplierTrivial (FreeGroup.lift (id : G → G))
    (FreeGroup.lift_surjective_of_surjective Function.surjective_id) hG P.projection P.surjective
    P.ker_le_center hE

/-- `H₂(G; ℤ) = 0` in Hopf form makes `G` superperfect in central-extension form. -/
theorem isSuperperfect_of_hopfMultiplierTrivial {G : Type u} [Group G]
    (hG : HopfMultiplierTrivial G) : LVSuperperfect.IsSuperperfect G := by
  intro E _ P hE
  exact injective_of_perfect_central_of_hopfMultiplierTrivial (FreeGroup.prod : FreeGroup G →* G)
    FreeGroup.prod_surjective (hG G FreeGroup.prod FreeGroup.prod_surjective) P.projection
    P.surjective P.ker_le_center hE

/-- **`hsp` from the Hopf multiplier.**  If `Lˣ` (with `L = L_{𝔽₂}(1,2)`) has trivial Hopf
multiplier, then the body of `LeavittK2.EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement`
holds.  (`simple_kazhdan_sofic_group.tex` l.733-735.) -/
theorem binaryLeavittUnits_superperfect_of_hopfMultiplierTrivial
    (h : HopfMultiplierTrivial
      ((GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))ˣ)) :
    ∀ (E : Type) [Group E]
      (P : GroupApproximation.CentralExtension E
        ((GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))ˣ)),
      commutator E = ⊤ → Function.Injective P.projection :=
  LVSuperperfect.isSuperperfect_binaryLeavittUnits_iff.mp
    (isSuperperfect_of_hopfMultiplierTrivial h)

section Cover

variable {F : Type u} {G : Type v} [Group F] [Group G]

/-- The map `F ⧸ [F, ker f] → G` induced by `f`. -/
def hopfLift (f : F →* G) : F ⧸ ⁅(⊤ : Subgroup F), f.ker⁆ →* G :=
  QuotientGroup.lift ⁅(⊤ : Subgroup F), f.ker⁆ f Subgroup.commutator_le_right

theorem hopfLift_mk' (f : F →* G) (x : F) :
    hopfLift f (QuotientGroup.mk' ⁅(⊤ : Subgroup F), f.ker⁆ x) = f x :=
  rfl

/-- The **Hopf cover** `[F,F]/[F,R]`, as the image of `[F,F]` in `F ⧸ [F,R]`. -/
def hopfCover (f : F →* G) : Subgroup (F ⧸ ⁅(⊤ : Subgroup F), f.ker⁆) :=
  (commutator F).map (QuotientGroup.mk' ⁅(⊤ : Subgroup F), f.ker⁆)

theorem mk'_mem_hopfCover (f : F →* G) {x : F} (hx : x ∈ commutator F) :
    QuotientGroup.mk' ⁅(⊤ : Subgroup F), f.ker⁆ x ∈ hopfCover f :=
  Subgroup.mem_map_of_mem _ hx

/-- The projection `[F,F]/[F,R] → G`. -/
def hopfCoverProjection (f : F →* G) : hopfCover f →* G :=
  (hopfLift f).comp (hopfCover f).subtype

theorem hopfCoverProjection_mk' (f : F →* G) (x : F)
    (hx : QuotientGroup.mk' ⁅(⊤ : Subgroup F), f.ker⁆ x ∈ hopfCover f) :
    hopfCoverProjection f ⟨QuotientGroup.mk' ⁅(⊤ : Subgroup F), f.ker⁆ x, hx⟩ = f x :=
  rfl

/-- For perfect `G`, the projection of the Hopf cover is surjective. -/
theorem hopfCoverProjection_surjective (f : F →* G) (hf : Function.Surjective f)
    (hGp : commutator G = ⊤) : Function.Surjective (hopfCoverProjection f) := by
  intro g
  have hg : g ∈ commutator G := by
    rw [hGp]
    exact Subgroup.mem_top g
  rw [← map_commutator_of_surjective f hf] at hg
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
  exact ⟨⟨QuotientGroup.mk' ⁅(⊤ : Subgroup F), f.ker⁆ x, mk'_mem_hopfCover f hx⟩,
    hopfCoverProjection_mk' f x (mk'_mem_hopfCover f hx)⟩

/-- The kernel of the Hopf cover projection is central. -/
theorem hopfCoverProjection_ker_le_center (f : F →* G) :
    (hopfCoverProjection f).ker ≤ Subgroup.center (hopfCover f) := by
  intro e he
  obtain ⟨x, hxc, hxe⟩ := Subgroup.mem_map.mp e.2
  have h2 : hopfCoverProjection f e = f x := by
    have h3 : e = ⟨QuotientGroup.mk' ⁅(⊤ : Subgroup F), f.ker⁆ x, mk'_mem_hopfCover f hxc⟩ :=
      Subtype.ext hxe.symm
    rw [h3, hopfCoverProjection_mk']
  have hfx : x ∈ f.ker := by
    rw [MonoidHom.mem_ker, ← h2]
    exact MonoidHom.mem_ker.mp he
  have hc : (e : F ⧸ ⁅(⊤ : Subgroup F), f.ker⁆) ∈
      Subgroup.center (F ⧸ ⁅(⊤ : Subgroup F), f.ker⁆) := by
    rw [← hxe]
    exact mk'_mem_center_of_mem f.ker hfx
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact Subgroup.mem_center_iff.mp hc g

/-- For perfect `G`, the Hopf cover is contained in its own commutator. -/
theorem hopfCover_le_commutator (f : F →* G) (hf : Function.Surjective f)
    (hGp : commutator G = ⊤) : hopfCover f ≤ ⁅hopfCover f, hopfCover f⁆ := by
  have hdec : ∀ a : F, ∃ y ∈ commutator F, y⁻¹ * a ∈ f.ker := by
    intro a
    have ha : f a ∈ commutator G := by
      rw [hGp]
      exact Subgroup.mem_top _
    rw [← map_commutator_of_surjective f hf] at ha
    obtain ⟨y, hy, hya⟩ := Subgroup.mem_map.mp ha
    refine ⟨y, hy, ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hya, inv_mul_cancel]
  have hle : commutator F ≤
      ⁅hopfCover f, hopfCover f⁆.comap (QuotientGroup.mk' ⁅(⊤ : Subgroup F), f.ker⁆) := by
    rw [_root_.commutator_def F, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨y, hy, hyr⟩ := hdec a
    obtain ⟨z, hz, hzr⟩ := hdec b
    have key := commutatorElement_mul_mul_of_mem_center
      (QuotientGroup.mk' ⁅(⊤ : Subgroup F), f.ker⁆ y)
      (QuotientGroup.mk' ⁅(⊤ : Subgroup F), f.ker⁆ z)
      _ _ (mk'_mem_center_of_mem f.ker hyr) (mk'_mem_center_of_mem f.ker hzr)
    rw [← map_mul (QuotientGroup.mk' ⁅(⊤ : Subgroup F), f.ker⁆) y (y⁻¹ * a),
      ← map_mul (QuotientGroup.mk' ⁅(⊤ : Subgroup F), f.ker⁆) z (z⁻¹ * b),
      mul_inv_cancel_left, mul_inv_cancel_left] at key
    rw [Subgroup.mem_comap, map_commutatorElement, key]
    exact Subgroup.commutator_mem_commutator (mk'_mem_hopfCover f hy) (mk'_mem_hopfCover f hz)
  exact Subgroup.map_le_iff_le_comap.mpr hle

/-- For perfect `G`, the Hopf cover is perfect. -/
theorem commutator_hopfCover_eq_top (f : F →* G) (hf : Function.Surjective f)
    (hGp : commutator G = ⊤) : commutator (hopfCover f) = ⊤ := by
  rw [eq_top_iff]
  intro e _
  have h1 : (hopfCover f).subtype e ∈ ⁅hopfCover f, hopfCover f⁆ :=
    hopfCover_le_commutator f hf hGp e.2
  rw [← Subgroup.map_subtype_commutator (hopfCover f)] at h1
  exact (Subgroup.mem_map_iff_mem (hopfCover f).subtype_injective).mp h1

/-- **The Hopf cover `[F,F]/[F,R] ↠ G` is a perfect central extension** of a perfect group `G`. -/
def hopfCoverExtension (f : F →* G) (hf : Function.Surjective f) (hGp : commutator G = ⊤) :
    GroupApproximation.CentralExtension (hopfCover f) G where
  projection := hopfCoverProjection f
  surjective := hopfCoverProjection_surjective f hf hGp
  ker_le_center := hopfCoverProjection_ker_le_center f

/-- If the Hopf cover projection is injective, then `R ∩ [F,F] ≤ [F,R]`. -/
theorem ker_inf_commutator_le_of_hopfCoverProjection_injective (f : F →* G)
    (hinj : Function.Injective (hopfCoverProjection f)) :
    f.ker ⊓ commutator F ≤ ⁅(⊤ : Subgroup F), f.ker⁆ := by
  intro x hx
  obtain ⟨hxk, hxc⟩ := Subgroup.mem_inf.mp hx
  have h2 : hopfCoverProjection f
      ⟨QuotientGroup.mk' ⁅(⊤ : Subgroup F), f.ker⁆ x, mk'_mem_hopfCover f hxc⟩ =
      hopfCoverProjection f 1 := by
    rw [map_one, hopfCoverProjection_mk']
    exact MonoidHom.mem_ker.mp hxk
  exact (mk'_eq_one_iff ⁅(⊤ : Subgroup F), f.ker⁆ x).mp (congrArg Subtype.val (hinj h2))

end Cover

/-- **Superperfect implies trivial Hopf multiplier** for perfect `G : Type`: apply
superperfectness to the Hopf cover of `FreeGroup.prod : FreeGroup G ↠ G`. -/
theorem hopfMultiplierTrivial_of_isSuperperfect {G : Type} [Group G] (hGp : commutator G = ⊤)
    (h : LVSuperperfect.IsSuperperfect G) : HopfMultiplierTrivial G :=
  (hopfMultiplierTrivial_iff (FreeGroup.prod : FreeGroup G →* G) FreeGroup.prod_surjective).mpr
    (ker_inf_commutator_le_of_hopfCoverProjection_injective (FreeGroup.prod : FreeGroup G →* G)
      (h ↥(hopfCover (FreeGroup.prod : FreeGroup G →* G))
        (hopfCoverExtension (FreeGroup.prod : FreeGroup G →* G) FreeGroup.prod_surjective hGp)
        (commutator_hopfCover_eq_top (FreeGroup.prod : FreeGroup G →* G)
          FreeGroup.prod_surjective hGp)))

/-- **For a perfect group, superperfect ⇔ trivial Hopf multiplier** (`H₂(G; ℤ) = 0`).
(`simple_kazhdan_sofic_group.tex` l.733-735.) -/
theorem hopfMultiplierTrivial_iff_isSuperperfect {G : Type} [Group G] (hGp : commutator G = ⊤) :
    HopfMultiplierTrivial G ↔ LVSuperperfect.IsSuperperfect G :=
  ⟨isSuperperfect_of_hopfMultiplierTrivial, hopfMultiplierTrivial_of_isSuperperfect hGp⟩

end GroupApproximation.Full.LVHopf
