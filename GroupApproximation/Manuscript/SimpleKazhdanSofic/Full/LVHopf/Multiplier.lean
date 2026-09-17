import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVHopf.Basic

/-!
# The Hopf multiplier and independence of presentation (lane LVHopf, leaf T1b.iv)

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735 (via `K₂(4, L_{𝔽₂}(1,2)) = ⊥`, Khanh
arXiv:2609.08428, Thm 5.1).  For a surjection `f : F ↠ G` with kernel `R`, the **Hopf multiplier**
is `(R ∩ [F,F]) / [F,R]`.  Hopf's formula identifies it with `H₂(G; ℤ)` when `F` is free.  Here it
is defined as a subgroup of `F ⧸ [F, R]`:

* `hopfMultiplier f := (R ⊓ [F,F]).map (F ↠ F ⧸ [F,R])`.
* `hopfQuotientEquiv f : (R ⊓ [F,F]) ⧸ [F,R] ≃* hopfMultiplier f`: the literal subquotient form.
* `hopfMultiplier_eq_bot_iff`: the multiplier vanishes iff `R ⊓ [F,F] ≤ [F,R]`.
* `hopfMultiplierMap`: functoriality along a map of presentations.
* `hopfMultiplierEquivOfLifts`, `hopfMultiplierEquiv`: **independence of presentation**.  Two free
  presentations of `G`, in any universes, have isomorphic multipliers.
* `HopfMultiplierTrivial G`: `H₂(G; ℤ) = 0` in Hopf form.  `hopfMultiplierTrivial_iff`: it suffices
  to check one free presentation.
-/

namespace GroupApproximation.Full.LVHopf

open scoped commutatorElement

universe u v w u' v'

section Multiplier

variable {F : Type u} {G : Type v} [Group F] [Group G]

/-- **Hopf multiplier** of a surjection `f : F ↠ G` with kernel `R`: the image of `R ∩ [F,F]` in
`F ⧸ [F, R]`, i.e. `(R ∩ [F,F]) / [F,R]` (Hopf's formula for `H₂(G; ℤ)` when `F` is free).
(`simple_kazhdan_sofic_group.tex` l.733-735.) -/
def hopfMultiplier (f : F →* G) : Subgroup (F ⧸ ⁅(⊤ : Subgroup F), f.ker⁆) :=
  (f.ker ⊓ commutator F).map (QuotientGroup.mk' ⁅(⊤ : Subgroup F), f.ker⁆)

theorem mem_hopfMultiplier (f : F →* G) {y : F ⧸ ⁅(⊤ : Subgroup F), f.ker⁆} :
    y ∈ hopfMultiplier f ↔
      ∃ x ∈ f.ker ⊓ commutator F, QuotientGroup.mk' ⁅(⊤ : Subgroup F), f.ker⁆ x = y :=
  Iff.rfl

/-- The Hopf multiplier vanishes iff `R ∩ [F,F] ≤ [F,R]`. -/
theorem hopfMultiplier_eq_bot_iff (f : F →* G) :
    hopfMultiplier f = ⊥ ↔ f.ker ⊓ commutator F ≤ ⁅(⊤ : Subgroup F), f.ker⁆ := by
  rw [hopfMultiplier, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']

/-- The kernel of `R ∩ [F,F] → F ⧸ [F,R]` is `[F,R]`, as a subgroup of `R ∩ [F,F]`. -/
theorem hopfSubgroupMap_ker (f : F →* G) :
    ((QuotientGroup.mk' ⁅(⊤ : Subgroup F), f.ker⁆).subgroupMap (f.ker ⊓ commutator F)).ker =
      ⁅(⊤ : Subgroup F), f.ker⁆.subgroupOf (f.ker ⊓ commutator F) := by
  ext y
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hy
    exact (mk'_eq_one_iff ⁅(⊤ : Subgroup F), f.ker⁆ (y : F)).mp (congrArg Subtype.val hy)
  · intro hy
    exact Subtype.ext ((mk'_eq_one_iff ⁅(⊤ : Subgroup F), f.ker⁆ (y : F)).mpr hy)

/-- **Hopf formula, literal subquotient form**: `(R ∩ [F,F]) / [F,R] ≃* hopfMultiplier f`. -/
noncomputable def hopfQuotientEquiv (f : F →* G) :
    (f.ker ⊓ commutator F) ⧸ ⁅(⊤ : Subgroup F), f.ker⁆.subgroupOf (f.ker ⊓ commutator F) ≃*
      hopfMultiplier f :=
  (QuotientGroup.quotientMulEquivOfEq (hopfSubgroupMap_ker f)).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective
      ((QuotientGroup.mk' ⁅(⊤ : Subgroup F), f.ker⁆).subgroupMap (f.ker ⊓ commutator F))
      ((QuotientGroup.mk' ⁅(⊤ : Subgroup F), f.ker⁆).subgroupMap_surjective
        (f.ker ⊓ commutator F)))

end Multiplier

section Functoriality

variable {F : Type u} {G : Type v} {F' : Type u'} {G' : Type v'} [Group F] [Group G] [Group F']
  [Group G']

/-- A map of presentations `φ : F → F'` with `φ (ker f) ≤ ker g` maps `[F, ker f]` into
`[F', ker g]`. -/
theorem commutator_ker_le_comap (f : F →* G) (g : F' →* G') (φ : F →* F')
    (hker : f.ker ≤ g.ker.comap φ) :
    ⁅(⊤ : Subgroup F), f.ker⁆ ≤ ⁅(⊤ : Subgroup F'), g.ker⁆.comap φ := by
  rw [Subgroup.commutator_le]
  intro a _ b hb
  rw [Subgroup.mem_comap, map_commutatorElement]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top (φ a))
    (Subgroup.mem_comap.mp (hker hb))

/-- The induced map `F ⧸ [F, ker f] → F' ⧸ [F', ker g]`. -/
def hopfQuotientMap (f : F →* G) (g : F' →* G') (φ : F →* F') (hker : f.ker ≤ g.ker.comap φ) :
    F ⧸ ⁅(⊤ : Subgroup F), f.ker⁆ →* F' ⧸ ⁅(⊤ : Subgroup F'), g.ker⁆ :=
  QuotientGroup.map _ _ φ (commutator_ker_le_comap f g φ hker)

theorem hopfQuotientMap_mk' (f : F →* G) (g : F' →* G') (φ : F →* F')
    (hker : f.ker ≤ g.ker.comap φ) (x : F) :
    hopfQuotientMap f g φ hker (QuotientGroup.mk' ⁅(⊤ : Subgroup F), f.ker⁆ x) =
      QuotientGroup.mk' ⁅(⊤ : Subgroup F'), g.ker⁆ (φ x) :=
  rfl

/-- The induced map carries the Hopf multiplier of `f` into that of `g`. -/
theorem map_hopfMultiplier_le (f : F →* G) (g : F' →* G') (φ : F →* F')
    (hker : f.ker ≤ g.ker.comap φ) :
    (hopfMultiplier f).map (hopfQuotientMap f g φ hker) ≤ hopfMultiplier g := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
  obtain ⟨x, hx, rfl⟩ := (mem_hopfMultiplier f).mp hz
  obtain ⟨hxk, hxc⟩ := Subgroup.mem_inf.mp hx
  refine (mem_hopfMultiplier g).mpr ⟨φ x, Subgroup.mem_inf.mpr ⟨Subgroup.mem_comap.mp (hker hxk),
    map_commutator_le φ (Subgroup.mem_map_of_mem φ hxc)⟩, ?_⟩
  exact (hopfQuotientMap_mk' f g φ hker x).symm

/-- **Functoriality of the Hopf multiplier** along a map of presentations. -/
def hopfMultiplierMap (f : F →* G) (g : F' →* G') (φ : F →* F')
    (hker : f.ker ≤ g.ker.comap φ) : hopfMultiplier f →* hopfMultiplier g where
  toFun y := ⟨hopfQuotientMap f g φ hker y,
    map_hopfMultiplier_le f g φ hker (Subgroup.mem_map_of_mem _ y.2)⟩
  map_one' := Subtype.ext (map_one (hopfQuotientMap f g φ hker))
  map_mul' y z := Subtype.ext (map_mul (hopfQuotientMap f g φ hker) y z)

end Functoriality

section Independence

variable {F : Type u} {F' : Type v} {G : Type w} [Group F] [Group F'] [Group G]

/-- If `g ∘ φ = f`, then `φ (ker f) ≤ ker g`. -/
theorem ker_le_comap_ker_of_comp_eq (f : F →* G) (g : F' →* G) (φ : F →* F')
    (hφ : g.comp φ = f) : f.ker ≤ g.ker.comap φ := by
  intro x hx
  rw [Subgroup.mem_comap, MonoidHom.mem_ker]
  have h1 : g (φ x) = f x := DFunLike.congr_fun hφ x
  rw [h1]
  exact MonoidHom.mem_ker.mp hx

/-- Round trip of lifts is the identity on the Hopf multiplier. -/
theorem hopfQuotientMap_comp_eq_self (f : F →* G) (g : F' →* G) (φ : F →* F') (ψ : F' →* F)
    (hφ : g.comp φ = f) (hψ : f.comp ψ = g) {z : F ⧸ ⁅(⊤ : Subgroup F), f.ker⁆}
    (hz : z ∈ hopfMultiplier f) :
    hopfQuotientMap g f ψ (ker_le_comap_ker_of_comp_eq g f ψ hψ)
      (hopfQuotientMap f g φ (ker_le_comap_ker_of_comp_eq f g φ hφ) z) = z := by
  have hcomp : f.comp (ψ.comp φ) = f.comp (MonoidHom.id F) := by
    refine MonoidHom.ext fun x => ?_
    have h1 : f (ψ (φ x)) = g (φ x) := DFunLike.congr_fun hψ (φ x)
    have h2 : g (φ x) = f x := DFunLike.congr_fun hφ x
    exact h1.trans h2
  obtain ⟨x, hx, rfl⟩ := (mem_hopfMultiplier f).mp hz
  exact mk'_comp_eq_of_mem_commutator f (ψ.comp φ) (MonoidHom.id F) hcomp
    (Subgroup.mem_inf.mp hx).2

/-- **Independence of presentation.**  If `f : F ↠ G` and `g : F' ↠ G` admit lifts `φ : F → F'`
and `ψ : F' → F` over `G`, then their Hopf multipliers are isomorphic.  (Hopf 1942; Brown,
*Cohomology of Groups*, II.5.  `simple_kazhdan_sofic_group.tex` l.733-735.) -/
def hopfMultiplierEquivOfLifts (f : F →* G) (g : F' →* G) (φ : F →* F') (ψ : F' →* F)
    (hφ : g.comp φ = f) (hψ : f.comp ψ = g) : hopfMultiplier f ≃* hopfMultiplier g :=
  MonoidHom.toMulEquiv
    (hopfMultiplierMap f g φ (ker_le_comap_ker_of_comp_eq f g φ hφ))
    (hopfMultiplierMap g f ψ (ker_le_comap_ker_of_comp_eq g f ψ hψ))
    (MonoidHom.ext fun y => Subtype.ext (hopfQuotientMap_comp_eq_self f g φ ψ hφ hψ y.2))
    (MonoidHom.ext fun y => Subtype.ext (hopfQuotientMap_comp_eq_self g f ψ φ hψ hφ y.2))

end Independence

/-- **Independence of presentation for free presentations**: any two free presentations of `G`, in
any universes, have isomorphic Hopf multipliers. -/
noncomputable def hopfMultiplierEquiv {α : Type u} {β : Type v} {G : Type w} [Group G]
    (f : FreeGroup α →* G) (g : FreeGroup β →* G) (hf : Function.Surjective f)
    (hg : Function.Surjective g) : hopfMultiplier f ≃* hopfMultiplier g :=
  hopfMultiplierEquivOfLifts f g (Classical.choose (exists_freeGroup_lift f g hg))
    (Classical.choose (exists_freeGroup_lift g f hf))
    (Classical.choose_spec (exists_freeGroup_lift f g hg))
    (Classical.choose_spec (exists_freeGroup_lift g f hf))

/-- A subgroup isomorphic to the trivial subgroup is trivial. -/
theorem eq_bot_of_mulEquiv {M : Type u} {N : Type v} [Group M] [Group N] {H : Subgroup M}
    {K : Subgroup N} (e : H ≃* K) (hH : H = ⊥) : K = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  have h1 : ((e.symm ⟨y, hy⟩ : H) : M) = 1 := Subgroup.mem_bot.mp (hH.le (e.symm ⟨y, hy⟩).2)
  have h2 : e.symm ⟨y, hy⟩ = 1 := Subtype.ext h1
  have h3 : (⟨y, hy⟩ : K) = 1 := by
    rw [← e.apply_symm_apply ⟨y, hy⟩, h2, map_one]
  exact congrArg Subtype.val h3

/-- **Trivial Schur multiplier** (`H₂(G; ℤ) = 0`) in Hopf form: for every free presentation
`R ↪ F ↠ G` (with `F = FreeGroup α`, `α : Type u`), `R ∩ [F,F] ≤ [F,R]`.
(`simple_kazhdan_sofic_group.tex` l.733-735.) -/
def HopfMultiplierTrivial (G : Type u) [Group G] : Prop :=
  ∀ (α : Type u) (f : FreeGroup α →* G), Function.Surjective f →
    f.ker ⊓ commutator (FreeGroup α) ≤ ⁅(⊤ : Subgroup (FreeGroup α)), f.ker⁆

/-- One free presentation (in any universe) suffices to check `HopfMultiplierTrivial`. -/
theorem hopfMultiplierTrivial_iff {G : Type u} [Group G] {β : Type v} (f₀ : FreeGroup β →* G)
    (hf₀ : Function.Surjective f₀) :
    HopfMultiplierTrivial G ↔
      f₀.ker ⊓ commutator (FreeGroup β) ≤ ⁅(⊤ : Subgroup (FreeGroup β)), f₀.ker⁆ := by
  constructor
  · intro h
    have h1 : hopfMultiplier (FreeGroup.prod : FreeGroup G →* G) = ⊥ :=
      (hopfMultiplier_eq_bot_iff _).mpr (h G FreeGroup.prod FreeGroup.prod_surjective)
    exact (hopfMultiplier_eq_bot_iff f₀).mp
      (eq_bot_of_mulEquiv (hopfMultiplierEquiv FreeGroup.prod f₀ FreeGroup.prod_surjective hf₀) h1)
  · intro h α f hf
    exact (hopfMultiplier_eq_bot_iff f).mp
      (eq_bot_of_mulEquiv (hopfMultiplierEquiv f₀ f hf₀ hf) ((hopfMultiplier_eq_bot_iff f₀).mpr h))

end GroupApproximation.Full.LVHopf
