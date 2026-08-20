import GroupApproximation.Sofic.WeakMFNonsoficDouble
import GroupApproximation.Sofic.SoficTransfer

/-!
# The iterated amalgam `⋆_Γ G` over an arbitrary vertex set

The Kun--Thom/Shulman double construction is not one group but a family.  Over
one inclusion `Γ ≤ G` it produces

* the two-vertex symmetric double `G *_Γ G`;
* the infinite line double `*_Γ G` of Gao--Kunnawalkam Elayavalli--Mj
  Question 1.6;
* the `|K|`-vertex amalgam `G *_Γ ⋯ *_Γ G` which is the Bass--Serre covering
  kernel of the free-lamp amalgam `G *_Γ (Γ × K)`.

All three are the same construction on different index sets, and this file
builds it once: `IteratedDouble G Γ ι` is the wide amalgam of one copy of `G`
per element of `ι`, glued along one common copy of `Γ`.  `Sofic/LineDouble`
does the `ι = ℤ` case by hand; nothing there is changed.

## What is proved here

Everything is unconditional and purely algebraic.

* the construction, its vertex embeddings (`inIterated_injective`) and its
  countability;
* **relabelling**: a map of index sets induces a homomorphism
  (`iteratedRelabel`), functorially (`iteratedRelabel_comp`,
  `iteratedRelabel_id`), and relabelling along a map with a left inverse is
  injective (`iteratedRelabel_injective_of_leftInverse`).  In particular a
  bijection of index sets induces an isomorphism (`iteratedEquivOfEquiv`); the
  lamp group's permutation action in `Sofic/FreeLampKernelSplitting` is built
  from `iteratedRelabel` in exactly this way;
* **the two-vertex double sits inside**: for any two distinct indices the
  symmetric double embeds (`doubleToIterated_injective`), by the same
  retraction argument that `LineDouble` uses for the line, and hence
  soficity descends and non-soficity ascends.

The extensionality helper `iteratedDouble_hom_ext` is stated once, because
every later proof about the construction is an application of it.
-/

namespace GroupApproximation

open Monoid

/-! ## The construction -/

/-- One copy of `G` at every vertex of the index set. -/
abbrev IteratedFactor (G : Type) (ι : Type) : ι → Type := fun _ ↦ G

instance iteratedFactorGroup (G : Type) [Group G] (ι : Type) :
    ∀ i : ι, Group (IteratedFactor G ι i) :=
  fun _ ↦ inferInstanceAs (Group G)

/-- Every edge identification is the fixed inclusion `Γ ↪ G`. -/
def iteratedMap (G : Type) [Group G] (Γ : Subgroup G) (ι : Type) :
    ∀ i : ι, ↥Γ →* IteratedFactor G ι i :=
  fun _ ↦ Γ.subtype

theorem iteratedMap_injective (G : Type) [Group G] (Γ : Subgroup G) (ι : Type) :
    ∀ i : ι, Function.Injective (iteratedMap G Γ ι i) :=
  fun _ ↦ Γ.subtype_injective

/-- The `ι`-fold amalgam `⋆_{Γ, i ∈ ι} G`. -/
abbrev IteratedDouble (G : Type) [Group G] (Γ : Subgroup G) (ι : Type) : Type :=
  PushoutI (iteratedMap G Γ ι)

/-- The vertex-group embedding at the index `i`. -/
def inIterated (G : Type) [Group G] (Γ : Subgroup G) (ι : Type) (i : ι) :
    G →* IteratedDouble G Γ ι :=
  PushoutI.of (φ := iteratedMap G Γ ι) i

theorem inIterated_injective (G : Type) [Group G] (Γ : Subgroup G) (ι : Type)
    (i : ι) : Function.Injective (inIterated G Γ ι i) :=
  PushoutI.of_injective (iteratedMap_injective G Γ ι) i

@[simp] theorem inIterated_coe_subgroup (G : Type) [Group G] (Γ : Subgroup G)
    (ι : Type) (i : ι) (γ : ↥Γ) :
    inIterated G Γ ι i (γ : G) = PushoutI.base (iteratedMap G Γ ι) γ :=
  PushoutI.of_apply_eq_base (iteratedMap G Γ ι) i γ

instance iteratedFactorCountable (G : Type) [Group G] [Countable G] (ι : Type) :
    ∀ i : ι, Countable (IteratedFactor G ι i) :=
  fun _ ↦ inferInstanceAs (Countable G)

instance iteratedDoubleCountable (G : Type) [Group G] [Countable G]
    (Γ : Subgroup G) (ι : Type) [Countable ι] :
    Countable (IteratedDouble G Γ ι) := by
  haveI hΓ : Countable ↥Γ := Subtype.countable
  haveI h0 : Countable (FreeMonoid (Σ i : ι, IteratedFactor G ι i)) :=
    inferInstanceAs (Countable (List (Σ i : ι, IteratedFactor G ι i)))
  haveI h1 : Countable (CoprodI (IteratedFactor G ι)) :=
    Con.mk'_surjective.countable
  haveI h2 : Countable
      (FreeMonoid (CoprodI (IteratedFactor G ι) ⊕ ↥Γ)) :=
    inferInstanceAs (Countable (List (CoprodI (IteratedFactor G ι) ⊕ ↥Γ)))
  haveI h3 : Countable (Coprod (CoprodI (IteratedFactor G ι)) ↥Γ) :=
    Con.mk'_surjective.countable
  exact Con.mk'_surjective.countable

/-- The extensionality principle used by every proof below: two homomorphisms
out of the amalgam agree as soon as they agree on each vertex group and on the
common edge group. -/
theorem iteratedDouble_hom_ext (G : Type) [Group G] (Γ : Subgroup G)
    {ι : Type} {M : Type} [Monoid M]
    {f g : IteratedDouble G Γ ι →* M}
    (hof : ∀ (i : ι) (x : G), f (inIterated G Γ ι i x) = g (inIterated G Γ ι i x))
    (hbase : ∀ γ : ↥Γ, f (PushoutI.base (iteratedMap G Γ ι) γ)
      = g (PushoutI.base (iteratedMap G Γ ι) γ)) : f = g := by
  refine PushoutI.hom_ext (fun i ↦ ?_) ?_
  · ext x
    exact hof i x
  · ext γ
    exact hbase γ

/-- The same principle for automorphisms of the amalgam, which is the shape
the lamp group's index action needs. -/
theorem iteratedDouble_mulAut_ext (G : Type) [Group G] (Γ : Subgroup G)
    {ι : Type} {f g : MulAut (IteratedDouble G Γ ι)}
    (hof : ∀ (i : ι) (x : G), f (inIterated G Γ ι i x) = g (inIterated G Γ ι i x))
    (hbase : ∀ γ : ↥Γ, f (PushoutI.base (iteratedMap G Γ ι) γ)
      = g (PushoutI.base (iteratedMap G Γ ι) γ)) : f = g := by
  have h : f.toMonoidHom = g.toMonoidHom :=
    iteratedDouble_hom_ext G Γ hof hbase
  exact MulEquiv.ext (fun x ↦ DFunLike.congr_fun h x)

/-! ## Relabelling the vertex set -/

/-- The factor maps of a relabelling. -/
def iteratedRelabelMaps (G : Type) [Group G] (Γ : Subgroup G) {ι κ : Type}
    (f : ι → κ) : ∀ i : ι, IteratedFactor G ι i →* IteratedDouble G Γ κ :=
  fun i ↦ inIterated G Γ κ (f i)

theorem iteratedRelabelMaps_comp (G : Type) [Group G] (Γ : Subgroup G)
    {ι κ : Type} (f : ι → κ) :
    ∀ i : ι, (iteratedRelabelMaps G Γ f i).comp (iteratedMap G Γ ι i)
      = PushoutI.base (iteratedMap G Γ κ) :=
  fun i ↦ PushoutI.of_comp_eq_base (f i)

/-- Relabelling the vertex set along an arbitrary map of index sets. -/
def iteratedRelabel (G : Type) [Group G] (Γ : Subgroup G) {ι κ : Type}
    (f : ι → κ) : IteratedDouble G Γ ι →* IteratedDouble G Γ κ :=
  PushoutI.lift (iteratedRelabelMaps G Γ f) (PushoutI.base (iteratedMap G Γ κ))
    (iteratedRelabelMaps_comp G Γ f)

@[simp] theorem iteratedRelabel_inIterated (G : Type) [Group G] (Γ : Subgroup G)
    {ι κ : Type} (f : ι → κ) (i : ι) (x : G) :
    iteratedRelabel G Γ f (inIterated G Γ ι i x) = inIterated G Γ κ (f i) x :=
  PushoutI.lift_of _ _ _ _

@[simp] theorem iteratedRelabel_base (G : Type) [Group G] (Γ : Subgroup G)
    {ι κ : Type} (f : ι → κ) (γ : ↥Γ) :
    iteratedRelabel G Γ f (PushoutI.base (iteratedMap G Γ ι) γ)
      = PushoutI.base (iteratedMap G Γ κ) γ :=
  PushoutI.lift_base _ _ _ _

@[simp] theorem iteratedRelabel_id (G : Type) [Group G] (Γ : Subgroup G)
    (ι : Type) : iteratedRelabel G Γ (id : ι → ι) = MonoidHom.id _ := by
  refine iteratedDouble_hom_ext G Γ (fun i x ↦ ?_) (fun γ ↦ ?_)
  · simp
  · simp

theorem iteratedRelabel_comp (G : Type) [Group G] (Γ : Subgroup G)
    {ι κ μ : Type} (f : ι → κ) (h : κ → μ) :
    (iteratedRelabel G Γ h).comp (iteratedRelabel G Γ f)
      = iteratedRelabel G Γ (h ∘ f) := by
  refine iteratedDouble_hom_ext G Γ (fun i x ↦ ?_) (fun γ ↦ ?_)
  · simp [Function.comp_apply]
  · simp

/-- A left inverse on index sets induces a left inverse on amalgams. -/
theorem iteratedRelabel_leftInverse (G : Type) [Group G] (Γ : Subgroup G)
    {ι κ : Type} {f : ι → κ} {g : κ → ι} (hgf : ∀ i, g (f i) = i) :
    Function.LeftInverse (iteratedRelabel G Γ g) (iteratedRelabel G Γ f) := by
  intro x
  have hc : (iteratedRelabel G Γ g).comp (iteratedRelabel G Γ f)
      = MonoidHom.id _ := by
    rw [iteratedRelabel_comp]
    have hid : (g ∘ f) = (id : ι → ι) := funext hgf
    rw [hid, iteratedRelabel_id]
  exact DFunLike.congr_fun hc x

theorem iteratedRelabel_injective_of_leftInverse (G : Type) [Group G]
    (Γ : Subgroup G) {ι κ : Type} {f : ι → κ} {g : κ → ι}
    (hgf : ∀ i, g (f i) = i) :
    Function.Injective (iteratedRelabel G Γ f) :=
  (iteratedRelabel_leftInverse G Γ hgf).injective

/-- A bijection of vertex sets is an isomorphism of amalgams.  This is the
form the lamp group's index action takes. -/
def iteratedEquivOfEquiv (G : Type) [Group G] (Γ : Subgroup G) {ι κ : Type}
    (e : ι ≃ κ) : IteratedDouble G Γ ι ≃* IteratedDouble G Γ κ where
  toFun := iteratedRelabel G Γ e
  invFun := iteratedRelabel G Γ e.symm
  left_inv := iteratedRelabel_leftInverse G Γ
    (f := (e : ι → κ)) (g := (e.symm : κ → ι)) (fun i ↦ e.symm_apply_apply i)
  right_inv := iteratedRelabel_leftInverse G Γ
    (f := (e.symm : κ → ι)) (g := (e : ι → κ)) (fun j ↦ e.apply_symm_apply j)
  map_mul' := (iteratedRelabel G Γ (e : ι → κ)).map_mul

@[simp] theorem iteratedEquivOfEquiv_inIterated (G : Type) [Group G]
    (Γ : Subgroup G) {ι κ : Type} (e : ι ≃ κ) (i : ι) (x : G) :
    iteratedEquivOfEquiv G Γ e (inIterated G Γ ι i x)
      = inIterated G Γ κ (e i) x := by
  show iteratedRelabel G Γ (e : ι → κ) (inIterated G Γ ι i x) = _
  rw [iteratedRelabel_inIterated]

@[simp] theorem iteratedEquivOfEquiv_base (G : Type) [Group G] (Γ : Subgroup G)
    {ι κ : Type} (e : ι ≃ κ) (γ : ↥Γ) :
    iteratedEquivOfEquiv G Γ e (PushoutI.base (iteratedMap G Γ ι) γ)
      = PushoutI.base (iteratedMap G Γ κ) γ := by
  show iteratedRelabel G Γ (e : ι → κ) (PushoutI.base (iteratedMap G Γ ι) γ) = _
  rw [iteratedRelabel_base]

/-! ## The two-vertex double inside the amalgam -/

/-- Two chosen vertices of the index set: `false` goes to `i`, `true` to
`j`. -/
def doubleIndex {ι : Type} (i j : ι) : Bool → ι
  | false => i
  | true => j

/-- The factor maps sending the two vertex groups of the symmetric double to
the vertices `i` and `j` of the amalgam. -/
def doubleToIteratedMaps (G : Type) [Group G] (Γ : Subgroup G) {ι : Type}
    (i j : ι) : ∀ b, DoubleFactor G b →* IteratedDouble G Γ ι :=
  fun b ↦ inIterated G Γ ι (doubleIndex i j b)

theorem doubleToIteratedMaps_comp (G : Type) [Group G] (Γ : Subgroup G)
    {ι : Type} (i j : ι) :
    ∀ b, (doubleToIteratedMaps G Γ i j b).comp (doubleMap G Γ b)
      = PushoutI.base (iteratedMap G Γ ι) :=
  fun b ↦ PushoutI.of_comp_eq_base (doubleIndex i j b)

/-- The canonical map from the two-vertex double onto the vertices `i` and
`j`. -/
def doubleToIterated (G : Type) [Group G] (Γ : Subgroup G) {ι : Type}
    (i j : ι) : SymmetricDouble G Γ →* IteratedDouble G Γ ι :=
  PushoutI.lift (doubleToIteratedMaps G Γ i j)
    (PushoutI.base (iteratedMap G Γ ι)) (doubleToIteratedMaps_comp G Γ i j)

@[simp] theorem doubleToIterated_inDouble (G : Type) [Group G] (Γ : Subgroup G)
    {ι : Type} (i j : ι) (b : Bool) (g : G) :
    doubleToIterated G Γ i j (inDouble G Γ b g)
      = inIterated G Γ ι (doubleIndex i j b) g :=
  PushoutI.lift_of _ _ _ _

open scoped Classical in
/-- Collapse the vertex `i` onto the first factor of the two-vertex double and
every other vertex onto the second. -/
noncomputable def iteratedToDoubleMaps (G : Type) [Group G] (Γ : Subgroup G)
    {ι : Type} (i : ι) :
    ∀ k : ι, IteratedFactor G ι k →* SymmetricDouble G Γ :=
  fun k ↦ if k = i then inDouble G Γ false else inDouble G Γ true

open scoped Classical in
theorem iteratedToDoubleMaps_comp (G : Type) [Group G] (Γ : Subgroup G)
    {ι : Type} (i : ι) :
    ∀ k : ι, (iteratedToDoubleMaps G Γ i k).comp (iteratedMap G Γ ι k)
      = PushoutI.base (doubleMap G Γ) := by
  intro k
  by_cases hk : k = i
  · simpa [iteratedToDoubleMaps, iteratedMap, inDouble, doubleMap, hk] using
      (PushoutI.of_comp_eq_base (φ := doubleMap G Γ) false)
  · simpa [iteratedToDoubleMaps, iteratedMap, inDouble, doubleMap, hk] using
      (PushoutI.of_comp_eq_base (φ := doubleMap G Γ) true)

open scoped Classical in
/-- The retraction of the amalgam onto the selected two-vertex double. -/
noncomputable def iteratedToDouble (G : Type) [Group G] (Γ : Subgroup G)
    {ι : Type} (i : ι) : IteratedDouble G Γ ι →* SymmetricDouble G Γ :=
  PushoutI.lift (iteratedToDoubleMaps G Γ i) (PushoutI.base (doubleMap G Γ))
    (iteratedToDoubleMaps_comp G Γ i)

open scoped Classical in
@[simp] theorem iteratedToDouble_inIterated (G : Type) [Group G]
    (Γ : Subgroup G) {ι : Type} (i k : ι) (g : G) :
    iteratedToDouble G Γ i (inIterated G Γ ι k g)
      = if k = i then inDouble G Γ false g else inDouble G Γ true g := by
  unfold iteratedToDouble inIterated
  rw [PushoutI.lift_of]
  by_cases hk : k = i <;> simp [iteratedToDoubleMaps, hk]

/-- The retraction is a left inverse to the two-vertex inclusion, for any pair
of distinct vertices. -/
theorem iteratedToDouble_comp_doubleToIterated (G : Type) [Group G]
    (Γ : Subgroup G) {ι : Type} {i j : ι} (hij : j ≠ i) :
    (iteratedToDouble G Γ i).comp (doubleToIterated G Γ i j)
      = MonoidHom.id _ := by
  classical
  apply PushoutI.hom_ext_nonempty
  intro b
  ext g
  change iteratedToDouble G Γ i (doubleToIterated G Γ i j (inDouble G Γ b g))
    = inDouble G Γ b g
  rw [doubleToIterated_inDouble, iteratedToDouble_inIterated]
  cases b
  · simp [doubleIndex]
  · simp [doubleIndex, hij]

/-- **The two-vertex symmetric double embeds in the amalgam** along any pair of
distinct vertices. -/
theorem doubleToIterated_injective (G : Type) [Group G] (Γ : Subgroup G)
    {ι : Type} {i j : ι} (hij : j ≠ i) :
    Function.Injective (doubleToIterated G Γ i j) :=
  Function.LeftInverse.injective fun x ↦
    DFunLike.congr_fun (iteratedToDouble_comp_doubleToIterated G Γ hij) x

/-! ## The three degenerations

The construction has three boundaries, and `Sofic/InfranormalCompressionPair`
rules out two of them for a compression pair (`IsCompressionPair.ne_bot`,
`IsCompressionPair.ne_top`).  This section says what is on the other side of
each, so that "the compression pair avoids them" is a statement with content.

* one vertex: the amalgam is `G`;
* `Γ = ⊤`: every vertex is glued to every other, and the amalgam is `G` again,
  for any nonempty vertex set;
* `Γ = ⊥`: nothing is glued, and the amalgam is the free product `∗_{i ∈ ι} G`.
-/

/-- The collapse map: forget the vertex labels. -/
def iteratedCollapse (G : Type) [Group G] (Γ : Subgroup G) (ι : Type) :
    IteratedDouble G Γ ι →* G :=
  PushoutI.lift (fun _ ↦ MonoidHom.id G) Γ.subtype
    (fun _ ↦ MonoidHom.id_comp _)

@[simp] theorem iteratedCollapse_inIterated (G : Type) [Group G]
    (Γ : Subgroup G) (ι : Type) (i : ι) (g : G) :
    iteratedCollapse G Γ ι (inIterated G Γ ι i g) = g :=
  PushoutI.lift_of _ _ _ _

@[simp] theorem iteratedCollapse_base (G : Type) [Group G] (Γ : Subgroup G)
    (ι : Type) (γ : ↥Γ) :
    iteratedCollapse G Γ ι (PushoutI.base (iteratedMap G Γ ι) γ) = (γ : G) :=
  PushoutI.lift_base _ _ _ _

/-- **One vertex.**  The amalgam on a single vertex is the group itself. -/
def iteratedUniqueEquiv (G : Type) [Group G] (Γ : Subgroup G) (ι : Type)
    [Unique ι] : IteratedDouble G Γ ι ≃* G where
  toFun := iteratedCollapse G Γ ι
  invFun := inIterated G Γ ι default
  left_inv x := by
    have h : (inIterated G Γ ι default).comp (iteratedCollapse G Γ ι)
        = MonoidHom.id _ := by
      refine iteratedDouble_hom_ext G Γ (fun i g ↦ ?_) (fun γ ↦ ?_)
      · show inIterated G Γ ι default
            (iteratedCollapse G Γ ι (inIterated G Γ ι i g))
          = inIterated G Γ ι i g
        rw [iteratedCollapse_inIterated, Subsingleton.elim (default : ι) i]
      · show inIterated G Γ ι default (iteratedCollapse G Γ ι
            (PushoutI.base (iteratedMap G Γ ι) γ))
          = PushoutI.base (iteratedMap G Γ ι) γ
        rw [iteratedCollapse_base, inIterated_coe_subgroup]
    exact DFunLike.congr_fun h x
  right_inv g := iteratedCollapse_inIterated G Γ ι default g
  map_mul' := (iteratedCollapse G Γ ι).map_mul

/-- **Everything glued.**  Over the whole group as edge group the amalgam
collapses to `G`, for every nonempty vertex set. -/
def iteratedTopEquiv (G : Type) [Group G] (ι : Type) (i₀ : ι) :
    IteratedDouble G (⊤ : Subgroup G) ι ≃* G where
  toFun := iteratedCollapse G ⊤ ι
  invFun := inIterated G ⊤ ι i₀
  left_inv x := by
    have h : (inIterated G ⊤ ι i₀).comp (iteratedCollapse G ⊤ ι)
        = MonoidHom.id _ := by
      refine iteratedDouble_hom_ext G ⊤ (fun i g ↦ ?_) (fun γ ↦ ?_)
      · show inIterated G ⊤ ι i₀
            (iteratedCollapse G ⊤ ι (inIterated G ⊤ ι i g))
          = inIterated G ⊤ ι i g
        rw [iteratedCollapse_inIterated]
        have h₀ : inIterated G ⊤ ι i₀ g
            = PushoutI.base (iteratedMap G (⊤ : Subgroup G) ι)
                ⟨g, Subgroup.mem_top g⟩ :=
          inIterated_coe_subgroup G ⊤ ι i₀ ⟨g, Subgroup.mem_top g⟩
        have hi : inIterated G ⊤ ι i g
            = PushoutI.base (iteratedMap G (⊤ : Subgroup G) ι)
                ⟨g, Subgroup.mem_top g⟩ :=
          inIterated_coe_subgroup G ⊤ ι i ⟨g, Subgroup.mem_top g⟩
        rw [h₀, hi]
      · show inIterated G ⊤ ι i₀ (iteratedCollapse G ⊤ ι
            (PushoutI.base (iteratedMap G (⊤ : Subgroup G) ι) γ))
          = PushoutI.base (iteratedMap G (⊤ : Subgroup G) ι) γ
        rw [iteratedCollapse_base, inIterated_coe_subgroup]
    exact DFunLike.congr_fun h x
  right_inv g := iteratedCollapse_inIterated G ⊤ ι i₀ g
  map_mul' := (iteratedCollapse G (⊤ : Subgroup G) ι).map_mul

/-! ### Nothing glued -/

theorem iteratedBotMaps_comp (G : Type) [Group G] (ι : Type) :
    ∀ i : ι, (CoprodI.of (M := IteratedFactor G ι) (i := i)).comp
        (iteratedMap G (⊥ : Subgroup G) ι i)
      = (1 : ↥(⊥ : Subgroup G) →* CoprodI (IteratedFactor G ι)) := by
  intro i
  ext γ
  have hγ : (γ : G) = 1 := Subgroup.mem_bot.mp γ.2
  show CoprodI.of (M := IteratedFactor G ι) (i := i) (γ : G) = 1
  rw [hγ]
  exact map_one _

/-- The comparison map from the amalgam over the trivial subgroup to the free
product. -/
def iteratedBotToCoprod (G : Type) [Group G] (ι : Type) :
    IteratedDouble G (⊥ : Subgroup G) ι →* CoprodI (IteratedFactor G ι) :=
  PushoutI.lift (fun i ↦ CoprodI.of (M := IteratedFactor G ι) (i := i))
    (1 : ↥(⊥ : Subgroup G) →* CoprodI (IteratedFactor G ι))
    (iteratedBotMaps_comp G ι)

@[simp] theorem iteratedBotToCoprod_inIterated (G : Type) [Group G] (ι : Type)
    (i : ι) (g : G) :
    iteratedBotToCoprod G ι (inIterated G (⊥ : Subgroup G) ι i g)
      = CoprodI.of (M := IteratedFactor G ι) (i := i) g :=
  PushoutI.lift_of _ _ _ _

/-- **Nothing glued.**  Over the trivial subgroup the amalgam is the free
product of the vertex groups. -/
def iteratedBotEquiv (G : Type) [Group G] (ι : Type) :
    IteratedDouble G (⊥ : Subgroup G) ι ≃* CoprodI (IteratedFactor G ι) where
  toFun := iteratedBotToCoprod G ι
  invFun := PushoutI.ofCoprodI
  left_inv x := by
    have h : (PushoutI.ofCoprodI (φ := iteratedMap G (⊥ : Subgroup G) ι)).comp
        (iteratedBotToCoprod G ι) = MonoidHom.id _ := by
      refine iteratedDouble_hom_ext G ⊥ (fun i g ↦ ?_) (fun γ ↦ ?_)
      · -- `inIterated` is `PushoutI.of` by definition, so the goal has to be
        -- restated in its terms before the rewrite can see the pattern
        show PushoutI.ofCoprodI (iteratedBotToCoprod G ι
            (inIterated G (⊥ : Subgroup G) ι i g))
          = inIterated G (⊥ : Subgroup G) ι i g
        rw [iteratedBotToCoprod_inIterated, PushoutI.ofCoprodI_of]
      · have hγ : γ = 1 := Subtype.ext (Subgroup.mem_bot.mp γ.2)
        show PushoutI.ofCoprodI (iteratedBotToCoprod G ι
            (PushoutI.base (iteratedMap G (⊥ : Subgroup G) ι) γ))
          = PushoutI.base (iteratedMap G (⊥ : Subgroup G) ι) γ
        rw [hγ]
        simp
    exact DFunLike.congr_fun h x
  right_inv y := by
    have h : (iteratedBotToCoprod G ι).comp
        (PushoutI.ofCoprodI (φ := iteratedMap G (⊥ : Subgroup G) ι))
        = MonoidHom.id _ := by
      refine CoprodI.ext_hom _ _ (fun i ↦ ?_)
      ext g
      show iteratedBotToCoprod G ι (PushoutI.ofCoprodI
          (CoprodI.of (M := IteratedFactor G ι) (i := i) g))
        = CoprodI.of (M := IteratedFactor G ι) (i := i) g
      rw [PushoutI.ofCoprodI_of]
      -- what `ofCoprodI_of` leaves is `PushoutI.of`, which is `inIterated`
      show iteratedBotToCoprod G ι (inIterated G (⊥ : Subgroup G) ι i g)
        = CoprodI.of (M := IteratedFactor G ι) (i := i) g
      rw [iteratedBotToCoprod_inIterated]
    exact DFunLike.congr_fun h y
  map_mul' := (iteratedBotToCoprod G ι).map_mul

/-! ## Transfer along the embedding -/

/-- Soficity of the amalgam descends to the two-vertex double. -/
theorem isSofic_symmetricDouble_of_isSofic_iterated (G : Type) [Group G]
    (Γ : Subgroup G) {ι : Type} {i j : ι} (hij : j ≠ i)
    (h : IsSofic (IteratedDouble G Γ ι)) : IsSofic (SymmetricDouble G Γ) :=
  isSofic_of_injective (doubleToIterated G Γ i j)
    (doubleToIterated_injective G Γ hij) h

/-- A nonsofic two-vertex double makes every amalgam with at least two vertices
nonsofic.  With `ι = ℤ` this is `LineDouble`'s conclusion; with `ι = K` it is
the one the free-lamp splitting consumes. -/
theorem not_isSofic_iterated_of_not_isSofic_symmetricDouble (G : Type)
    [Group G] (Γ : Subgroup G) {ι : Type} {i j : ι} (hij : j ≠ i)
    (h : ¬ IsSofic (SymmetricDouble G Γ)) : ¬ IsSofic (IteratedDouble G Γ ι) :=
  fun hiter ↦ h (isSofic_symmetricDouble_of_isSofic_iterated G Γ hij hiter)

end GroupApproximation
