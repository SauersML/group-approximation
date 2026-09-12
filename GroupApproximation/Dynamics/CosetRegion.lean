import GroupApproximation.Dynamics.Surjunctivity
import Mathlib.Data.Fintype.Pi
import Mathlib.GroupTheory.Coset.Basic

/-!
# Surjunctivity on finitely many subgroup tracks

The coordinates in a finite union of right subgroup cosets form a full shift
over that subgroup with a finite track alphabet. Include every boundary coset
read by the memory among these tracks. The remaining coordinates are the
exterior: they are fixed and do not influence the tracked output.

This module proves the boundary-label argument, constructs the required
coordinates from right-coset representatives, and establishes the coset-region
lemma with a uniformly finite-memory inverse.
-/

namespace GroupApproximation.Surjunctivity

universe u v w z

variable {K : Type u} [Group K]
variable {C : Type v} [Fintype C] [TopologicalSpace C] [DiscreteTopology C]
variable {E : Type w} [TopologicalSpace E]

/-- Freeze the exterior coordinates to obtain the automaton on subgroup tracks. -/
def trackMap (ρ : ((K → C) × E) → ((K → C) × E)) (e : E) :
    (K → C) → (K → C) := fun x => (ρ (x, e)).1

omit [Group K] [Fintype C] [DiscreteTopology C] in
theorem continuous_trackMap {ρ : ((K → C) × E) → ((K → C) × E)}
    (hρ : Continuous ρ) (e : E) : Continuous (trackMap ρ e) :=
  continuous_fst.comp (hρ.comp (continuous_id.prodMk continuous_const))

omit [Group K] [Fintype C] [TopologicalSpace C] [DiscreteTopology C]
  [TopologicalSpace E] in
/-- Injectivity of the whole map passes to the tracked map because the exterior
is fixed. In particular boundary tracks need not be updated. -/
theorem injective_trackMap {ρ : ((K → C) × E) → ((K → C) × E)}
    (hinj : Function.Injective ρ) (hfixed : ∀ x e, (ρ (x, e)).2 = e) (e : E) :
    Function.Injective (trackMap ρ e) := by
  intro x y h
  have heq : ρ (x, e) = ρ (y, e) := by
    apply Prod.ext
    · exact h
    · rw [hfixed, hfixed]
  exact congrArg Prod.fst (hinj heq)

/-- An injective continuous map on subgroup tracks and exterior coordinates is
surjective when the subgroup is surjunctive, the exterior is fixed, and the
tracked rule is equivariant and does not read exterior coordinates. -/
theorem surjective_of_finite_tracks
    (hK : IsSurjunctive K) (ρ : ((K → C) × E) → ((K → C) × E))
    (hcont : Continuous ρ) (hinj : Function.Injective ρ)
    (hfixed : ∀ x e, (ρ (x, e)).2 = e)
    (htracks : ∀ x e f, (ρ (x, e)).1 = (ρ (x, f)).1)
    (σ : K → E → E)
    (hequiv : ∀ k x e, (ρ (shift k x, σ k e)).1 = shift k (ρ (x, e)).1) :
    Function.Surjective ρ := by
  intro y
  have hCA : IsEquivariant (trackMap ρ y.2) := by
    intro k x
    exact (htracks (shift k x) y.2 (σ k y.2)).trans (hequiv k x y.2)
  have hsurj : Function.Surjective (trackMap ρ y.2) :=
    hK.surjective (trackMap ρ y.2) (continuous_trackMap hcont y.2) hCA
      (injective_trackMap hinj hfixed y.2)
  obtain ⟨x, hx⟩ := hsurj y.1
  refine ⟨(x, y.2), Prod.ext ?_ (hfixed x y.2)⟩
  exact hx

theorem bijective_of_finite_tracks
    (hK : IsSurjunctive K) (ρ : ((K → C) × E) → ((K → C) × E))
    (hcont : Continuous ρ) (hinj : Function.Injective ρ)
    (hfixed : ∀ x e, (ρ (x, e)).2 = e)
    (htracks : ∀ x e f, (ρ (x, e)).1 = (ρ (x, f)).1)
    (σ : K → E → E)
    (hequiv : ∀ k x e, (ρ (shift k x, σ k e)).1 = shift k (ρ (x, e)).1) :
    Function.Bijective ρ :=
  ⟨hinj, surjective_of_finite_tracks hK ρ hcont hinj hfixed htracks σ hequiv⟩

/-- Adding the memory boundary to the active region makes the output on the
enlarged region independent of all exterior coordinates. This is the locality
step used before identifying finitely many subgroup cosets with finite tracks. -/
theorem eqOn_region_of_memory
    {G : Type u} [Group G] {B : Type v}
    {ρ : (G → B) → (G → B)} {M : Finset G} {R T : Set G}
    (hmem : HasMemory ρ M)
    (hfixed : ∀ x g, g ∉ R → ρ x g = x g)
    (hboundary : ∀ g ∈ R, ∀ m ∈ M, g * m ∈ T)
    {x y : G → B} (hxy : Set.EqOn x y T) : Set.EqOn (ρ x) (ρ y) T := by
  intro g hg
  by_cases hgr : g ∈ R
  · apply hmem x y g
    intro m hm
    exact hxy (hboundary g hgr m hm)
  · rw [hfixed x g hgr, hfixed y g hgr]
    exact hxy hg

/-- An inverse retains every pointwise fixed exterior coordinate. -/
theorem inverse_fixes_exterior
    {G : Type u} {B : Type v} {ρ ψ : (G → B) → (G → B)} {R : Set G}
    (hρψ : Function.RightInverse ψ ρ)
    (hfixed : ∀ x g, g ∉ R → ρ x g = x g) :
    ∀ x g, g ∉ R → ψ x g = x g := by
  intro x g hg
  calc
    ψ x g = ρ (ψ x) g := (hfixed (ψ x) g hg).symm
    _ = x g := congrFun (hρψ x) g

section Coordinates

variable {G : Type u} {I : Type w} {B : Type v} {O : Type z} [TopologicalSpace B]

/-- Reindex configurations into subgroup tracks and the remaining coordinates. -/
def configurationCoordinates (e : (K × I) ⊕ O ≃ G) :
    (G → B) ≃ₜ ((K → I → B) × (O → B)) where
  toFun x := (fun k i => x (e (.inl (k, i))), fun o => x (e (.inr o)))
  invFun y g := Sum.elim (fun p => y.1 p.1 p.2) y.2 (e.symm g)
  left_inv x := by
    funext g
    have h := congrArg x (e.apply_symm_apply g)
    cases hg : e.symm g with
    | inl p => simpa only [hg, Sum.elim_inl] using h
    | inr o => simpa only [hg, Sum.elim_inr] using h
  right_inv y := by
    apply Prod.ext
    · funext k i
      simp only [Equiv.symm_apply_apply, Sum.elim_inl]
    · funext o
      simp only [Equiv.symm_apply_apply, Sum.elim_inr]
  continuous_toFun := by
    apply Continuous.prodMk
    · exact continuous_pi fun k => continuous_pi fun i => continuous_apply _
    · exact continuous_pi fun o => continuous_apply _
  continuous_invFun := by
    apply continuous_pi
    intro g
    cases hg : e.symm g with
    | inl p =>
      exact (continuous_apply p.2).comp ((continuous_apply p.1).comp continuous_fst)
    | inr o =>
      exact (continuous_apply o).comp continuous_snd

/-- The input configuration assembled from finite subgroup tracks and exterior. -/
def assembleCoordinates (e : (K × I) ⊕ O ≃ G)
    (x : K → I → B) (z : O → B) : G → B :=
  (configurationCoordinates e).symm (x, z)

omit [Group K] in
@[simp] theorem assembleCoordinates_track (e : (K × I) ⊕ O ≃ G)
    (x : K → I → B) (z : O → B) (k : K) (i : I) :
    assembleCoordinates e x z (e (.inl (k, i))) = x k i := by
  simp [assembleCoordinates, configurationCoordinates]

omit [Group K] in
@[simp] theorem assembleCoordinates_exterior (e : (K × I) ⊕ O ≃ G)
    (x : K → I → B) (z : O → B) (o : O) :
    assembleCoordinates e x z (e (.inr o)) = z o := by
  simp [assembleCoordinates, configurationCoordinates]

end Coordinates

/-- The coset-region argument with explicit finite coset coordinates. The index
equivalence lists the tracked cosets and their exterior, and its two transport
identities identify left subgroup translation in those coordinates. -/
theorem surjective_of_coset_coordinates
    {G : Type u} [Group G] {I : Type w} {B : Type v} {O : Type z}
    [Fintype I] [Fintype B]
    [TopologicalSpace B] [DiscreteTopology B]
    (hK : IsSurjunctive K) (κ : K →* G) (e : (K × I) ⊕ O ≃ G)
    (ζ : K → O → O)
    (hcoord : ∀ k a i, e (.inl (k * a, i)) = κ k * e (.inl (a, i)))
    (hexterior : ∀ k o, e (.inr (ζ k o)) = κ k * e (.inr o))
    (ρ : (G → B) → (G → B)) (hcont : Continuous ρ)
    (hinj : Function.Injective ρ) (M : Finset G) (hmem : HasMemory ρ M)
    (R : Set G)
    (hfixed : ∀ x g, g ∉ R → ρ x g = x g)
    (hcover : R ⊆ Set.range (fun p : K × I => e (.inl p)))
    (hboundary : ∀ g ∈ R, ∀ m ∈ M,
      g * m ∈ Set.range (fun p : K × I => e (.inl p)))
    (hequiv : ∀ k x g, ρ (fun h => x (κ k * h)) g = ρ x (κ k * g)) :
    Function.Surjective ρ := by
  classical
  let c := configurationCoordinates (B := B) e
  let τ := c ∘ ρ ∘ c.symm
  have hτcont : Continuous τ := c.continuous.comp (hcont.comp c.symm.continuous)
  have hτinj : Function.Injective τ := c.injective.comp (hinj.comp c.symm.injective)
  have hτfixed : ∀ x z, (τ (x, z)).2 = z := by
    intro x z
    funext o
    have hnot : e (.inr o) ∉ R := by
      intro ho
      obtain ⟨p, hp⟩ := hcover ho
      have hbad := e.injective hp
      cases hbad
    change ρ (assembleCoordinates e x z) (e (.inr o)) = z o
    rw [hfixed _ _ hnot, assembleCoordinates_exterior]
  have hτtracks : ∀ x z w, (τ (x, z)).1 = (τ (x, w)).1 := by
    intro x z w
    have hagree : Set.EqOn (assembleCoordinates e x z) (assembleCoordinates e x w)
        (Set.range (fun p : K × I => e (.inl p))) := by
      rintro g ⟨⟨a, i⟩, rfl⟩
      simp only [assembleCoordinates_track]
    have hout := eqOn_region_of_memory hmem hfixed hboundary hagree
    funext a i
    exact hout ⟨(a, i), rfl⟩
  let σ : K → (O → B) → (O → B) := fun k z o => z (ζ k o)
  have hτequiv : ∀ k x z, (τ (shift k x, σ k z)).1 = shift k (τ (x, z)).1 := by
    intro k x z
    have hshift : assembleCoordinates e (shift k x) (σ k z) =
        fun g => assembleCoordinates e x z (κ k * g) := by
      funext g
      obtain ⟨q, rfl⟩ := e.surjective g
      cases q with
      | inl p =>
        rcases p with ⟨a, i⟩
        rw [← hcoord k a i]
        simp only [assembleCoordinates_track, shift_apply]
      | inr o =>
        rw [← hexterior k o]
        simp only [assembleCoordinates_exterior, σ]
    funext a i
    change ρ (assembleCoordinates e (shift k x) (σ k z)) (e (.inl (a, i))) =
      ρ (assembleCoordinates e x z) (e (.inl (k * a, i)))
    rw [hshift, hequiv, hcoord]
  have hτsurj := surjective_of_finite_tracks hK τ hτcont hτinj hτfixed
    hτtracks σ hτequiv
  intro y
  obtain ⟨x, hx⟩ := hτsurj (c y)
  exact ⟨c.symm x, c.injective hx⟩

section RightCosets

variable {G : Type u} [Group G]

/-- The right cosets, on which multiplication by the subgroup on the left is
invisible. -/
abbrev RightCosets (H : Subgroup G) := Quotient (QuotientGroup.rightRel H)

def rightCosetMk (H : Subgroup G) (g : G) : RightCosets H := Quotient.mk'' g

@[simp] theorem rightCosetMk_mul (H : Subgroup G) (k : H) (g : G) :
    rightCosetMk H ((k : G) * g) = rightCosetMk H g := by
  symm
  apply Quotient.sound
  change QuotientGroup.rightRel H g ((k : G) * g)
  rw [QuotientGroup.rightRel_apply]
  simpa only [mul_inv_cancel_right] using k.property

@[simp] theorem rightCosetMk_out (H : Subgroup G) (q : RightCosets H) :
    rightCosetMk H q.out = q := Quotient.out_eq q

/-- Choose one representative of each right coset. Left multiplication on the
subgroup factor is the actual left action on the group. -/
noncomputable def rightCosetCoordinates (H : Subgroup G) : H × RightCosets H ≃ G :=
  Equiv.ofBijective (fun p => (p.1 : G) * p.2.out) (by
    constructor
    · rintro ⟨k, q⟩ ⟨l, r⟩ h
      have hq : q = r := by
        have hquot := congrArg (rightCosetMk H) h
        simpa only [rightCosetMk_mul, rightCosetMk_out] using hquot
      subst r
      have hk : k = l := Subtype.ext (mul_right_cancel h)
      subst l
      rfl
    · intro g
      let q := rightCosetMk H g
      have hmem : g * q.out⁻¹ ∈ H :=
        QuotientGroup.rightRel_apply.mp (Quotient.mk_out g)
      refine ⟨(⟨g * q.out⁻¹, hmem⟩, q), ?_⟩
      exact inv_mul_cancel_right g q.out)

@[simp] theorem rightCosetCoordinates_apply (H : Subgroup G)
    (k : H) (q : RightCosets H) :
    rightCosetCoordinates H (k, q) = (k : G) * q.out := rfl

/-- Split the quotient index into a chosen finite set and its complement. -/
noncomputable def splitRightCosetIndex (H : Subgroup G) (S : Finset (RightCosets H)) :
    (H × S) ⊕ (H × {q : RightCosets H // q ∉ S}) ≃ H × RightCosets H := by
  classical
  exact
    { toFun := Sum.elim (fun p => (p.1, p.2.1)) (fun p => (p.1, p.2.1))
      invFun p := if h : p.2 ∈ S then .inl (p.1, ⟨p.2, h⟩) else .inr (p.1, ⟨p.2, h⟩)
      left_inv p := by
        cases p with
        | inl p => simp only [Sum.elim_inl, dif_pos p.2.property]
        | inr p => simp only [Sum.elim_inr, dif_neg p.2.property]
      right_inv p := by
        dsimp
        split <;> rfl }

/-- Finite right cosets as finitely many subgroup tracks, with all
other right cosets retained as exterior coordinates. -/
noncomputable def finiteRightCosetCoordinates (H : Subgroup G)
    (S : Finset (RightCosets H)) :
    (H × S) ⊕ (H × {q : RightCosets H // q ∉ S}) ≃ G :=
  (splitRightCosetIndex H S).trans (rightCosetCoordinates H)

@[simp] theorem finiteRightCosetCoordinates_inl (H : Subgroup G)
    (S : Finset (RightCosets H)) (k : H) (q : S) :
    finiteRightCosetCoordinates H S (.inl (k, q)) = (k : G) * q.1.out := rfl

@[simp] theorem finiteRightCosetCoordinates_inr (H : Subgroup G)
    (S : Finset (RightCosets H)) (p : H × {q : RightCosets H // q ∉ S}) :
    finiteRightCosetCoordinates H S (.inr p) = (p.1 : G) * p.2.1.out := rfl

theorem mem_finiteRightCosetCoordinates_range (H : Subgroup G)
    (S : Finset (RightCosets H)) (g : G) :
    g ∈ Set.range (fun p : H × S => finiteRightCosetCoordinates H S (.inl p)) ↔
      rightCosetMk H g ∈ S := by
  constructor
  · rintro ⟨⟨k, q⟩, rfl⟩
    simpa only [finiteRightCosetCoordinates_inl, rightCosetMk_mul, rightCosetMk_out]
      using q.property
  · intro hg
    let q := rightCosetMk H g
    have hmem : g * q.out⁻¹ ∈ H :=
      QuotientGroup.rightRel_apply.mp (Quotient.mk_out g)
    refine ⟨(⟨g * q.out⁻¹, hmem⟩, ⟨q, hg⟩), ?_⟩
    exact inv_mul_cancel_right g q.out

theorem rightCosetMk_eq_of_mem (H : Subgroup G) {g r : G}
    (h : g * r⁻¹ ∈ H) : rightCosetMk H g = rightCosetMk H r := by
  symm
  apply Quotient.sound
  exact QuotientGroup.rightRel_apply.mpr h

/-- The coset-region surjectivity lemma. The active set only needs to be covered
by finitely many right cosets of the surjunctive subgroup. -/
theorem surjective_of_finite_coset_support
    {B : Type v} [Fintype B] [TopologicalSpace B] [DiscreteTopology B]
    (H : Subgroup G) (hH : IsSurjunctive H)
    (ρ : (G → B) → (G → B)) (hcont : Continuous ρ)
    (hinj : Function.Injective ρ) (hmem : IsFiniteMemory ρ)
    (R : Set G) (S : Finset G)
    (hcover : ∀ g ∈ R, ∃ r ∈ S, g * r⁻¹ ∈ H)
    (hfixed : ∀ x g, g ∉ R → ρ x g = x g)
    (hequiv : ∀ k : H, ∀ x g,
      ρ (fun h => x ((k : G) * h)) g = ρ x ((k : G) * g)) :
    Function.Surjective ρ := by
  classical
  obtain ⟨M, hM⟩ := hmem
  let F : Finset (RightCosets H) :=
    S.biUnion fun r => (insert 1 M).image fun m => rightCosetMk H (r * m)
  have hF : ∀ r ∈ S, ∀ m ∈ insert 1 M, rightCosetMk H (r * m) ∈ F := by
    intro r hr m hm
    exact Finset.mem_biUnion.mpr ⟨r, hr, Finset.mem_image.mpr ⟨m, hm, rfl⟩⟩
  let e := finiteRightCosetCoordinates H F
  let ζ : H → (H × {q : RightCosets H // q ∉ F}) →
      (H × {q : RightCosets H // q ∉ F}) := fun k p => (k * p.1, p.2)
  apply surjective_of_coset_coordinates hH H.subtype e ζ
    (fun k a i => ?_) (fun k o => ?_) ρ hcont hinj M hM R hfixed
    (fun g hg => ?_) (fun g hg m hm => ?_) hequiv
  · simp only [e, finiteRightCosetCoordinates_inl, Subgroup.coe_mul, mul_assoc]
    rfl
  · simp only [e, ζ, finiteRightCosetCoordinates_inr, Subgroup.coe_mul, mul_assoc]
    rfl
  · apply (mem_finiteRightCosetCoordinates_range H F g).mpr
    obtain ⟨r, hr, hgr⟩ := hcover g hg
    rw [rightCosetMk_eq_of_mem H hgr]
    simpa only [mul_one] using hF r hr 1 (Finset.mem_insert_self 1 M)
  · apply (mem_finiteRightCosetCoordinates_range H F (g * m)).mpr
    obtain ⟨r, hr, hgr⟩ := hcover g hg
    have hgrm : g * m * (r * m)⁻¹ ∈ H := by
      simpa only [mul_inv_rev, mul_assoc, mul_inv_cancel_left] using hgr
    rw [rightCosetMk_eq_of_mem H hgrm]
    exact hF r hr m (Finset.mem_insert_of_mem hm)

/-- An injective finite-memory map supported in finitely many subgroup cosets
is bijective, with a finite-memory inverse preserving subgroup symmetry and
fixing the original exterior pointwise. -/
theorem coset_region
    {B : Type v} [Fintype B] [TopologicalSpace B] [DiscreteTopology B]
    (H : Subgroup G) (hH : IsSurjunctive H)
    (ρ : (G → B) → (G → B)) (hinj : Function.Injective ρ)
    (hmem : IsFiniteMemory ρ) (R : Set G) (S : Finset G)
    (hcover : ∀ g ∈ R, ∃ r ∈ S, g * r⁻¹ ∈ H)
    (hfixed : ∀ x g, g ∉ R → ρ x g = x g)
    (hequiv : ∀ k : H, ∀ x g,
      ρ (shift (k : G) x) g = ρ x ((k : G) * g)) :
    Function.Bijective ρ ∧ ∃ ψ : (G → B) → (G → B),
      IsFiniteMemory ψ ∧ Function.LeftInverse ψ ρ ∧ Function.RightInverse ψ ρ ∧
      (∀ x g, g ∉ R → ψ x g = x g) ∧
      (∀ k : H, ∀ x g, ψ (shift (k : G) x) g = ψ x ((k : G) * g)) := by
  classical
  have hc := hmem.continuous
  have hb : Function.Bijective ρ :=
    ⟨hinj, surjective_of_finite_coset_support H hH ρ hc hinj hmem R S hcover hfixed
      hequiv⟩
  let e := Equiv.ofBijective ρ hb
  have hψcont : Continuous e.symm := continuous_equiv_symm e hc
  have hψfixed : ∀ x g, g ∉ R → e.symm x g = x g :=
    inverse_fixes_exterior e.apply_symm_apply hfixed
  have hψequiv : ∀ k : H, ∀ x g,
      e.symm (shift (k : G) x) g = e.symm x ((k : G) * g) := by
    intro k x g
    have hf : e.symm (shift (k : G) x) = shift (k : G) (e.symm x) := by
      apply e.injective
      funext a
      change ρ (e.symm (shift (k : G) x)) a = ρ (shift (k : G) (e.symm x)) a
      rw [hequiv]
      change e (e.symm (shift (k : G) x)) a = e (e.symm x) ((k : G) * a)
      rw [e.apply_symm_apply, e.apply_symm_apply]
      rfl
    exact congrFun hf g
  have hψmem : IsFiniteMemory e.symm :=
    isFiniteMemory_of_continuous_coset_support H S hψcont hψequiv (by
      intro x g hg
      apply hψfixed x g
      intro hgr
      obtain ⟨r, hr, hmemr⟩ := hcover g hgr
      exact hg r hr hmemr)
  exact ⟨hb, e.symm, hψmem, e.symm_apply_apply, e.apply_symm_apply, hψfixed, hψequiv⟩

end RightCosets

end GroupApproximation.Surjunctivity
