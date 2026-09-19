import GroupApproximation.Sofic.CliffordLampGroup

/-!
# The Clifford lamp group of a graph

For a set `S` of sites and a symmetric adjacency relation `Adj` on it, the
Clifford group of the graph is presented by an involution `lamp s` for every
site, one further involution `sign`, the centrality of `sign`, and the
braiding relation

    ⁅lamp s, lamp s'⁆ = sign        for distinct *adjacent* sites,

with no relation at all between non-adjacent lamps.  This is the group
`C(𝒢)` displayed at (3.3) of
`notes/LITERAL_GROUP_BLOCK_AMALGAM_STRUCTURE_2026-08-14.md`, and it is the
lamp kernel of the literal forty-one-relator group.

Two design points are load-bearing and deliberate.

*The relation, not a fibring.*  `BlockCliffordLamp.BlockClifford` braids two
sites when they lie over a common block, on a finite sigma-indexed site set.
That presentation is a *quotient* of this one, because adjacency implies
lying in a common connected component but not conversely; the converse for
the literal group is Proposition 4.2 of the artifact above, whose proof rests
on the identification of the literal base with `ℤ³ ⋊ SL₃(ℤ)` — a literature
premise this repository does not own.  Braiding on `Adj` therefore keeps the
group on the unconditional side, and every result below is free of
finiteness, decidability and ordering hypotheses.

*A universal property.*  `lift` maps the presented group into an arbitrary
group from the four relations alone.  This is what allows an inverse
homomorphism to be exhibited downstream; a Clifford-algebra model would give
a group with no map out of it.

Nontriviality of the sign is proved through `toFull`, the collapse onto the
complete Clifford lamp group of `con:clifford` obtained by imposing all the
missing braiding relations, where `CliffordLamp.sign_ne_one` applies.  No
normal form and no faithfulness statement for this presentation is claimed
anywhere.
-/

namespace GroupApproximation
namespace GraphCliffordLamp

open scoped commutatorElement

universe u v w

/-- Free generators: `Sum.inl ()` is the central sign, `Sum.inr s` the lamp
at the site `s`. -/
abbrev Gen (S : Type u) := Unit ⊕ S

variable {S : Type u}

/-! ## The presentation -/

/-- The four relator families: the sign and the lamps are involutions, the
sign is central, and two *distinct adjacent* lamps anticommute through the
sign.  Non-adjacent lamps satisfy no relation. -/
inductive IsRelator (Adj : S → S → Prop) : FreeGroup (Gen S) → Prop
  | sign_sq : IsRelator Adj (FreeGroup.of (Sum.inl ()) ^ 2)
  | lamp_sq (s : S) : IsRelator Adj (FreeGroup.of (Sum.inr s) ^ 2)
  | sign_comm (s : S) :
      IsRelator Adj ⁅(FreeGroup.of (Sum.inl ()) : FreeGroup (Gen S)),
        FreeGroup.of (Sum.inr s)⁆
  | braiding {s s' : S} (hne : s ≠ s') (hadj : Adj s s') :
      IsRelator Adj
        (⁅(FreeGroup.of (Sum.inr s) : FreeGroup (Gen S)),
            FreeGroup.of (Sum.inr s')⁆ *
          (FreeGroup.of (Sum.inl ()))⁻¹)

/-- The graph Clifford relators as a set. -/
def relators (Adj : S → S → Prop) : Set (FreeGroup (Gen S)) :=
  {w | IsRelator Adj w}

/-- The Clifford lamp group of the graph `(S, Adj)`. -/
abbrev GraphClifford (Adj : S → S → Prop) := PresentedGroup (relators Adj)

/-- The central sign. -/
def sign (Adj : S → S → Prop) : GraphClifford Adj :=
  PresentedGroup.of (Sum.inl ())

/-- The lamp at a site. -/
def lamp (Adj : S → S → Prop) (s : S) : GraphClifford Adj :=
  PresentedGroup.of (Sum.inr s)

theorem sign_sq (Adj : S → S → Prop) : sign Adj ^ 2 = 1 := by
  have h := PresentedGroup.one_of_mem (IsRelator.sign_sq (Adj := Adj))
  rwa [map_pow] at h

theorem lamp_sq (Adj : S → S → Prop) (s : S) : lamp Adj s ^ 2 = 1 := by
  have h := PresentedGroup.one_of_mem (IsRelator.lamp_sq (Adj := Adj) s)
  rwa [map_pow] at h

theorem sign_commute_lamp (Adj : S → S → Prop) (s : S) :
    Commute (sign Adj) (lamp Adj s) := by
  have h := PresentedGroup.one_of_mem (IsRelator.sign_comm (Adj := Adj) s)
  rw [map_commutatorElement] at h
  exact commutatorElement_eq_one_iff_commute.mp h

/-- The braiding relation: two distinct adjacent lamps commute exactly up to
the sign. -/
theorem commutator_lamp_lamp (Adj : S → S → Prop) {s s' : S} (hne : s ≠ s')
    (hadj : Adj s s') : ⁅lamp Adj s, lamp Adj s'⁆ = sign Adj := by
  have h1 := PresentedGroup.one_of_mem
    (IsRelator.braiding (Adj := Adj) hne hadj)
  rw [map_mul, map_inv, map_commutatorElement] at h1
  have h2 : ⁅lamp Adj s, lamp Adj s'⁆ * (sign Adj)⁻¹ = 1 := h1
  calc ⁅lamp Adj s, lamp Adj s'⁆
      = ⁅lamp Adj s, lamp Adj s'⁆ * (sign Adj)⁻¹ * sign Adj := by group
    _ = 1 * sign Adj := by rw [h2]
    _ = sign Adj := one_mul _

/-- The sign is central. -/
theorem sign_commute (Adj : S → S → Prop) (g : GraphClifford Adj) :
    Commute (sign Adj) g := by
  have hmem : g ∈ Subgroup.centralizer {sign Adj} := by
    apply PresentedGroup.generated_by (relators Adj)
      (Subgroup.centralizer {sign Adj}) (fun j => ?_) g
    rw [Subgroup.mem_centralizer_singleton_iff]
    match j with
    | Sum.inl () => rfl
    | Sum.inr s => exact (sign_commute_lamp Adj s).eq.symm
  rw [Subgroup.mem_centralizer_singleton_iff] at hmem
  exact Commute.symm hmem

theorem sign_mem_center (Adj : S → S → Prop) :
    sign Adj ∈ Subgroup.center (GraphClifford Adj) :=
  Subgroup.mem_center_iff.mpr fun g => ((sign_commute Adj g).symm).eq

/-- The sign together with all the lamps generates the group. -/
theorem mem_subgroup_of_sign_mem_of_lamp_mem (Adj : S → S → Prop)
    (H : Subgroup (GraphClifford Adj)) (hsign : sign Adj ∈ H)
    (hlamp : ∀ s, lamp Adj s ∈ H) (g : GraphClifford Adj) : g ∈ H := by
  apply PresentedGroup.generated_by (relators Adj) H
  intro j
  cases j with
  | inl u => cases u; exact hsign
  | inr s => exact hlamp s

/-! ## The universal property -/

section Lift

variable {G : Type v} [Group G]

theorem lift_kills (Adj : S → S → Prop) (f : S → G) (z : G) (hz : z ^ 2 = 1)
    (hf : ∀ s, f s ^ 2 = 1) (hzc : ∀ s, Commute z (f s))
    (hbraid : ∀ s s', s ≠ s' → Adj s s' → ⁅f s, f s'⁆ = z) :
    ∀ w ∈ relators Adj,
      FreeGroup.lift (Sum.elim (fun _ => z) f) w = 1 := by
  intro w hw
  change IsRelator Adj w at hw
  cases hw with
  | sign_sq =>
      rw [map_pow, FreeGroup.lift_apply_of]
      exact hz
  | lamp_sq s =>
      rw [map_pow, FreeGroup.lift_apply_of]
      exact hf s
  | sign_comm s =>
      rw [map_commutatorElement, FreeGroup.lift_apply_of,
        FreeGroup.lift_apply_of]
      exact (hzc s).commutator_eq
  | @braiding s s' hne hadj =>
      rw [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of,
        FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
      show ⁅f s, f s'⁆ * z⁻¹ = 1
      rw [hbraid s s' hne hadj]
      exact mul_inv_cancel _

/-- **Universal property of the graph Clifford lamp group.**  A family of
involutions indexed by the sites, together with a central involution that
their adjacent commutators realize, determines a homomorphism.  This is what
lets an inverse be exhibited on generators. -/
def lift (Adj : S → S → Prop) (f : S → G) (z : G) (hz : z ^ 2 = 1)
    (hf : ∀ s, f s ^ 2 = 1) (hzc : ∀ s, Commute z (f s))
    (hbraid : ∀ s s', s ≠ s' → Adj s s' → ⁅f s, f s'⁆ = z) :
    GraphClifford Adj →* G :=
  PresentedGroup.toGroup (lift_kills Adj f z hz hf hzc hbraid)

@[simp] theorem lift_sign (Adj : S → S → Prop) (f : S → G) (z : G)
    (hz : z ^ 2 = 1) (hf : ∀ s, f s ^ 2 = 1) (hzc : ∀ s, Commute z (f s))
    (hbraid : ∀ s s', s ≠ s' → Adj s s' → ⁅f s, f s'⁆ = z) :
    lift Adj f z hz hf hzc hbraid (sign Adj) = z :=
  PresentedGroup.toGroup.of _

@[simp] theorem lift_lamp (Adj : S → S → Prop) (f : S → G) (z : G)
    (hz : z ^ 2 = 1) (hf : ∀ s, f s ^ 2 = 1) (hzc : ∀ s, Commute z (f s))
    (hbraid : ∀ s s', s ≠ s' → Adj s s' → ⁅f s, f s'⁆ = z) (s : S) :
    lift Adj f z hz hf hzc hbraid (lamp Adj s) = f s :=
  PresentedGroup.toGroup.of _

end Lift

/-! ## The complete Clifford lamp group as a detector -/

/-- The collapse onto the complete Clifford lamp group on all sites: impose
every missing braiding relation. -/
def toFull (Adj : S → S → Prop) :
    GraphClifford Adj →* CliffordLamp.CliffordLamp S :=
  lift Adj (fun s => CliffordLamp.lamp S s) (CliffordLamp.sign S)
    (CliffordLamp.sign_sq S) (fun s => CliffordLamp.lamp_sq S s)
    (fun s => CliffordLamp.sign_commute_lamp S s)
    (fun _ _ hne _ => CliffordLamp.commutator_lamp_lamp S hne)

@[simp] theorem toFull_sign (Adj : S → S → Prop) :
    toFull Adj (sign Adj) = CliffordLamp.sign S :=
  lift_sign _ _ _ _ _ _ _

@[simp] theorem toFull_lamp (Adj : S → S → Prop) (s : S) :
    toFull Adj (lamp Adj s) = CliffordLamp.lamp S s :=
  lift_lamp _ _ _ _ _ _ _ s

/-- **The sign survives.**  Collapsing the graph onto the complete graph
carries it to the central sign of the Clifford lamp group of
`con:clifford`, which the crossing-form model separates from `1`. -/
theorem sign_ne_one (Adj : S → S → Prop) : sign Adj ≠ 1 := by
  intro h
  have h1 : CliffordLamp.sign S = 1 := by
    rw [← toFull_sign Adj, h, map_one]
  exact CliffordLamp.sign_ne_one S h1

/-! ## Actions by adjacency-preserving site permutations -/

/-- A group acting on the sites *preserves adjacency* if it carries adjacent
pairs to adjacent pairs.  Nothing about blocks or components is asked for. -/
abbrev PreservesAdj (Adj : S → S → Prop) (V : Type w) [Group V]
    [MulAction V S] : Prop :=
  ∀ (v : V) (s s' : S), Adj s s' → Adj (v • s) (v • s')

section Action

variable {V : Type w} [Group V] [MulAction V S]

/-- Translating the sites by a group element is injective, so it preserves
distinctness of a braiding pair. -/
theorem smul_ne_smul {v : V} {s s' : S} (hne : s ≠ s') : v • s ≠ v • s' := by
  intro hc
  apply hne
  have hcancel := congrArg (fun x : S => v⁻¹ • x) hc
  simpa only [inv_smul_smul] using hcancel

/-- The endomorphism induced by a site translation. -/
def smulMap (Adj : S → S → Prop) (hV : PreservesAdj Adj V) (v : V) :
    GraphClifford Adj →* GraphClifford Adj :=
  lift Adj (fun s => lamp Adj (v • s)) (sign Adj) (sign_sq Adj)
    (fun s => lamp_sq Adj (v • s)) (fun s => sign_commute_lamp Adj (v • s))
    (fun s s' hne hadj =>
      commutator_lamp_lamp Adj (smul_ne_smul hne) (hV v s s' hadj))

@[simp] theorem smulMap_sign (Adj : S → S → Prop)
    (hV : PreservesAdj Adj V) (v : V) :
    smulMap Adj hV v (sign Adj) = sign Adj :=
  lift_sign _ _ _ _ _ _ _

@[simp] theorem smulMap_lamp (Adj : S → S → Prop) (hV : PreservesAdj Adj V)
    (v : V) (s : S) : smulMap Adj hV v (lamp Adj s) = lamp Adj (v • s) :=
  lift_lamp _ _ _ _ _ _ _ s

theorem smulMap_comp (Adj : S → S → Prop) (hV : PreservesAdj Adj V)
    (v₁ v₂ : V) (g : GraphClifford Adj) :
    smulMap Adj hV v₁ (smulMap Adj hV v₂ g) =
      smulMap Adj hV (v₁ * v₂) g := by
  have h : (smulMap Adj hV v₁).comp (smulMap Adj hV v₂) =
      smulMap Adj hV (v₁ * v₂) := by
    apply PresentedGroup.ext
    intro j
    match j with
    | Sum.inl () =>
        show smulMap Adj hV v₁ (smulMap Adj hV v₂ (sign Adj)) =
          smulMap Adj hV (v₁ * v₂) (sign Adj)
        rw [smulMap_sign, smulMap_sign, smulMap_sign]
    | Sum.inr s =>
        show smulMap Adj hV v₁ (smulMap Adj hV v₂ (lamp Adj s)) =
          smulMap Adj hV (v₁ * v₂) (lamp Adj s)
        rw [smulMap_lamp, smulMap_lamp, smulMap_lamp, mul_smul]
  exact DFunLike.congr_fun h g

theorem smulMap_one_apply (Adj : S → S → Prop) (hV : PreservesAdj Adj V)
    (g : GraphClifford Adj) : smulMap Adj hV (1 : V) g = g := by
  have h : smulMap Adj hV (1 : V) = MonoidHom.id (GraphClifford Adj) := by
    apply PresentedGroup.ext
    intro j
    match j with
    | Sum.inl () =>
        show smulMap Adj hV (1 : V) (sign Adj) = sign Adj
        rw [smulMap_sign]
    | Sum.inr s =>
        show smulMap Adj hV (1 : V) (lamp Adj s) = lamp Adj s
        rw [smulMap_lamp, one_smul]
  rw [h]
  rfl

/-- The automorphism induced by a site translation. -/
def smulAut (Adj : S → S → Prop) (hV : PreservesAdj Adj V) (v : V) :
    MulAut (GraphClifford Adj) :=
  MonoidHom.toMulEquiv (smulMap Adj hV v) (smulMap Adj hV v⁻¹)
    (by
      apply PresentedGroup.ext
      intro j
      match j with
      | Sum.inl () =>
          show smulMap Adj hV v⁻¹ (smulMap Adj hV v (sign Adj)) = sign Adj
          rw [smulMap_sign, smulMap_sign]
      | Sum.inr s =>
          show smulMap Adj hV v⁻¹ (smulMap Adj hV v (lamp Adj s)) =
            lamp Adj s
          rw [smulMap_lamp, smulMap_lamp, inv_smul_smul])
    (by
      apply PresentedGroup.ext
      intro j
      match j with
      | Sum.inl () =>
          show smulMap Adj hV v (smulMap Adj hV v⁻¹ (sign Adj)) = sign Adj
          rw [smulMap_sign, smulMap_sign]
      | Sum.inr s =>
          show smulMap Adj hV v (smulMap Adj hV v⁻¹ (lamp Adj s)) =
            lamp Adj s
          rw [smulMap_lamp, smulMap_lamp, smul_inv_smul])

@[simp] theorem smulAut_apply (Adj : S → S → Prop) (hV : PreservesAdj Adj V)
    (v : V) (g : GraphClifford Adj) :
    smulAut Adj hV v g = smulMap Adj hV v g := rfl

/-- **An adjacency-preserving action on the sites acts on the lamp group.**
The sign is fixed and the lamps are permuted along the site action. -/
def smulHom (Adj : S → S → Prop) (hV : PreservesAdj Adj V) :
    V →* MulAut (GraphClifford Adj) where
  toFun := smulAut Adj hV
  map_one' := by
    apply MulEquiv.ext
    intro g
    rw [smulAut_apply, smulMap_one_apply]
    rfl
  map_mul' v₁ v₂ := by
    apply MulEquiv.ext
    intro g
    rw [smulAut_apply]
    show smulMap Adj hV (v₁ * v₂) g =
      (smulAut Adj hV v₁ * smulAut Adj hV v₂) g
    rw [MulAut.mul_apply, smulAut_apply, smulAut_apply, smulMap_comp]

@[simp] theorem smulHom_apply_sign (Adj : S → S → Prop)
    (hV : PreservesAdj Adj V) (v : V) :
    smulHom Adj hV v (sign Adj) = sign Adj := by
  show smulAut Adj hV v (sign Adj) = sign Adj
  rw [smulAut_apply, smulMap_sign]

@[simp] theorem smulHom_apply_lamp (Adj : S → S → Prop)
    (hV : PreservesAdj Adj V) (v : V) (s : S) :
    smulHom Adj hV v (lamp Adj s) = lamp Adj (v • s) := by
  show smulAut Adj hV v (lamp Adj s) = lamp Adj (v • s)
  rw [smulAut_apply, smulMap_lamp]

end Action

/-! ## Countability -/

instance [Countable S] (Adj : S → S → Prop) :
    Countable (GraphClifford Adj) :=
  (PresentedGroup.mk_surjective (relators Adj)).countable

end GraphCliffordLamp
end GroupApproximation
