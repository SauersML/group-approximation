import GroupApproximation.Algebra.AbelianLampTelescopeKernel
import GroupApproximation.Algebra.WreathTelescopeTower

/-!
# The limit kernel of a coset telescope is the union of its stage kernels

**Section 37.5, equation (37.17), of the multi-mover dossier**, on the site
layer.

The two arithmetic engines that compute a limit kernel already exist in the
repository: `AbLamp.ker_push_eq_iSup` for the `Finsupp` lamp model `X →₀ A`,
and `WreathTelescope.mem_ker_pushHom_limit` for the general lamp model
`Lamp K X`.  Both are stated for an abstract tower of maps of site *sets*, and
both take their whole input as hypotheses about those maps.  What was missing is
the instantiation at the site sets the telescope actually uses, and that is what
this file supplies.

## The setting

`lev : ℕ → Subgroup G` increases, and `N` is the subgroup it exhausts:

```text
g ∈ N  ↔  ∃ n, g ∈ lev n .
```

The sites are the coset spaces `X n = G ⧸ lev n`, the limit site set is
`X∞ = G ⧸ N`, and the maps `X 0 → X n → X∞` are the canonical projections
`Subgroup.quotientMapOfLE`.  A lamp configuration is a finitely supported
labelling of `X 0`, and the pushforward along a map of site sets multiplies the
labels within each fibre.

Nothing here asks any of the subgroups to be normal.  `G ⧸ H` is used only as a
set of cosets; the single fact ever needed about it is `QuotientGroup.eq`, that
two elements have the same image exactly when `a⁻¹ * b ∈ H`.

## Two separation lemmas, and why both are needed

`LevelChain.exists_stage_of_projLimit_eq` is the *pointwise* statement: if two
sites are merged in the limit then they are merged at some finite stage.  It is
immediate from exhaustion — `a⁻¹ * b ∈ N` puts `a⁻¹ * b` in a single `lev n` —
and it is all the `Lamp K X` engine needs, because there the stage kernel is
*generated* by same-fibre differences, so one generator at a time suffices.

`LevelChain.exists_stage_separating` is the *uniform* statement: given a finite
set of sites, a single stage `n` already cuts it into the limit fibres.  This is
strictly stronger, and it is what the `Finsupp` engine needs, because there the
kernel is described by the *values* of the pushforward, and a value at a target
site is a sum over a whole fibre — so the stage must get every coincidence
inside the support right at once.  Finiteness of the support is exactly what
buys the single stage: the finitely many ratios `a⁻¹ * b` that lie in `N` lie in
finitely many levels, and the chain is increasing, so their maximum works.

The honest reusable kernel of 37.5 is therefore the purely combinatorial

```text
exists_level_separating :
  ∃ n, ∀ a ∈ T, ∀ b ∈ T, (a⁻¹ * b ∈ N ↔ a⁻¹ * b ∈ lev n)
```

for a finite `T : Finset G`, together with its fibre form
`exists_level_fibres_agree`: at that `n`, two elements of `T` have the same
image in `G ⧸ lev n` exactly when they have the same image in `G ⧸ N`.

## Relation to `exists_common_level`

`LiteralTelescopeCoreLEF.exists_common_level` proves the same maximum-of-levels
step under the hypothesis that the chain exhausts *all* of `G`.  That is not the
situation here: `lev` exhausts `N`, which is in general a proper subgroup, and
the elements to be covered are exactly the ratios that happen to lie in `N`.
`exists_common_level_of_forall_mem` below is that relative form; it takes the
per-element exhaustion as a hypothesis on the finite set, and its proof is the
same three-line supremum argument.  This file therefore does not import the
literal-telescope module.

## What is not proved here

* Nothing analytic, and nothing about soficity or the MF radical.  This file is
  the combinatorial input that `TelescopeRadicalInduction.ker_limit_le_coronaMFResidual`
  consumes as its `hunion` hypothesis; that module is outside the root import
  closure and is deliberately not imported.
* No claim that any stage kernel, or the limit kernel, is proper, nontrivial, or
  contained in any radical.  The tower here may well be constant.
* No normality, no finite generation, and no bound on the stage `n`, which
  depends on the finite set of sites arbitrarily.
-/

namespace GroupApproximation
namespace TelescopeLimitKernel

universe u v

/-! ## A finite set inside a relatively exhausting chain -/

section Core

variable {G : Type u} [Group G]

/-- **The relative common-level step.**  A finite set each of whose elements
lies in *some* member of an increasing chain lies in a single member: take the
maximum of the levels of its elements.

This is `LiteralTelescopeCoreLEF.exists_common_level` with the global
exhaustion hypothesis `∀ g : G, ∃ n, g ∈ lev n` weakened to the per-element one,
which is the form available when the chain exhausts a proper subgroup. -/
theorem exists_common_level_of_forall_mem (lev : ℕ → Subgroup G)
    (hmono : Monotone lev) (s : Finset G) (hs : ∀ g ∈ s, ∃ n, g ∈ lev n) :
    ∃ n : ℕ, ∀ g ∈ s, g ∈ lev n :=
  ⟨s.attach.sup fun g => (hs g.1 g.2).choose, fun g hg =>
    hmono (Finset.le_sup (f := fun g : {x // x ∈ s} => (hs g.1 g.2).choose)
      (Finset.mem_attach s ⟨g, hg⟩)) (hs g hg).choose_spec⟩

/-- **The combinatorial kernel of 37.5.**  For a finite set `T` of group
elements there is a single level at which the chain already sees every
coincidence that the limit subgroup sees inside `T`.

Only finitely many ratios `a⁻¹ * b` with `a, b ∈ T` lie in `N`, each of them
lies in some level, and the chain increases, so one level covers them all.  The
converse inclusion is free: every level is contained in `N`. -/
theorem exists_level_separating (lev : ℕ → Subgroup G) (N : Subgroup G)
    (hmono : Monotone lev) (hexh : ∀ g : G, g ∈ N ↔ ∃ n, g ∈ lev n)
    (T : Finset G) :
    ∃ n : ℕ, ∀ a ∈ T, ∀ b ∈ T, (a⁻¹ * b ∈ N ↔ a⁻¹ * b ∈ lev n) := by
  classical
  obtain ⟨n, hn⟩ := exists_common_level_of_forall_mem lev hmono
    (((T ×ˢ T).image fun p => p.1⁻¹ * p.2).filter fun g => g ∈ N)
    fun g hg => (hexh g).mp (Finset.mem_filter.mp hg).2
  refine ⟨n, fun a ha b hb => ⟨fun h => hn _ ?_, fun h => (hexh _).mpr ⟨n, h⟩⟩⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩, h⟩

/-- **The fibre form.**  At the level supplied by `exists_level_separating`, the
partition of `T` into `G ⧸ lev n`-fibres already equals its partition into
`G ⧸ N`-fibres.  This is the statement the pushforward argument consumes: the
stage-`n` fibres cut a finite set of sites exactly as the limit fibres do. -/
theorem exists_level_fibres_agree (lev : ℕ → Subgroup G) (N : Subgroup G)
    (hmono : Monotone lev) (hexh : ∀ g : G, g ∈ N ↔ ∃ n, g ∈ lev n)
    (T : Finset G) :
    ∃ n : ℕ, ∀ a ∈ T, ∀ b ∈ T,
      ((QuotientGroup.mk a : G ⧸ lev n) = QuotientGroup.mk b
        ↔ (QuotientGroup.mk a : G ⧸ N) = QuotientGroup.mk b) := by
  obtain ⟨n, hn⟩ := exists_level_separating lev N hmono hexh T
  refine ⟨n, fun a ha b hb => ?_⟩
  simp only [QuotientGroup.eq]
  exact (hn a ha b hb).symm

end Core

/-! ## Level chains and their site maps -/

/-- An increasing chain of subgroups of `G` together with the subgroup it
exhausts.  The telescope of Section 37 is such a chain: `lev n = Γₙ` and
`limit = N = ⋃ₙ Γₙ`.

No member is asked to be normal, and no member is asked to be proper. -/
structure LevelChain (G : Type u) [Group G] where
  /-- The levels `Γₙ`. -/
  lev : ℕ → Subgroup G
  /-- The subgroup the levels exhaust, `N = ⋃ₙ Γₙ`. -/
  limit : Subgroup G
  /-- The levels increase. -/
  mono : Monotone lev
  /-- The levels exhaust the limit, and nothing more. -/
  exhausts : ∀ g : G, g ∈ limit ↔ ∃ n, g ∈ lev n

namespace LevelChain

variable {G : Type u} [Group G] (C : LevelChain G)

/-- Every level sits inside the limit. -/
theorem lev_le_limit (n : ℕ) : C.lev n ≤ C.limit :=
  fun _ hg => (C.exhausts _).mpr ⟨n, hg⟩

/-- The site map `X 0 → X n` of the telescope. -/
def proj (n : ℕ) : G ⧸ C.lev 0 → G ⧸ C.lev n :=
  Subgroup.quotientMapOfLE (C.mono (Nat.zero_le n))

/-- The site map `X 0 → X∞` to the limit site set. -/
def projLimit : G ⧸ C.lev 0 → G ⧸ C.limit :=
  Subgroup.quotientMapOfLE (C.lev_le_limit 0)

@[simp] theorem proj_mk (n : ℕ) (g : G) :
    C.proj n (QuotientGroup.mk g) = (QuotientGroup.mk g : G ⧸ C.lev n) := rfl

@[simp] theorem projLimit_mk (g : G) :
    C.projLimit (QuotientGroup.mk g) = (QuotientGroup.mk g : G ⧸ C.limit) := rfl

/-- The tower commutes: the limit projection factors through every stage.  This
is the factorisation hypothesis both kernel engines ask for. -/
theorem projLimit_eq_comp (n : ℕ) :
    C.projLimit = Subgroup.quotientMapOfLE (C.lev_le_limit n) ∘ C.proj n := by
  funext x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rfl

/-- Consecutive stages compose. -/
theorem proj_trans {m n : ℕ} (h : m ≤ n) :
    Subgroup.quotientMapOfLE (C.mono h) ∘ C.proj m = C.proj n := by
  funext x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rfl

/-- Stages refine the limit: sites merged at a finite stage are merged in the
limit. -/
theorem projLimit_eq_of_proj_eq (n : ℕ) {x y : G ⧸ C.lev 0}
    (h : C.proj n x = C.proj n y) : C.projLimit x = C.projLimit y := by
  rw [C.projLimit_eq_comp n]
  exact congrArg (Subgroup.quotientMapOfLE (C.lev_le_limit n)) h

/-- Later stages merge more: the fibres coarsen along the tower. -/
theorem proj_eq_of_le {m n : ℕ} (hmn : m ≤ n) {x y : G ⧸ C.lev 0}
    (h : C.proj m x = C.proj m y) : C.proj n x = C.proj n y := by
  rw [← C.proj_trans hmn]
  exact congrArg (Subgroup.quotientMapOfLE (C.mono hmn)) h

/-- **Pointwise separation.**  Two sites merged in the limit are merged at some
finite stage.  This is exhaustion and nothing else: the ratio of two
representatives lies in `N`, hence in a single level. -/
theorem exists_stage_of_projLimit_eq {x y : G ⧸ C.lev 0}
    (h : C.projLimit x = C.projLimit y) : ∃ n : ℕ, C.proj n x = C.proj n y := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  rw [projLimit_mk, projLimit_mk, QuotientGroup.eq] at h
  obtain ⟨n, hn⟩ := (C.exhausts _).mp h
  refine ⟨n, ?_⟩
  rw [proj_mk, proj_mk, QuotientGroup.eq]
  exact hn

/-- **Uniform separation.**  Given a *finite* set of sites there is a single
stage whose fibres cut it exactly as the limit fibres do.

The pointwise statement above cannot be used directly for a value-based
kernel computation, because different pairs of the finite set could a priori
need different stages.  Finiteness removes that: pass to representatives, apply
`exists_level_separating` to the finite set of representatives, and take the
level it produces. -/
theorem exists_stage_separating (S : Finset (G ⧸ C.lev 0)) :
    ∃ n : ℕ, ∀ x ∈ S, ∀ y ∈ S,
      C.projLimit x = C.projLimit y → C.proj n x = C.proj n y := by
  classical
  obtain ⟨n, hn⟩ := exists_level_separating C.lev C.limit C.mono C.exhausts
    (S.image Quotient.out)
  refine ⟨n, fun x hx y hy hxy => ?_⟩
  have hxo : (QuotientGroup.mk (Quotient.out x) : G ⧸ C.lev 0) = x :=
    QuotientGroup.out_eq' x
  have hyo : (QuotientGroup.mk (Quotient.out y) : G ⧸ C.lev 0) = y :=
    QuotientGroup.out_eq' y
  have hmx : Quotient.out x ∈ S.image Quotient.out := Finset.mem_image_of_mem _ hx
  have hmy : Quotient.out y ∈ S.image Quotient.out := Finset.mem_image_of_mem _ hy
  have hlim : (QuotientGroup.mk (Quotient.out x) : G ⧸ C.limit)
      = QuotientGroup.mk (Quotient.out y) :=
    calc (QuotientGroup.mk (Quotient.out x) : G ⧸ C.limit)
        = C.projLimit (QuotientGroup.mk (Quotient.out x)) := rfl
      _ = C.projLimit x := by rw [hxo]
      _ = C.projLimit y := hxy
      _ = C.projLimit (QuotientGroup.mk (Quotient.out y)) := by rw [hyo]
      _ = QuotientGroup.mk (Quotient.out y) := rfl
  have hstage : (Quotient.out x)⁻¹ * Quotient.out y ∈ C.lev n :=
    (hn _ hmx _ hmy).mp (QuotientGroup.eq.mp hlim)
  calc C.proj n x
      = C.proj n (QuotientGroup.mk (Quotient.out x)) := by rw [hxo]
    _ = QuotientGroup.mk (Quotient.out x) := rfl
    _ = QuotientGroup.mk (Quotient.out y) := QuotientGroup.eq.mpr hstage
    _ = C.proj n (QuotientGroup.mk (Quotient.out y)) := rfl
    _ = C.proj n y := by rw [hyo]

end LevelChain

/-! ## The limit kernel on the `Finsupp` lamp model

`AbLamp A X = Multiplicative (X →₀ A)` and the pushforward is
`Finsupp.mapDomain`.  The arithmetic is `AbLamp.ker_push_eq_iSup`; everything
below is the coset instantiation of its hypotheses. -/

section AbelianLamps

variable {G : Type u} [Group G] {A : Type v} [AddCommGroup A]

/-- **Equation (37.17) on the `Finsupp` model.**  The kernel of the pushforward
to the limit site set is the supremum of the kernels of the finite stages. -/
theorem ker_push_projLimit_eq_iSup (C : LevelChain G) :
    (AbLamp.push (A := A) C.projLimit).ker
      = ⨆ n : ℕ, (AbLamp.push (A := A) (C.proj n)).ker :=
  AbLamp.ker_push_eq_iSup (A := A) C.proj C.projLimit
    (fun n => ⟨Subgroup.quotientMapOfLE (C.lev_le_limit n), C.projLimit_eq_comp n⟩)
    C.exists_stage_separating

/-- The stage kernels increase along the tower. -/
theorem ker_push_proj_mono (C : LevelChain G) {m n : ℕ} (h : m ≤ n) :
    (AbLamp.push (A := A) (C.proj m)).ker ≤ (AbLamp.push (A := A) (C.proj n)).ker := by
  rw [← C.proj_trans h]
  exact AbLamp.ker_le_ker_comp _ _

/-- Being increasing, the stage kernels are directed, so their supremum is their
union. -/
theorem directed_ker_push_proj (C : LevelChain G) :
    Directed (· ≤ ·) fun n : ℕ => (AbLamp.push (A := A) (C.proj n)).ker :=
  fun m n => ⟨max m n, ker_push_proj_mono C (le_max_left m n),
    ker_push_proj_mono C (le_max_right m n)⟩

/-- **Equation (37.17), union form.**  A configuration killed by the limit
pushforward is killed at a single finite stage — not merely a product of
elements each killed at some stage.  This is the shape the tower induction of
`TelescopeRadicalInduction` consumes. -/
theorem mem_ker_push_projLimit_iff (C : LevelChain G)
    {f : AbLamp A (G ⧸ C.lev 0)} :
    f ∈ (AbLamp.push (A := A) C.projLimit).ker
      ↔ ∃ n : ℕ, f ∈ (AbLamp.push (A := A) (C.proj n)).ker := by
  rw [ker_push_projLimit_eq_iSup]
  exact Subgroup.mem_iSup_of_directed (directed_ker_push_proj C)

end AbelianLamps

/-! ## The limit kernel on the general lamp model

`Lamp K X` for a commutative lamp group `K`.  The arithmetic is
`WreathTelescope.mem_ker_pushHom_limit`, whose kernel description is by
generators, so only the pointwise separation is needed. -/

section GeneralLamps

variable {G : Type u} [Group G] {K : Type v} [CommGroup K]

/-- **Equation (37.17) on the general lamp model, union form.** -/
theorem mem_ker_pushHom_projLimit_iff (C : LevelChain G)
    (f : Lamp K (G ⧸ C.lev 0)) :
    f ∈ (WreathLampPushforward.pushHom (K := K) C.projLimit).ker
      ↔ ∃ n : ℕ, f ∈ (WreathLampPushforward.pushHom (K := K) (C.proj n)).ker :=
  WreathTelescope.mem_ker_pushHom_limit (K := K) C.proj C.projLimit
    (fun n _ _ h => C.projLimit_eq_of_proj_eq n h)
    (fun _ _ hnm h => C.proj_eq_of_le hnm h)
    (fun _ _ h => C.exists_stage_of_projLimit_eq h) f

/-- **Equation (37.17) on the general lamp model, supremum form.** -/
theorem ker_pushHom_projLimit_eq_iSup (C : LevelChain G) :
    (WreathLampPushforward.pushHom (K := K) C.projLimit).ker
      = ⨆ n : ℕ, (WreathLampPushforward.pushHom (K := K) (C.proj n)).ker :=
  WreathTelescope.ker_pushHom_limit (K := K) C.proj C.projLimit
    (fun n _ _ h => C.projLimit_eq_of_proj_eq n h)
    (fun _ _ hnm h => C.proj_eq_of_le hnm h)
    (fun _ _ h => C.exists_stage_of_projLimit_eq h)

end GeneralLamps

end TelescopeLimitKernel
end GroupApproximation
