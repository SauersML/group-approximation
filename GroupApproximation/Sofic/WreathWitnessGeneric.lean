import GroupApproximation.Algebra.PermutationalWreathSimple
import GroupApproximation.Sofic.CollapseUniverseScopeDefs
import GroupApproximation.Sofic.InvolutionCollapseEndpoint

/-!
# One-site lamps are involutive compression witnesses, in any wreath product

`non_mf_groups_exist.tex`, the paragraph between `def:invwitness` and
`thm:collapse` (grep `"In a permutational wreath product"`, never a line
number: the file is edited concurrently):

> In a permutational wreath product `K^{(X)} ⋊ G` with `L ≤ G` compressed by
> `s` and `x₀ ∈ X` a point fixed by `s L s⁻¹`, every involution of the Clifford
> copy at `x₀` is a witness: generators at distinct points commute, and the
> compressed copy fixes the point.

That sentence is general: arbitrary lamp group `K`, arbitrary site set `X`,
arbitrary acting group `G`, arbitrary subgroup `L ≤ G`.  The repository proved
it only for the Clifford-lamp ambient group of the ascending-HNN construction,
which is one instance of it.  This module states and proves the general
sentence, on `Algebra.PermutationalWreath`'s `Wreath K G X`, and the
ascending-HNN witness in `Sofic.AscendingHNNWreathWitness` is derived from it.

The two reasons the manuscript gives are the two nontrivial conditions:

* *the compressed copy fixes the point* is `(W2)`: conjugating a one-site lamp
  by an element of `G` moves the site (`conj_inl_single`), so an element
  fixing `x₀` fixes the lamp outright and therefore commutes with it;
* *generators at distinct points commute* is `(W3)`: two `G`-conjugates of the
  same one-site lamp sit at the sites `γ₁ • x₀` and `γ₂ • x₀`, and they either
  sit at distinct sites, where the restricted direct product makes them
  commute, or they are literally the same element.  Note that no commutativity
  of `K` is used --- which is exactly why the lamp group may be the nonabelian
  Clifford group.

`(W1)` needs only that the lamp value is an involution, which is the
manuscript's "every involution of the Clifford copy at `x₀`".

Nothing here is analytic; the collapse theorem that consumes the witness lives
in `Sofic.InvolutionCollapseEndpoint`.
-/

namespace GroupApproximation
namespace WreathWitness

open SemidirectProduct

universe u v w

/-! ## What the wreath sentence actually uses

The proof of the printed sentence uses three facts about the lamps and nothing
else: each lamp is an involution, lamps commute, and conjugation by the acting
group moves a lamp's site.  Isolating them as data makes the sentence available
to *every* group carrying such a family, not only to groups that are literally
`K^{(X)} ⋊ G`.

That extra reach is not decoration.  The manuscript's own collapse example is
the sign-free quotient of the Kazhdan--Clifford group, whose lamps commute only
*after* the central Clifford sign is killed; it is not a permutational wreath
product in this repository's sense, and no isomorphism onto one is available
without normal-form theory for the Clifford presentation.  It does carry a lamp
family, so it gets the sentence.  See `Sofic.WreathWitnessSignFree`. -/

/-- A conjugation-equivariant family of commuting involutions indexed by a
`G`-set: the abstract content of "the lamps of `K^{(X)} ⋊ G` at the sites
`X`". -/
structure LampFamily (H : Type u) [Group H] (G : Type w) [Group G]
    (X : Type v) [MulAction G X] where
  /-- The lamp sitting at a given site. -/
  lam : X → H
  /-- The acting group, realized inside the ambient group. -/
  emb : G →* H
  /-- Every lamp is an involution.  This is `(W1)`. -/
  lam_mul_self : ∀ x : X, lam x * lam x = 1
  /-- Lamps commute, whatever their sites.  This is what `(W3)` needs, and it
  is the clause the Clifford lamps satisfy only after the sign is killed. -/
  lam_commute : ∀ x y : X, Commute (lam x) (lam y)
  /-- Conjugating a lamp by the acting group moves its site and nothing
  else. -/
  conj_lam : ∀ (g : G) (x : X), emb g * lam x * (emb g)⁻¹ = lam (g • x)

namespace LampFamily

variable {H : Type u} [Group H] {G : Type w} [Group G] {X : Type v}
variable [MulAction G X] (F : LampFamily H G X)

/-- An element of the acting group fixing a site centralizes the lamp
there. -/
theorem commute_emb_lam_of_fixed {g : G} {x : X} (hfix : g • x = x) :
    Commute (F.emb g) (F.lam x) := by
  have h : F.emb g * F.lam x * (F.emb g)⁻¹ = F.lam x := by
    rw [F.conj_lam g x, hfix]
  exact mul_inv_eq_iff_eq_mul.mp h

/-- **The printed wreath sentence, for any lamp family.**  If `x₀` is fixed by
the `s`-compressed copy of `L`, the lamp at `x₀` is an involutive compression
witness for the image of `L` and the image of `s`.

The two reasons the manuscript gives are the two hypotheses used: `conj_lam`
plus the fixed point gives `(W2)`, and `lam_commute` gives `(W3)`. -/
theorem isInvolutiveCompressionWitness (L : Subgroup G) (s : G) (x₀ : X)
    (hfix : ∀ γ ∈ L, (s * γ * s⁻¹) • x₀ = x₀) :
    CollapseUniverseScope.IsInvolutiveCompressionWitness
      (L.map F.emb) (F.emb s) (F.lam x₀) := by
  refine ⟨F.lam_mul_self x₀, ?_, ?_⟩
  · rintro _ ⟨γ, hγ, rfl⟩
    have hrw : F.emb s * F.emb γ * (F.emb s)⁻¹ = F.emb (s * γ * s⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    rw [hrw]
    exact F.commute_emb_lam_of_fixed (hfix γ hγ)
  · rintro _ ⟨γ₁, -, rfl⟩ _ ⟨γ₂, -, rfl⟩
    rw [F.conj_lam γ₁ x₀, F.conj_lam γ₂ x₀]
    exact F.lam_commute _ _

end LampFamily

section Generic

variable {K : Type u} [Group K] {G : Type w} [Group G] {X : Type v}
variable [MulAction G X] [DecidableEq X]

/-- The lamp carrying the value `k₀` at the single site `x₀`, seen inside the
wreath product.  This is the manuscript's "involution of the Clifford copy at
`x₀`" once `k₀` is an involution. -/
def siteLamp (x₀ : X) (k₀ : K) : Wreath K G X :=
  inl (Lamp.single x₀ k₀)

/-- **(W1) for a torsion lamp value.**  The one-site lamp inherits the order of
its value. -/
theorem siteLamp_pow (x₀ : X) (k₀ : K) (m : ℕ) (hk : k₀ ^ m = 1) :
    siteLamp (G := G) x₀ k₀ ^ m = 1 := by
  have hsingle : Lamp.single x₀ k₀ ^ m = (1 : Lamp K X) := by
    have h1 : (Lamp.singleHom (K := K) x₀) (k₀ ^ m) =
        Lamp.single x₀ k₀ ^ m := by
      rw [map_pow, Lamp.singleHom_apply]
    rw [hk, map_one] at h1
    exact h1.symm
  rw [siteLamp, ← map_pow, hsingle, map_one]

/-- **(W1).**  An involutive lamp value gives an involutive one-site lamp. -/
theorem siteLamp_mul_self (x₀ : X) {k₀ : K} (hk : k₀ * k₀ = 1) :
    siteLamp (G := G) x₀ k₀ * siteLamp (G := G) x₀ k₀ = 1 := by
  have hsingle : Lamp.single x₀ k₀ * Lamp.single x₀ k₀ = (1 : Lamp K X) := by
    have h1 := map_mul (Lamp.singleHom (K := K) x₀) k₀ k₀
    rw [hk, map_one] at h1
    simpa using h1.symm
  rw [siteLamp, ← map_mul, hsingle, map_one]

/-- **(W2), the manuscript's "the compressed copy fixes the point".**  An
element of the acting group that fixes the site commutes with the one-site lamp
there, because conjugation by it only moves the site. -/
theorem commute_inr_siteLamp (g : G) (x₀ : X) (k₀ : K) (hfix : g • x₀ = x₀) :
    Commute (inr g : Wreath K G X) (siteLamp x₀ k₀) := by
  have hconj : (inr g : Wreath K G X) * siteLamp x₀ k₀ * (inr g)⁻¹ =
      siteLamp x₀ k₀ := by
    rw [siteLamp, conj_inl_single K G X, hfix]
  exact mul_inv_eq_iff_eq_mul.mp hconj

/-- **(W3), the manuscript's "generators at distinct points commute".**  Two
conjugates of the same one-site lamp by elements of the acting group commute:
either their sites differ, and lamps at distinct sites commute in the
restricted direct product, or the two conjugates are the same element.  No
hypothesis on `K` is used. -/
theorem commute_conj_siteLamp (g₁ g₂ : G) (x₀ : X) (k₀ : K) :
    Commute ((inr g₁ : Wreath K G X) * siteLamp x₀ k₀ * (inr g₁)⁻¹)
      ((inr g₂ : Wreath K G X) * siteLamp x₀ k₀ * (inr g₂)⁻¹) := by
  rw [siteLamp, conj_inl_single K G X, conj_inl_single K G X]
  have hbase := conj_single_commute (K := K) g₁ g₂ x₀ k₀
  rw [lampAut_single, lampAut_single] at hbase
  exact (show Commute _ _ from hbase).map
    (inl : Lamp K X →* Wreath K G X)

/-! ## The packaged witness

The three conditions are assembled once, in the raw conjunction that both
spellings of the witness predicate unfold to, and the two named predicates are
then immediate. -/

/-- **The manuscript's permutational-wreath sentence, unpackaged.**  Let `L` be
any subgroup of the wreath product every element of which lies in the acting
copy and whose `s`-conjugate fixes the site `x₀`.  Then the one-site lamp at
`x₀` with involutive value satisfies the three conditions `(W1)`--`(W3)` for
`(L, inr s)`.

The single hypothesis `hL` is the manuscript's "`L ≤ G` compressed by `s` and
`x₀ ∈ X` a point fixed by `s L s⁻¹`", packaged so that it can be discharged
directly from whatever description of `L` a caller has. -/
theorem siteLamp_witness_conditions {L : Subgroup (Wreath K G X)} (s : G)
    (x₀ : X) {k₀ : K} (hk : k₀ * k₀ = 1)
    (hL : ∀ w ∈ L, ∃ g : G, (inr g : Wreath K G X) = w ∧ (s * g * s⁻¹) • x₀ = x₀) :
    siteLamp (G := G) x₀ k₀ * siteLamp (G := G) x₀ k₀ = 1 ∧
      (∀ γ ∈ L, Commute ((inr s : Wreath K G X) * γ * (inr s)⁻¹)
        (siteLamp x₀ k₀)) ∧
      (∀ γ₁ ∈ L, ∀ γ₂ ∈ L,
        Commute (γ₁ * siteLamp x₀ k₀ * γ₁⁻¹) (γ₂ * siteLamp x₀ k₀ * γ₂⁻¹)) := by
  refine ⟨siteLamp_mul_self x₀ hk, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨g, rfl, hfix⟩ := hL γ hγ
    have hrw : (inr s : Wreath K G X) * inr g * (inr s)⁻¹ =
        inr (s * g * s⁻¹) := by
      rw [← map_inv, ← map_mul, ← map_mul]
    rw [hrw]
    exact commute_inr_siteLamp _ x₀ k₀ hfix
  · intro γ₁ hγ₁ γ₂ hγ₂
    obtain ⟨g₁, rfl, -⟩ := hL γ₁ hγ₁
    obtain ⟨g₂, rfl, -⟩ := hL γ₂ hγ₂
    exact commute_conj_siteLamp g₁ g₂ x₀ k₀

/-- **The manuscript's permutational-wreath sentence**, at the manuscript's
scope: the ambient group lives in an arbitrary universe, as `thm:collapse`
requires. -/
theorem isInvolutiveCompressionWitness_siteLamp
    {L : Subgroup (Wreath K G X)} (s : G) (x₀ : X) {k₀ : K}
    (hk : k₀ * k₀ = 1)
    (hL : ∀ w ∈ L, ∃ g : G, (inr g : Wreath K G X) = w ∧ (s * g * s⁻¹) • x₀ = x₀) :
    CollapseUniverseScope.IsInvolutiveCompressionWitness L
      (inr s : Wreath K G X) (siteLamp x₀ k₀) :=
  siteLamp_witness_conditions s x₀ hk hL

/-- **The one-site lamps of a permutational wreath product are a lamp
family.**  The commutation clause needs no hypothesis on `K`: two one-site
lamps at the same site are the same element, and at distinct sites they commute
because the base is a restricted direct product. -/
def wreathLampFamily {k₀ : K} (hk : k₀ * k₀ = 1) :
    LampFamily (Wreath K G X) G X where
  lam x := siteLamp x k₀
  emb := inr
  lam_mul_self := fun x => siteLamp_mul_self x hk
  lam_commute := fun x y => by
    by_cases h : x = y
    · subst h
      exact Commute.refl _
    · exact (show Commute (Lamp.single x k₀) (Lamp.single y k₀) from
        Lamp.single_commute h k₀ k₀).map (inl : Lamp K X →* Wreath K G X)
  conj_lam := fun g x => by
    rw [siteLamp, siteLamp, conj_inl_single K G X]

@[simp] theorem wreathLampFamily_lam {k₀ : K} (hk : k₀ * k₀ = 1) (x : X) :
    (wreathLampFamily (G := G) hk).lam x = siteLamp x k₀ := rfl

@[simp] theorem wreathLampFamily_emb {k₀ : K} (hk : k₀ * k₀ = 1) :
    (wreathLampFamily (G := G) (X := X) hk).emb = (inr : G →* Wreath K G X) :=
  rfl

/-- The same sentence with `L` presented the way the manuscript writes it, as a
subgroup of the *acting* group `G` carried into the wreath product, and the
site fixed by the compressed copy `s L s⁻¹`.  This is the lamp-family theorem
read at `wreathLampFamily`; the wreath product is one instance of the
abstraction, and `Sofic.WreathWitnessSignFree` is the other. -/
theorem isInvolutiveCompressionWitness_map_inr (L : Subgroup G) (s : G)
    (x₀ : X) {k₀ : K} (hk : k₀ * k₀ = 1)
    (hfix : ∀ γ ∈ L, (s * γ * s⁻¹) • x₀ = x₀) :
    CollapseUniverseScope.IsInvolutiveCompressionWitness
      (L.map (inr : G →* Wreath K G X)) (inr s : Wreath K G X)
      (siteLamp x₀ k₀) :=
  (wreathLampFamily hk).isInvolutiveCompressionWitness L s x₀ hfix

end Generic

/-! ## The `Type 0` spelling used by the collapse endpoint

`Sofic.InvolutionCollapseEndpoint` states its witness predicate only for
ambient groups in `Type 0`.  There it is the same conjunction, so the general
theorem specializes without any further argument. -/

section Zero

variable {K : Type} [Group K] {G : Type} [Group G] {X : Type}
variable [MulAction G X] [DecidableEq X]

/-- The `Type 0` spelling of the wreath sentence, for the consumers of
`InvolutionCollapseEndpoint.IsInvolutiveCompressionWitness`. -/
theorem isInvolutiveCompressionWitness_siteLamp_zero
    {L : Subgroup (Wreath K G X)} (s : G) (x₀ : X) {k₀ : K}
    (hk : k₀ * k₀ = 1)
    (hL : ∀ w ∈ L, ∃ g : G, (inr g : Wreath K G X) = w ∧ (s * g * s⁻¹) • x₀ = x₀) :
    InvolutionCollapseEndpoint.IsInvolutiveCompressionWitness L
      (inr s : Wreath K G X) (siteLamp x₀ k₀) :=
  siteLamp_witness_conditions s x₀ hk hL

end Zero

end WreathWitness
end GroupApproximation
