import GroupApproximation.Algebra.WreathLampPushforward

/-!
# Section 37.1 in full generality: the wreath product is a functor

`Algebra/WreathLampPushforward.pushWreath` pushes a permutational wreath
product along a map of sites while keeping the acting group fixed -- that is the
form the telescope of Section 37 iterates, where the acting group `G` never
changes and only the site space `G/Γₙ` moves.

Several statements of the dossier need the acting group to move as well.  Lemma
37.7A reduces the lamplighter `A^{(ℤ)} ⋊ ℤ` modulo `m` in *both* coordinates at
once: the sites `ℤ ↠ ℤ/m` and the shift `ℤ ↠ ℤ/m`.  This file supplies that
map.

`wreathMap φ q hq : K^{(X)} ⋊ G →* K^{(Y)} ⋊ G'` is defined for a group
homomorphism `φ : G →* G'` and a site map `q : X → Y` which is equivariant over
`φ`, i.e. `q (g • x) = φ g • q x`.  Taking `G' = G` and `φ = id` recovers
`pushWreath`.

The only real content is `push_lampAut_hom`: the fibre product defining the
pushforward commutes with the site action, now across two different acting
groups.  It is the proof of `push_lampAut` with `g •` on the target replaced by
`φ g •` throughout.
-/

namespace GroupApproximation

namespace WreathLampPushforward

universe u v w v' w'

variable {K : Type u} [CommGroup K] {X : Type v} {Y : Type v'}
variable {G : Type w} [Group G] {G' : Type w'} [Group G']
variable [MulAction G X] [MulAction G' Y] [DecidableEq X]

/-- **Equivariance of the pushforward across a change of acting group.**  If the
site map intertwines the two actions through `φ`, then pushing forward commutes
with the lamp automorphisms. -/
theorem push_lampAut_hom (φ : G →* G') (q : X → Y)
    (hq : ∀ (g : G) (x : X), q (g • x) = φ g • q x)
    (g : G) (f : Lamp K X) :
    push q (lampAut (K := K) g f) = lampAut (φ g) (push q f) := by
  classical
  refine Lamp.ext fun y => ?_
  rw [push_apply, lampAut_apply, push_apply, pushFun, pushFun, supp_lampAut]
  have hfilter : ((supp f).image (fun x => g • x)).filter (fun x => q x = y)
      = ((supp f).filter (fun x => q x = (φ g)⁻¹ • y)).image (fun x => g • x) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨x', hx', rfl⟩, hq'⟩
      refine ⟨x', ⟨hx', ?_⟩, rfl⟩
      rw [hq] at hq'
      rw [← hq', inv_smul_smul]
    · rintro ⟨x', ⟨hx', hq'⟩, rfl⟩
      refine ⟨⟨x', hx', rfl⟩, ?_⟩
      rw [hq, hq', smul_inv_smul]
  rw [hfilter, Finset.prod_image (fun a _ b _ hab => by
    simpa using congrArg (fun z => g⁻¹ • z) hab)]
  exact Finset.prod_congr rfl fun x _ => by rw [lampAut_apply, inv_smul_smul]

/-- **The wreath product as a functor of the pair (acting group, site set).**
An equivariant map of sites over a group homomorphism induces a homomorphism of
permutational wreath products, acting as the pushforward on lamps and as `φ` on
the acting group. -/
noncomputable def wreathMap (φ : G →* G') (q : X → Y)
    (hq : ∀ (g : G) (x : X), q (g • x) = φ g • q x) :
    Wreath K G X →* Wreath K G' Y :=
  SemidirectProduct.map (pushHom q) φ (by
    intro g
    refine MonoidHom.ext fun f => ?_
    show push q (lampAut g f) = lampAut (φ g) (push q f)
    exact push_lampAut_hom φ q hq g f)

@[simp] theorem wreathMap_left (φ : G →* G') (q : X → Y)
    (hq : ∀ (g : G) (x : X), q (g • x) = φ g • q x) (w : Wreath K G X) :
    (wreathMap φ q hq w).left = push q w.left := rfl

@[simp] theorem wreathMap_right (φ : G →* G') (q : X → Y)
    (hq : ∀ (g : G) (x : X), q (g • x) = φ g • q x) (w : Wreath K G X) :
    (wreathMap φ q hq w).right = φ w.right := rfl

/-- On the acting group the functor is `φ`. -/
theorem wreathMap_inr (φ : G →* G') (q : X → Y)
    (hq : ∀ (g : G) (x : X), q (g • x) = φ g • q x) (g : G) :
    wreathMap (K := K) φ q hq (SemidirectProduct.inr g)
      = SemidirectProduct.inr (φ g) := by
  refine SemidirectProduct.ext ?_ rfl
  show push q (1 : Lamp K X) = 1
  exact map_one (pushHom q)

/-- On the lamp subgroup the functor is the pushforward. -/
theorem wreathMap_inl (φ : G →* G') (q : X → Y)
    (hq : ∀ (g : G) (x : X), q (g • x) = φ g • q x) (f : Lamp K X) :
    wreathMap φ q hq (SemidirectProduct.inl f)
      = SemidirectProduct.inl (push q f) := by
  refine SemidirectProduct.ext rfl ?_
  exact map_one φ

end WreathLampPushforward

end GroupApproximation
