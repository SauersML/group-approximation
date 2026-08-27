import GroupApproximation.Sofic.LinearResidual
import GroupApproximation.Algebra.PermutationalWreathSimple
import GroupApproximation.Algebra.WreathSplitQuotient

/-!
# Functoriality of the approximation radicals and canonical descent

**Sections 50 to 52** of the ascending-HNN dossier, in the form that needs no
concrete family.

Each radical of the dossier is cut out by a class of target groups: an element belongs to it
exactly when every homomorphism into that class kills it.  A subgroup of this shape is
automatically functorial, because a representation of the target pulls back along a homomorphism
to a representation of the source, and the pullback kills whatever the source radical contains.
`GroupApproximation.map_finiteResidual_le` records the argument for the finite residual
(Lemma 50.1); the same two lines are carried out here for the cofinite-corona MF radical, the
finite-dimensional unitary residual and the all-fields linear residual, in every case without a
countability hypothesis on either group.

Applied to endomorphisms this says the four radicals are *fully invariant*, a condition strictly
stronger than being characteristic: not merely automorphisms but all endomorphisms preserve them.
The consequence is Theorem 50.2.  A fully invariant normal subgroup `R` turns the quotient map
`G → G ⧸ R` into a functor on the endomorphism monoid: every `f : G →* G` has a unique
`f̄ : G ⧸ R →* G ⧸ R` with `f̄ ∘ mk = mk ∘ f`, the identity descends to the identity, composites
descend to composites, and therefore an automorphism descends to an automorphism, which is
Corollary 50.3.  Nothing about the concrete family enters; what the dossier adds there is the
separate computation identifying the telescope kernel with the finite residual.

The file closes the two leftovers of Sections 51 and 52 that are provable from the abstract wreath
picture.  `GroupApproximation.lamp_le_normalClosure_single` already shows that a single nontrivial
one-site lamp normally generates every configuration; the reverse inclusion is immediate because
the lamp subgroup is the kernel of the wreath projection, so the normal closure is *exactly* the
lamp subgroup (Theorem 51.1), the quotient by that one relation is the acting group
(Corollary 51.2), and the relation is invisible to finite generation: over an infinite site set a
nontrivial lamp group has a lamp subgroup that is not finitely generated (Corollary 51.1A) even
though one element normally generates it.  Finally the size half of Lemma 52.1 is recorded as a
standalone statement: alternating groups of different degrees are not isomorphic.
-/

namespace GroupApproximation

namespace RadicalFunctoriality

open MatricialStabilityRadical

universe u v w

/-! ## Functoriality of the three remaining radicals -/

section Functoriality

variable {G : Type u} [Group G] {H : Type v} [Group H]

/-- **Lemma 50.1 for the MF radical.**  A corona representation of the target pulls back along a
homomorphism, so nothing invisible in the source can become visible in the image.  Unlike
`GroupApproximation.map_coronaMFResidual_le`, which routes through the ultraproduct radical, this
needs no countability assumption: the pullback is available for arbitrary groups. -/
theorem map_coronaMFResidual_le (f : G →* H) :
    (coronaMFResidual G).map f ≤ coronaMFResidual H := by
  rw [SetLike.le_def]
  rintro _ ⟨x, hx, rfl⟩
  have hx' : CoronaMFInvisible x := hx
  show CoronaMFInvisible (f x)
  intro X hX rho
  exact hx' X hX (rho.comp f)

/-- **Lemma 50.1 for the finite-dimensional unitary residual.**  A finite-dimensional unitary
representation of the target pulls back to one of the source. -/
theorem map_fdUnitaryResidual_le (f : G →* H) :
    (fdUnitaryResidual G).map f ≤ fdUnitaryResidual H := by
  rw [SetLike.le_def]
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_fdUnitaryResidual_iff]
  intro Y phi
  exact mem_fdUnitaryResidual_iff.mp hx Y (phi.comp f)

/-- **Lemma 50.1 for the all-fields linear residual.**  A finite-dimensional linear representation
of the target over a field pulls back to one of the source over the same field. -/
theorem map_linearResidual_le (f : G →* H) :
    (linearResidual G).map f ≤ linearResidual H := by
  rw [SetLike.le_def]
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_linearResidual_iff]
  intro F hF d rho
  exact mem_linearResidual_iff.mp hx F hF d (rho.comp f)

end Functoriality

/-! ## Full invariance -/

section Invariance

variable {G : Type u} [Group G]

/-- A subgroup is fully invariant when every endomorphism of the ambient group maps it into
itself.  This is the condition isolated after (50.3): it holds for a radical cut out by a class of
target groups, and it is strictly stronger than being characteristic. -/
def IsFullyInvariant (R : Subgroup G) : Prop := ∀ f : G →* G, R.map f ≤ R

/-- A fully invariant subgroup is normal: conjugation is an endomorphism. -/
theorem normal_of_isFullyInvariant (R : Subgroup G) (hR : IsFullyInvariant R) : R.Normal := by
  refine ⟨fun x hx g => ?_⟩
  simpa using hR (MulAut.conj g).toMonoidHom (Subgroup.mem_map_of_mem _ hx)

/-- A fully invariant subgroup is characteristic: an automorphism and its inverse are both
endomorphisms, so the two inclusions of (50.3) combine into an equality. -/
theorem characteristic_of_isFullyInvariant (R : Subgroup G) (hR : IsFullyInvariant R) :
    R.Characteristic := by
  constructor
  intro phi
  ext x
  simp only [Subgroup.mem_comap]
  constructor
  · intro hx
    simpa using hR phi.symm.toMonoidHom (Subgroup.mem_map_of_mem _ hx)
  · intro hx
    exact hR phi.toMonoidHom (Subgroup.mem_map_of_mem _ hx)

/-- The finite residual is fully invariant. -/
theorem finiteResidual_isFullyInvariant : IsFullyInvariant (finiteResidual G) :=
  fun f => map_finiteResidual_le f

/-- The cofinite-corona MF radical is fully invariant. -/
theorem coronaMFResidual_isFullyInvariant : IsFullyInvariant (coronaMFResidual G) :=
  fun f => map_coronaMFResidual_le f

/-- The finite-dimensional unitary residual is fully invariant. -/
theorem fdUnitaryResidual_isFullyInvariant : IsFullyInvariant (fdUnitaryResidual G) :=
  fun f => map_fdUnitaryResidual_le f

/-- The all-fields linear residual is fully invariant. -/
theorem linearResidual_isFullyInvariant : IsFullyInvariant (linearResidual G) :=
  fun f => map_linearResidual_le f

instance finiteResidual_normal : (finiteResidual G).Normal :=
  normal_of_isFullyInvariant _ finiteResidual_isFullyInvariant

instance fdUnitaryResidual_normal : (fdUnitaryResidual G).Normal :=
  normal_of_isFullyInvariant _ fdUnitaryResidual_isFullyInvariant

instance linearResidual_normal : (linearResidual G).Normal :=
  normal_of_isFullyInvariant _ linearResidual_isFullyInvariant

instance finiteResidual_characteristic : (finiteResidual G).Characteristic :=
  characteristic_of_isFullyInvariant _ finiteResidual_isFullyInvariant

instance coronaMFResidual_characteristic : (coronaMFResidual G).Characteristic :=
  characteristic_of_isFullyInvariant _ coronaMFResidual_isFullyInvariant

instance fdUnitaryResidual_characteristic : (fdUnitaryResidual G).Characteristic :=
  characteristic_of_isFullyInvariant _ fdUnitaryResidual_isFullyInvariant

instance linearResidual_characteristic : (linearResidual G).Characteristic :=
  characteristic_of_isFullyInvariant _ linearResidual_isFullyInvariant

end Invariance

/-! ## Canonical descent to the quotient -/

section Descent

variable {G : Type u} [Group G] (R : Subgroup G) [R.Normal] (hR : IsFullyInvariant R)

/-- **Theorem 50.2.**  The endomorphism of `G ⧸ R` induced by an endomorphism of `G`.  Full
invariance is exactly what makes the composite `G → G → G ⧸ R` kill `R`. -/
def descend (f : G →* G) : G ⧸ R →* G ⧸ R :=
  QuotientGroup.map R R f (Subgroup.map_le_iff_le_comap.mp (hR f))

/-- The descended map is computed on representatives by the original map. -/
@[simp] theorem descend_mk (f : G →* G) (x : G) :
    descend R hR f (QuotientGroup.mk' R x) = QuotientGroup.mk' R (f x) := rfl

/-- Equation (50.6): the descended map intertwines the two quotient maps. -/
theorem descend_comp_mk' (f : G →* G) :
    (descend R hR f).comp (QuotientGroup.mk' R) = (QuotientGroup.mk' R).comp f :=
  MonoidHom.ext fun _ => rfl

/-- The intertwining property determines the descended map, because the quotient map is
surjective. -/
theorem eq_descend_of_comp_mk' (f : G →* G) (k : G ⧸ R →* G ⧸ R)
    (hk : k.comp (QuotientGroup.mk' R) = (QuotientGroup.mk' R).comp f) : k = descend R hR f := by
  refine MonoidHom.ext fun q => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R q
  exact DFunLike.congr_fun hk x

include hR in
/-- **Theorem 50.2, in the dossier's existence-and-uniqueness form** (50.5) and (50.6). -/
theorem existsUnique_descend (f : G →* G) :
    ∃! k : G ⧸ R →* G ⧸ R,
      k.comp (QuotientGroup.mk' R) = (QuotientGroup.mk' R).comp f :=
  ⟨descend R hR f, descend_comp_mk' R hR f, fun k hk => eq_descend_of_comp_mk' R hR f k hk⟩

/-- Descent takes the identity to the identity. -/
theorem descend_id : descend R hR (MonoidHom.id G) = MonoidHom.id (G ⧸ R) := by
  refine MonoidHom.ext fun q => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R q
  rfl

/-- Descent takes composites to composites. -/
theorem descend_comp (f g : G →* G) :
    descend R hR (g.comp f) = (descend R hR g).comp (descend R hR f) := by
  refine MonoidHom.ext fun q => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R q
  rfl

/-- **Corollary 50.3.**  An automorphism of `G` descends to an automorphism of `G ⧸ R`: the
descended maps of an automorphism and its inverse are mutually inverse, because their composites
agree with the identity after precomposition with the surjective quotient map. -/
def descendEquiv (e : G ≃* G) : G ⧸ R ≃* G ⧸ R where
  toFun := descend R hR e.toMonoidHom
  invFun := descend R hR e.symm.toMonoidHom
  left_inv := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R q
    show QuotientGroup.mk' R (e.symm (e x)) = QuotientGroup.mk' R x
    rw [MulEquiv.symm_apply_apply]
  right_inv := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R q
    show QuotientGroup.mk' R (e (e.symm x)) = QuotientGroup.mk' R x
    rw [MulEquiv.apply_symm_apply]
  map_mul' := fun a b => map_mul (descend R hR e.toMonoidHom) a b

/-- The descended automorphism is the descended endomorphism of the same map. -/
theorem descendEquiv_toMonoidHom (e : G ≃* G) :
    (descendEquiv R hR e).toMonoidHom = descend R hR e.toMonoidHom :=
  MonoidHom.ext fun _ => rfl

/-- The descended automorphism is computed on representatives by the original automorphism. -/
@[simp] theorem descendEquiv_mk (e : G ≃* G) (x : G) :
    descendEquiv R hR e (QuotientGroup.mk' R x) = QuotientGroup.mk' R (e x) := rfl

end Descent

/-! ## The four radicals descend -/

section RadicalDescent

variable {G : Type u} [Group G] (f : G →* G)

/-- Every endomorphism descends uniquely to the quotient by the finite residual. -/
theorem existsUnique_descend_finiteResidual :
    ∃! k : G ⧸ finiteResidual G →* G ⧸ finiteResidual G,
      k.comp (QuotientGroup.mk' (finiteResidual G))
        = (QuotientGroup.mk' (finiteResidual G)).comp f :=
  existsUnique_descend _ finiteResidual_isFullyInvariant f

/-- Every endomorphism descends uniquely to the quotient by the MF radical. -/
theorem existsUnique_descend_coronaMFResidual :
    ∃! k : G ⧸ coronaMFResidual G →* G ⧸ coronaMFResidual G,
      k.comp (QuotientGroup.mk' (coronaMFResidual G))
        = (QuotientGroup.mk' (coronaMFResidual G)).comp f :=
  existsUnique_descend _ coronaMFResidual_isFullyInvariant f

/-- Every endomorphism descends uniquely to the quotient by the finite-dimensional unitary
residual. -/
theorem existsUnique_descend_fdUnitaryResidual :
    ∃! k : G ⧸ fdUnitaryResidual G →* G ⧸ fdUnitaryResidual G,
      k.comp (QuotientGroup.mk' (fdUnitaryResidual G))
        = (QuotientGroup.mk' (fdUnitaryResidual G)).comp f :=
  existsUnique_descend _ fdUnitaryResidual_isFullyInvariant f

/-- Every endomorphism descends uniquely to the quotient by the all-fields linear residual. -/
theorem existsUnique_descend_linearResidual :
    ∃! k : G ⧸ linearResidual G →* G ⧸ linearResidual G,
      k.comp (QuotientGroup.mk' (linearResidual G))
        = (QuotientGroup.mk' (linearResidual G)).comp f :=
  existsUnique_descend _ linearResidual_isFullyInvariant f

end RadicalDescent

/-! ## Corollary 51.1A: the lamp subgroup is not finitely generated -/

section LampGeneration

variable {K : Type u} [Group K] {X : Type v} [DecidableEq X]

/-- **Corollary 51.1A.**  Over an infinite site set the lamp group of a nontrivial lamp is not
finitely generated: a finite generating set is supported on finitely many sites, and the subgroup
it generates stays inside that support, whereas the one-site lamps exhaust all of `X`.  Combined
with `GroupApproximation.lamp_le_normalClosure_single` this is the dossier's point that a single
element normally generates a subgroup that has no finite generating set at all. -/
theorem lamp_not_fg [Nontrivial K] [Infinite X] : ¬ Group.FG (Lamp K X) := by
  classical
  intro hfg
  obtain ⟨S, hS⟩ := hfg.out
  have hle : Subgroup.closure (↑S : Set (Lamp K X))
      ≤ suppIn (K := K) (S.biUnion Lamp.support) := by
    refine (Subgroup.closure_le _).mpr ?_
    intro f hf
    rw [SetLike.mem_coe, mem_suppIn]
    intro x hx
    by_contra hne
    exact hx (Finset.mem_biUnion.mpr
      ⟨f, Finset.mem_coe.mp hf, Lamp.mem_support.mpr hne⟩)
  obtain ⟨x, hx⟩ : ∃ x : X, x ∉ S.biUnion (Lamp.support (K := K)) := by
    by_contra hcon
    push Not at hcon
    exact absurd (Set.Finite.subset (S.biUnion (Lamp.support (K := K))).finite_toSet
      fun y _ => hcon y) (Set.infinite_univ (α := X))
  obtain ⟨k, hk⟩ := exists_ne (1 : K)
  have hmem : Lamp.single x k ∈ Subgroup.closure (↑S : Set (Lamp K X)) := by
    rw [hS]
    exact Subgroup.mem_top _
  have hval : (Lamp.single x k).toFun x = 1 := mem_suppIn.mp (hle hmem) x hx
  rw [Lamp.single_apply_self] at hval
  exact hk hval

end LampGeneration

/-! ## Theorem 51.1 and Corollary 51.2 -/

section SimpleLampRelation

open SemidirectProduct

variable {K : Type u} [Group K] {G : Type w} [Group G] {X : Type v}
variable [MulAction G X] [DecidableEq X]

omit [DecidableEq X] in
/-- The wreath projection is surjective, split by the canonical inclusion of the acting group. -/
theorem wreathRightHom_surjective :
    Function.Surjective (rightHom : Wreath K G X →* G) :=
  fun g => ⟨inr g, rightHom_inr g⟩

/-- **Theorem 51.1**, equation (51.4).  For a simple lamp group and a transitive site action the
normal closure of a single nontrivial one-site lamp is *exactly* the lamp subgroup.  One inclusion
is `GroupApproximation.lamp_le_normalClosure_single`; the other holds because the lamp subgroup is
the kernel of the wreath projection, hence normal and containing the generator. -/
theorem normalClosure_single_eq_range_inl [IsSimpleGroup K] (x₀ : X)
    (htrans : ∀ x : X, ∃ g : G, g • x₀ = x) {k₀ : K} (hk₀ : k₀ ≠ 1) :
    Subgroup.normalClosure {(inl (Lamp.single x₀ k₀) : Wreath K G X)}
      = (inl : Lamp K X →* Wreath K G X).range := by
  haveI : ((inl : Lamp K X →* Wreath K G X).range).Normal := by
    rw [← ker_rightHom_eq_lampRange]
    infer_instance
  refine le_antisymm ?_ ?_
  · apply Subgroup.normalClosure_le_normal
    rintro y (rfl : y = _)
    exact ⟨Lamp.single x₀ k₀, rfl⟩
  · rintro _ ⟨f, rfl⟩
    exact lamp_le_normalClosure_single x₀ htrans hk₀ f

/-- **Corollary 51.2**, equation (51.8).  Adding the single relation `r = 1` to the wreath product
over a simple lamp collapses it onto the acting group.  The quotient map is split by
`GroupApproximation.rightHom_comp_inr`, so this is a split epimorphism with a nontrivial kernel
that no finite, compact, finite-dimensional or corona target can see. -/
noncomputable def wreathQuotientSingleEquiv [IsSimpleGroup K] (x₀ : X)
    (htrans : ∀ x : X, ∃ g : G, g • x₀ = x) {k₀ : K} (hk₀ : k₀ ≠ 1) :
    (Wreath K G X ⧸ Subgroup.normalClosure {(inl (Lamp.single x₀ k₀) : Wreath K G X)}) ≃* G :=
  (QuotientGroup.quotientMulEquivOfEq
      ((normalClosure_single_eq_range_inl x₀ htrans hk₀).trans
        ker_rightHom_eq_lampRange.symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ wreathRightHom_surjective)

/-- The collapse of Corollary 51.2 is the wreath projection itself. -/
@[simp] theorem wreathQuotientSingleEquiv_mk [IsSimpleGroup K] (x₀ : X)
    (htrans : ∀ x : X, ∃ g : G, g • x₀ = x) {k₀ : K} (hk₀ : k₀ ≠ 1) (w : Wreath K G X) :
    wreathQuotientSingleEquiv x₀ htrans hk₀
        (QuotientGroup.mk' (Subgroup.normalClosure
          {(inl (Lamp.single x₀ k₀) : Wreath K G X)}) w) = rightHom w := rfl

/-- **Corollary 51.1A in the wreath product.**  The single relation of Corollary 51.2 normally
generates a subgroup which, over an infinite site set, is not finitely generated. -/
theorem normalClosure_single_not_fg [IsSimpleGroup K] [Infinite X] (x₀ : X)
    (htrans : ∀ x : X, ∃ g : G, g • x₀ = x) {k₀ : K} (hk₀ : k₀ ≠ 1) :
    ¬ Group.FG ↥(Subgroup.normalClosure {(inl (Lamp.single x₀ k₀) : Wreath K G X)}) := by
  intro hfg
  rw [normalClosure_single_eq_range_inl x₀ htrans hk₀] at hfg
  haveI := hfg
  have e : Lamp K X ≃* (inl : Lamp K X →* Wreath K G X).range :=
    MonoidHom.ofInjective inl_injective
  exact lamp_not_fg (Group.fg_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)

end SimpleLampRelation

/-! ## Lemma 52.1: alternating groups of distinct degrees are not isomorphic -/

/-- **Lemma 52.1**, size half.  Alternating groups of distinct degrees have distinct orders, so
they are pairwise nonisomorphic.  Simplicity is Mathlib's `alternatingGroup.isSimpleGroup`; this
statement is what makes the alternating lamps of Section 52.3 an infinite family of genuinely
different hidden kernels. -/
theorem alternatingGroup_fin_eq_of_mulEquiv {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (e : alternatingGroup (Fin m) ≃* alternatingGroup (Fin n)) : m = n := by
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have hcard : Nat.card (alternatingGroup (Fin m)) = Nat.card (alternatingGroup (Fin n)) :=
    Nat.card_congr e.toEquiv
  have h2 : Nat.card (Equiv.Perm (Fin m)) = Nat.card (Equiv.Perm (Fin n)) := by
    rw [← two_mul_nat_card_alternatingGroup, ← two_mul_nat_card_alternatingGroup, hcard]
  have hfac : Nat.factorial m = Nat.factorial n := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] using h2
  rcases lt_trichotomy m n with h | h | h
  · have := (Nat.factorial_lt (show 0 < m by omega)).mpr h
    omega
  · exact h
  · have := (Nat.factorial_lt (show 0 < n by omega)).mpr h
    omega

end RadicalFunctoriality

end GroupApproximation
