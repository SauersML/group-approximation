import GroupApproximation.Sofic.LEFSofic
import GroupApproximation.Sofic.LocallyFiniteMF
import GroupApproximation.Sofic.SoficInvariantFiniteKernel

/-!
# The telescope core is locally residually finite

Theorem 4.1 of `notes/LITERAL_GROUP_IS_SOFIC_2026-08-14.md`: the kernel
`E_T = N_E ⋊ T` of the stable-letter exponent `E → ℤ` has every finitely
generated subgroup residually finite, hence is LEF, hence sofic.

## What replaces the finite lamp subgroup

The soficity proof of the finitely generated witness `W` runs on
`isLEF_semidirectProduct_of_invariant_finite`
(`Sofic/LEFMarkedCompression.lean`): a finite window of `ClLamp(X) ⋊ T` sits
inside a **finite** level-invariant lamp subgroup, and a finite-kernel
semidirect product with residually finite quotient is residually finite
because the action of the quotient has finite range.

That step is unavailable for `E`.  The lamp kernel `N_E = ∗_{⟨w⟩} ClLamp(8)`
contains nonabelian free subgroups, so no finite invariant subgroup contains a
window meeting two blocks.  What survives is the observation of §1 of the
soficity artifact: `N_E` is *locally finite in blocks* even though it is not
locally finite in elements.  Finitely many blocks generate a finitely
generated invariant sub-amalgam `M_J`, which is residually finite, and the
level `Γ_n` still acts on `M_J` through a finite permutation group of the
`8|J|` sites.

So the whole file is the same argument with "finite invariant kernel" weakened
to "**residually finite** invariant kernel whose restricted action has finite
range".  The finite-range hypothesis, which was free in the `W` proof (an
automorphism group of a finite group is finite), is now supplied by
`finite_range_restrictAut_of_finite_generating`: the kernel window is generated
by a finite invariant set — the union of the finitely many blocks, each of
order `512` — and the action factors through the self-maps of that set.

## "Locally" is load-bearing

`E_T` is LEF but is **not** residually finite (Theorem 4.1a of the artifact:
in any finite quotient the image of `ℤ[1/2]³` is `2`-divisible and finite,
hence of odd order, so `φ(T) = φ(B)`, all same-level lamps are identified and
`w` dies).  Nothing in this file states or uses residual finiteness of the
telescope core itself; every conclusion about it is the local one.  A directed
union of residually finite groups need not be residually finite, and this one
demonstrably is not.

## Quantifier order

Remark 4.2 of the artifact: the pair `(n, J)` is allowed to depend on the
window arbitrarily, and it does.  Nothing here asks for a bound on `n`, on
`|J|`, or on the sizes of the finite models.  That is exactly the quantifier
order of `isLEF_of_forall_finset_residuallyFinite`.

## What is used, and what is deliberately not

Used: exhaustion of LEF by residually finite subgroups
(`isLEF_of_locallyResiduallyFinite`), the kernel-of-the-site-action trick
(`residuallyFinite_semidirectProduct_of_finite_range`), and residual
finiteness permanence along injections and finite-index overgroups.

Not used anywhere: the false permanence direction "amenable kernel with sofic
quotient", which `notes/TRUE_LITERAL_NONMF_MARK_IS_CE_VISIBLE.md` §3 warns
against; no wreath-product permanence theorem; and no hypothesis that the
`V`-action on the infinite site set be modelled by permutations.  The only
action ever approximated is that of a single level on a finite block set, and
that action is a genuine finite permutation action by construction.

The `ℤ`-extension `E = E_T ⋊ ⟨τ⟩` is not treated here; it is the
Elek--Szabó step, formalized as `isSofic_int_semidirectProduct`.
-/

namespace GroupApproximation
namespace LiteralTelescopeCoreLEF

universe u v

/-! ## Telescope levels

The telescope `T = ⋃_{n ≥ 0} Γ_n` enters only through two facts: the levels
increase, and every element lies in one.  A finite window therefore lies in a
single level, with the level depending on the window arbitrarily.
-/

section Levels

variable {G : Type u} [Group G]

/-- A finite subset of an increasing exhausting chain of subgroups lies in a
single member of the chain.  This is input (S1) of the soficity artifact in
the only form the argument consumes: `T` is the increasing union of the
telescope levels, so the finitely many telescope coordinates of a window share
a level. -/
theorem exists_common_level (lev : ℕ → Subgroup G) (hmono : Monotone lev)
    (hexhaust : ∀ g : G, ∃ n, g ∈ lev n) (s : Finset G) :
    ∃ n : ℕ, ∀ g ∈ s, g ∈ lev n := by
  classical
  choose f hf using hexhaust
  exact ⟨s.sup f, fun g hg ↦ hmono (Finset.le_sup hg) (hf g)⟩

end Levels

/-! ## Actions with finite range on a finitely generated invariant kernel

`residuallyFinite_semidirectProduct_of_finite_range` needs the acting group to
have finite range in `MulAut` of the kernel.  In the `W` proof the kernel was
finite, so this was automatic.  Here the kernel is infinite and the finiteness
comes from the geometry instead: the level permutes a finite generating
configuration of the kernel — the sites carried by finitely many blocks — and
an automorphism of a group is determined by its values on a generating set.
-/

section FiniteRange

variable {N : Type} {G : Type u} [Group N] [Group G]

/-- The restriction of the `H`-action to a finite `H`-invariant generating set
`S` of the kernel, as a map into the self-maps of `S`.  For the literal group
`S` is the set of Clifford generators `c_x` carried by the blocks of `J`, and
`H` is a telescope level permuting them. -/
def generatorAction (φ : G →* MulAut N) (H : Subgroup G) {S : Set N}
    (hstab : ∀ h ∈ H, ∀ x ∈ S, φ h x ∈ S) (h : H) : S → S :=
  fun x ↦ ⟨φ (h : G) (x : N), hstab (h : G) h.2 (x : N) x.2⟩

@[simp] theorem generatorAction_val (φ : G →* MulAut N) (H : Subgroup G) {S : Set N}
    (hstab : ∀ h ∈ H, ∀ x ∈ S, φ h x ∈ S) (h : H) (x : S) :
    (generatorAction φ H hstab h x).1 = φ (h : G) (x : N) := rfl

/-- Two elements of the acting group that agree on a generating set of the
invariant kernel induce the same automorphism of it. -/
theorem restrictAut_eq_of_eqOn_generators (φ : G →* MulAut N) (K : Subgroup N)
    (H : Subgroup G) (hinv : ∀ h ∈ H, ∀ n ∈ K, φ h n ∈ K)
    {S : Set N} (hgen : Subgroup.closure S = K) {h h' : H}
    (hS : ∀ x ∈ S, φ (h : G) x = φ (h' : G) x) :
    restrictAut φ K H hinv h = restrictAut φ K H hinv h' := by
  have hK : ∀ n ∈ K, φ (h : G) n = φ (h' : G) n := by
    intro n hn
    rw [← hgen] at hn
    induction hn using Subgroup.closure_induction with
    | mem x hx => exact hS x hx
    | one => rw [map_one, map_one]
    | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]
    | inv a _ ha => rw [map_inv, map_inv, ha]
  apply MulEquiv.ext
  intro k
  apply Subtype.ext
  show φ (h : G) (k : N) = φ (h' : G) (k : N)
  exact hK (k : N) k.2

/-- **The finite-range criterion.**  If the invariant kernel `K` is generated
by a finite `H`-invariant set, the restricted action of `H` on `K` has finite
range: it factors injectively through the self-maps of that finite set.

This is what replaces "the kernel is finite" in the witness argument, and it
is the only place the order of a block (`512`, so finite) is used. -/
theorem finite_range_restrictAut_of_finite_generating (φ : G →* MulAut N)
    (K : Subgroup N) (H : Subgroup G) (hinv : ∀ h ∈ H, ∀ n ∈ K, φ h n ∈ K)
    {S : Set N} (hfin : S.Finite) (hgen : Subgroup.closure S = K)
    (hstab : ∀ h ∈ H, ∀ x ∈ S, φ h x ∈ S) :
    Finite (restrictAut φ K H hinv).range := by
  classical
  haveI : Finite S := hfin.to_subtype
  have hagree : ∀ h h' : H,
      generatorAction φ H hstab h = generatorAction φ H hstab h' →
        restrictAut φ K H hinv h = restrictAut φ K H hinv h' := by
    intro h h' hFF
    refine restrictAut_eq_of_eqOn_generators φ K H hinv hgen ?_
    intro x hx
    exact congrArg (fun f : S → S ↦ (f ⟨x, hx⟩).1) hFF
  refine Finite.of_injective
    (fun y : (restrictAut φ K H hinv).range ↦
      generatorAction φ H hstab
        (Classical.choose (MonoidHom.mem_range.mp y.2))) ?_
  intro y z hyz
  have hy := Classical.choose_spec (MonoidHom.mem_range.mp y.2)
  have hz := Classical.choose_spec (MonoidHom.mem_range.mp z.2)
  exact Subtype.ext (hy.symm.trans ((hagree _ _ hyz).trans hz))

end FiniteRange

/-! ## Windows

The exact analogue of `isLEF_semidirectProduct_of_invariant_finite`, with the
finiteness of the invariant kernel weakened to residual finiteness plus finite
range of the restricted action.  The enclosing subgroup pair still spans a copy
of `K ⋊ H` inside `N ⋊[φ] G` — `inclSemidirect` — and that copy is now
residually finite by the site-action kernel trick rather than by finiteness.
-/

section Windows

variable {N : Type} {G : Type u} [Group N] [Group G]

/-- A window sits inside the copy of `K ⋊ H` spanned by an enclosing pair. -/
theorem mem_inclSemidirect_range (φ : G →* MulAut N) (K : Subgroup N)
    (H : Subgroup G) (hinv : ∀ h ∈ H, ∀ n ∈ K, φ h n ∈ K)
    {g : N ⋊[φ] G} (hleft : g.left ∈ K) (hright : g.right ∈ H) :
    g ∈ (inclSemidirect φ K H hinv).range :=
  ⟨⟨⟨g.left, hleft⟩, ⟨g.right, hright⟩⟩, by rw [inclSemidirect_apply]⟩

/-- **Lemma 3.1 in Lean form.**  `M_J ⋊ Γ_n` is residually finite: the action
of the level has finite range, so its kernel `Λ` has finite index and the
direct product `M_J × Λ` of two residually finite groups sits inside with
finite index.  Splitness is used and is free here, since the pair spans an
honest semidirect product inside `N ⋊[φ] G`.

No claim is made for a non-split extension; finite-by-residually-finite
extensions are not residually finite in general (Deligne). -/
theorem residuallyFinite_inclSemidirect_range (φ : G →* MulAut N)
    (K : Subgroup N) (H : Subgroup G) (hinv : ∀ h ∈ H, ∀ n ∈ K, φ h n ∈ K)
    (hK : Group.ResiduallyFinite K) (hH : Group.ResiduallyFinite H)
    (hrange : Finite (restrictAut φ K H hinv).range) :
    Group.ResiduallyFinite (inclSemidirect φ K H hinv).range := by
  letI := hK
  letI := hH
  letI := hrange
  haveI : Group.ResiduallyFinite (K ⋊[restrictAut φ K H hinv] H) :=
    residuallyFinite_semidirectProduct_of_finite_range _
  exact residuallyFinite_of_mulEquiv
    (MonoidHom.ofInjective (inclSemidirect_injective φ K H hinv)).symm

/-- **Theorem 4.1, general form: local residual finiteness from windows.**
If every finite subset of `N ⋊[φ] G` is enclosed by a residually finite
invariant kernel window together with a residually finite subgroup of the
acting group whose restricted action has finite range, then *every finitely
generated subgroup* of `N ⋊[φ] G` is residually finite.

The conclusion is deliberately the local one.  It is not, and must not be
strengthened to, residual finiteness of `N ⋊[φ] G`: for the literal telescope
core that statement is false. -/
theorem locallyResiduallyFinite_of_windows (φ : G →* MulAut N)
    (hlocal : ∀ F : Finset (N ⋊[φ] G), ∃ (K : Subgroup N) (H : Subgroup G)
      (hinv : ∀ h ∈ H, ∀ n ∈ K, φ h n ∈ K),
      Group.ResiduallyFinite K ∧ Group.ResiduallyFinite H ∧
        Finite (restrictAut φ K H hinv).range ∧
        ∀ g ∈ F, g.left ∈ K ∧ g.right ∈ H) :
    ∀ Q : Subgroup (N ⋊[φ] G), Q.FG → Group.ResiduallyFinite Q := by
  intro Q hQ
  obtain ⟨F, hF⟩ := hQ
  obtain ⟨K, H, hinv, hK, hH, hrange, hmem⟩ := hlocal F
  have hle : Q ≤ (inclSemidirect φ K H hinv).range := by
    rw [← hF, Subgroup.closure_le]
    intro g hg
    exact mem_inclSemidirect_range φ K H hinv
      (hmem g (Finset.mem_coe.mp hg)).1 (hmem g (Finset.mem_coe.mp hg)).2
  letI := residuallyFinite_inclSemidirect_range φ K H hinv hK hH hrange
  exact residuallyFinite_of_injective (Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)

/-- The LEF form of the window theorem: the block-amalgam replacement for
`isLEF_semidirectProduct_of_invariant_finite`. -/
theorem isLEF_of_windows (φ : G →* MulAut N)
    (hlocal : ∀ F : Finset (N ⋊[φ] G), ∃ (K : Subgroup N) (H : Subgroup G)
      (hinv : ∀ h ∈ H, ∀ n ∈ K, φ h n ∈ K),
      Group.ResiduallyFinite K ∧ Group.ResiduallyFinite H ∧
        Finite (restrictAut φ K H hinv).range ∧
        ∀ g ∈ F, g.left ∈ K ∧ g.right ∈ H) :
    IsLEF (N ⋊[φ] G) :=
  isLEF_of_locallyResiduallyFinite (locallyResiduallyFinite_of_windows φ hlocal)

end Windows

/-! ## Blocks

Input (S2): the lamp kernel is generated by its blocks, each of them finite,
and the acting group permutes the block set.  Input (S3): every level has
finite orbits on the block set.

Nothing here needs the blocks to be free factors, or amalgamated, or of any
particular order; the amalgam normal form enters only through the residual
finiteness of `blockSpan`, which is a hypothesis.  As the robustness remark of
§6a records, block orbits reduce to site orbits because a block is determined
by its sites, so the `V`-set isomorphism `I ≅ X` is a convenience rather than
a load-bearing step.
-/

section Blocks

variable {N : Type} {G : Type u} {I : Type v} [Group N] [Group G]

/-- `M_J`: the subgroup generated by a set of blocks. -/
def blockSpan (P : I → Subgroup N) (J : Set I) : Subgroup N :=
  Subgroup.closure (⋃ i ∈ J, (P i : Set N))

theorem blockSpan_mono (P : I → Subgroup N) {J J' : Set I} (h : J ⊆ J') :
    blockSpan P J ≤ blockSpan P J' := by
  show Subgroup.closure (⋃ i ∈ J, (P i : Set N))
      ≤ Subgroup.closure (⋃ i ∈ J', (P i : Set N))
  refine Subgroup.closure_mono ?_
  intro x hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
  exact Set.mem_biUnion (h hi) hxi

theorem le_blockSpan (P : I → Subgroup N) {J : Set I} {i : I} (hi : i ∈ J) :
    P i ≤ blockSpan P J := fun _ hx ↦
  Subgroup.subset_closure (Set.mem_biUnion hi hx)

theorem blockSpan_le (P : I → Subgroup N) {J : Set I} {L : Subgroup N}
    (h : ∀ i ∈ J, P i ≤ L) : blockSpan P J ≤ L := by
  show Subgroup.closure (⋃ i ∈ J, (P i : Set N)) ≤ L
  rw [Subgroup.closure_le]
  intro x hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
  exact h i hi hxi

/-- The blocks generate the kernel exactly when the span over all of them is
everything.  This is the shape in which the amalgam lane states (S2). -/
theorem blockSpan_univ (P : I → Subgroup N) :
    blockSpan P Set.univ = Subgroup.closure (⋃ i, (P i : Set N)) := by
  show Subgroup.closure (⋃ i ∈ (Set.univ : Set I), (P i : Set N))
      = Subgroup.closure (⋃ i, (P i : Set N))
  congr 1
  ext x
  simp

/-- **A finitely supported span of finite blocks is finitely generated**: it
is the closure of the finite set of all elements of the blocks in play.

This is the bridge to a *local* residual finiteness statement about the lamp
kernel.  `TelescopeCoreData.subAmalgam_residuallyFinite` asks for residual
finiteness of each `M_J`; if what the amalgam lane delivers instead is that
every finitely generated subgroup of the lamp kernel is residually finite,
this lemma supplies the missing finite-generation hypothesis and the two
forms become interchangeable. -/
theorem blockSpan_fg (P : I → Subgroup N) {J : Set I} (hJ : J.Finite)
    (hPfin : ∀ i : I, (P i : Set N).Finite) : (blockSpan P J).FG := by
  have hSfin : (⋃ i ∈ J, (P i : Set N)).Finite :=
    hJ.biUnion fun i _ ↦ hPfin i
  obtain ⟨t, ht⟩ := hSfin.exists_finset_coe
  refine ⟨t, ?_⟩
  show Subgroup.closure (t : Set N)
      = Subgroup.closure (⋃ i ∈ J, (P i : Set N))
  rw [ht]

/-- Every element of the kernel is carried by finitely many blocks.  This is
the step that makes `J₀` finite in the proof of Theorem 4.1: an element of
`N_E` is a word in finitely many blocks. -/
theorem exists_finite_blockSpan (P : I → Subgroup N)
    (hspan : blockSpan P Set.univ = ⊤) (n : N) :
    ∃ J : Set I, J.Finite ∧ n ∈ blockSpan P J := by
  have hn : n ∈ Subgroup.closure (⋃ i ∈ (Set.univ : Set I), (P i : Set N)) := by
    show n ∈ blockSpan P Set.univ
    rw [hspan]
    exact Subgroup.mem_top n
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, -, hxi⟩ := Set.mem_iUnion₂.mp hx
      exact ⟨{i}, Set.finite_singleton i,
        le_blockSpan P (Set.mem_singleton_iff.mpr rfl) hxi⟩
  | one => exact ⟨∅, Set.finite_empty, one_mem _⟩
  | mul a b _ _ ha hb =>
      obtain ⟨Ja, hJa, hain⟩ := ha
      obtain ⟨Jb, hJb, hbin⟩ := hb
      exact ⟨Ja ∪ Jb, hJa.union hJb,
        mul_mem (blockSpan_mono P Set.subset_union_left hain)
          (blockSpan_mono P Set.subset_union_right hbin)⟩
  | inv a _ ha =>
      obtain ⟨J, hJ, hain⟩ := ha
      exact ⟨J, hJ, inv_mem hain⟩

/-- `J = Γ_n · J₀`: the saturation of a block set under a subgroup of the
acting group. -/
def blockOrbitClosure (σ : G →* Equiv.Perm I) (H : Subgroup G) (J : Set I) :
    Set I :=
  ⋃ i ∈ J, Set.range fun h : H ↦ σ (h : G) i

theorem subset_blockOrbitClosure (σ : G →* Equiv.Perm I) (H : Subgroup G)
    (J : Set I) : J ⊆ blockOrbitClosure σ H J := by
  intro i hi
  refine Set.mem_biUnion hi ⟨1, ?_⟩
  show σ ((1 : H) : G) i = i
  simp

/-- The saturation of a finite block set by a subgroup with finite block
orbits is finite.  This is input (S3), and it is the only place the geometry
of the telescope enters. -/
theorem blockOrbitClosure_finite (σ : G →* Equiv.Perm I) (H : Subgroup G)
    {J : Set I} (hJ : J.Finite)
    (horbit : ∀ i : I, (Set.range fun h : H ↦ σ (h : G) i).Finite) :
    (blockOrbitClosure σ H J).Finite :=
  hJ.biUnion fun i _ ↦ horbit i

theorem blockOrbitClosure_invariant (σ : G →* Equiv.Perm I) (H : Subgroup G)
    (J : Set I) (g : H) {i : I} (hi : i ∈ blockOrbitClosure σ H J) :
    σ (g : G) i ∈ blockOrbitClosure σ H J := by
  obtain ⟨j, hj, h, hhi⟩ := Set.mem_iUnion₂.mp hi
  refine Set.mem_biUnion hj ⟨g * h, ?_⟩
  show σ ((g * h : H) : G) j = σ (g : G) i
  -- `hhi` is a beta-redex, so it cannot be used as a rewrite pattern; apply
  -- the outer permutation to it instead.
  rw [Subgroup.coe_mul, map_mul, Equiv.Perm.mul_apply]
  exact congrArg (σ (g : G)) hhi

theorem blockOrbitClosure_invariant' (σ : G →* Equiv.Perm I) (H : Subgroup G)
    (J : Set I) {g : G} (hg : g ∈ H) {i : I}
    (hi : i ∈ blockOrbitClosure σ H J) :
    σ g i ∈ blockOrbitClosure σ H J :=
  blockOrbitClosure_invariant σ H J ⟨g, hg⟩ hi

/-- **Finite orbits transport along a homomorphism into the acting group.**

The block geometry of the literal group states its level orbits for the level
subgroups sitting inside the *vertical* group `V = T ⋊ ⟨τ⟩`, since that is
where `MappingTelescopeFiniteOrbits` puts them; the telescope core needs them
for the level subgroups sitting inside the *telescope* `T`.  The two index the
same set of permutations, because the inclusion `T ↪ V` carries one level
subgroup onto the other, so the smaller range is a subset of the finite one.

Instantiate with `f := SemidirectProduct.inl`, `τ := MulAction.toPermHom`, and
`S := (MappingTelescope.level α hα n).range`, whose image under `inl` is
`MappingTelescopeFiniteOrbits.verticalLevel α hα n`. -/
theorem finite_orbit_of_map {A B X : Type*} [Group A] [Group B]
    (f : A →* B) (τ : B →* Equiv.Perm X) (S : Subgroup A) (x : X)
    (h : (Set.range fun b : S.map f ↦ τ (b : B) x).Finite) :
    (Set.range fun a : S ↦ τ (f (a : A)) x).Finite := by
  refine h.subset ?_
  rintro _ ⟨a, rfl⟩
  exact ⟨⟨f (a : A), Subgroup.mem_map_of_mem f a.2⟩, rfl⟩

/-- **Block equivariance from generator equivariance.**

`TelescopeCoreData.block_equivariant` asks that the acting group carry each
block subgroup onto the block subgroup at the moved index.  For the literal
group that is not proved directly: what is proved is the *site-level*
statement, that the lamp at a site conjugates to the lamp at the moved site,
together with the fact that the block index moves by the induced permutation.
This lemma is the reduction, and it is the whole of it — a closure induction is
not needed, since a generating set suffices for containment.

`act` is a plain function rather than a `MulAction`, so a caller can restrict an
action along an inclusion (for the literal group, along `T ↪ V`) at the call
site without first repackaging it. -/
theorem block_equivariant_of_generators {Site : Type*}
    (φ : G →* MulAut N) (σ : G →* Equiv.Perm I) (P : I → Subgroup N)
    (c : Site → N) (blockOf : Site → I) (act : G → Site → Site)
    (hP : ∀ i : I, P i = Subgroup.closure (c '' {s : Site | blockOf s = i}))
    (hc : ∀ (g : G) (s : Site), φ g (c s) = c (act g s))
    (hblock : ∀ (g : G) (s : Site), blockOf (act g s) = σ g (blockOf s))
    (g : G) (i : I) : ∀ x ∈ P i, φ g x ∈ P (σ g i) := by
  intro x hx
  have hmap : P i ≤ Subgroup.comap (φ g).toMonoidHom (P (σ g i)) := by
    rw [hP i, Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    show c s ∈ Subgroup.comap (φ g).toMonoidHom (P (σ g i))
    rw [Subgroup.mem_comap]
    show φ g (c s) ∈ P (σ g i)
    rw [hc g s, hP (σ g i)]
    refine Subgroup.subset_closure ⟨act g s, ?_, rfl⟩
    show blockOf (act g s) = σ g i
    rw [hblock g s, hs]
  exact Subgroup.mem_comap.mp (hmap hx)

/-- **The window of Theorem 4.1.**  Given a finite subset of `N ⋊[φ] G`,
there is a level `n` and a finite `Γ_n`-invariant set `J` of blocks whose span
contains every kernel coordinate of the subset, while every acting coordinate
lies in the level.

The pair `(n, J)` depends on the window arbitrarily: `n` is a level containing
the finitely many acting coordinates and `J = Γ_n · J₀` grows with both.  This
is Remark 4.2. -/
theorem exists_invariant_block_window (φ : G →* MulAut N) (P : I → Subgroup N)
    (σ : G →* Equiv.Perm I) (lev : ℕ → Subgroup G)
    (hspan : blockSpan P Set.univ = ⊤)
    (hlevMono : Monotone lev) (hlevExhausts : ∀ g : G, ∃ n, g ∈ lev n)
    (hlevOrbit : ∀ (n : ℕ) (i : I),
      (Set.range fun h : lev n ↦ σ (h : G) i).Finite)
    (F : Finset (N ⋊[φ] G)) :
    ∃ (n : ℕ) (J : Set I), J.Finite ∧
      (∀ g ∈ lev n, ∀ i ∈ J, σ g i ∈ J) ∧
      ∀ g ∈ F, g.left ∈ blockSpan P J ∧ g.right ∈ lev n := by
  classical
  obtain ⟨n, hn⟩ := exists_common_level lev hlevMono hlevExhausts
    (F.image SemidirectProduct.right)
  choose Jof hJofFinite hJofMem using exists_finite_blockSpan P hspan
  refine ⟨n, blockOrbitClosure σ (lev n)
    (⋃ g ∈ (F : Set (N ⋊[φ] G)), Jof g.left), ?_, ?_, ?_⟩
  · exact blockOrbitClosure_finite σ (lev n)
      (F.finite_toSet.biUnion fun g _ ↦ hJofFinite g.left) (hlevOrbit n)
  · intro g hg i hi
    exact blockOrbitClosure_invariant' σ (lev n) _ hg hi
  · intro g hg
    refine ⟨?_, hn g.right (Finset.mem_image_of_mem _ hg)⟩
    refine blockSpan_mono P ?_ (hJofMem g.left)
    exact Set.Subset.trans
      (fun i hi ↦ Set.mem_biUnion (Finset.mem_coe.mpr hg) hi)
      (subset_blockOrbitClosure σ (lev n) _)

/-- **Theorem 4.1 (abstract form).**  A semidirect product whose kernel is
generated by finite blocks permuted by the acting group, and whose acting
group is exhausted by residually finite levels with finite block orbits, is
*locally* residually finite as soon as the finitely supported block spans are
residually finite.

The two residual-finiteness hypotheses are the imported facts: `hblockRF` is
statement (M) of the soficity-tower design note — residual finiteness of the
finite sub-amalgams `M_J` — and `hlevRF` is residual finiteness of the
telescope levels.  Everything else is structural.

Again: the conclusion is local and cannot be improved.  `E_T` itself is not
residually finite. -/
theorem locallyResiduallyFinite_blockTelescope (φ : G →* MulAut N)
    (P : I → Subgroup N) (σ : G →* Equiv.Perm I) (lev : ℕ → Subgroup G)
    (hequiv : ∀ (g : G) (i : I), ∀ x ∈ P i, φ g x ∈ P (σ g i))
    (hspan : blockSpan P Set.univ = ⊤)
    (hblockFinite : ∀ i : I, (P i : Set N).Finite)
    (hlevMono : Monotone lev) (hlevExhausts : ∀ g : G, ∃ n, g ∈ lev n)
    (hlevOrbit : ∀ (n : ℕ) (i : I),
      (Set.range fun h : lev n ↦ σ (h : G) i).Finite)
    (hblockRF : ∀ J : Set I, J.Finite →
      Group.ResiduallyFinite (blockSpan P J))
    (hlevRF : ∀ n : ℕ, Group.ResiduallyFinite (lev n)) :
    ∀ Q : Subgroup (N ⋊[φ] G), Q.FG → Group.ResiduallyFinite Q := by
  classical
  refine locallyResiduallyFinite_of_windows φ ?_
  intro F
  obtain ⟨n, J, hJfin, hJinv, hmem⟩ :=
    exists_invariant_block_window φ P σ lev hspan hlevMono hlevExhausts
      hlevOrbit F
  have hinv : ∀ h ∈ lev n, ∀ x ∈ blockSpan P J, φ h x ∈ blockSpan P J := by
    intro h hh x hx
    have hmap : blockSpan P J ≤
        Subgroup.comap (φ h).toMonoidHom (blockSpan P J) := by
      refine blockSpan_le P ?_
      intro i hi y hy
      rw [Subgroup.mem_comap]
      exact le_blockSpan P (hJinv h hh i hi) (hequiv h i y hy)
    exact Subgroup.mem_comap.mp (hmap hx)
  have hSfin : (⋃ i ∈ J, (P i : Set N)).Finite :=
    hJfin.biUnion fun i _ ↦ hblockFinite i
  refine ⟨blockSpan P J, lev n, hinv, hblockRF J hJfin, hlevRF n, ?_, hmem⟩
  refine finite_range_restrictAut_of_finite_generating φ _ _ hinv hSfin rfl ?_
  intro h hh x hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
  exact Set.mem_biUnion (hJinv h hh i hi) (hequiv h i x hxi)

end Blocks

/-! ## The literal telescope core

`E_T = N_E ⋊ T`, the kernel of the stable-letter exponent `E → ℤ`.

The inputs of Theorem 4.1 are bundled as a structure so that the instantiation
against the split (S1), the block geometry (S2), the level orbits (S3) and the
sub-amalgam residual finiteness (M) is a single object to build.

**No field is a literature input.**  The two that were expected to carry trust
surface do not:

* `subAmalgam_residuallyFinite` — statement (M).  The amalgam side proves the
  stronger, hypothesis-free statement that *every finitely generated* subgroup
  of the lamp kernel is residually finite; `blockSpan_fg` supplies the missing
  finite-generation hypothesis, so the field is dischargeable from it.  It
  needs neither the amalgam normal form nor Karrass--Pietrowski--Solitar.
* `level_residuallyFinite` — residual finiteness of the telescope levels.  The
  telescope of the literal chain is built over the *matrix* base, so a level is
  the range of an injective level map out of it and residual finiteness follows
  from that of the matrix base by transport along the induced isomorphism.  No
  identification of the presented base with the matrix group is used, and that
  identification is in any case proved in the repository, so the `B ≅ Γ̄`
  caveat recorded in the soficity artifact's audit header does not apply here.

The fields are hypotheses for modularity, not because they are unproved.

What the instantiation does still rest on is two facts about the orbital graph
--- that distinct sites of one block are adjacent, and that no site is adjacent
to itself --- since the identification of the lamp kernel with the block
amalgam is stated relative to a block-Clifford presentation, and that
presentation is discharged only modulo those two.  They are orbit computations,
not literature inputs and not analysis.
-/

section Core

/-- The inputs of Theorem 4.1 for the literal telescope core.

`Lamp` is the lamp kernel `N_E`, `Tel` is the telescope `T`, and `Block` is
the block set of the marked orbital graph.  `level` is the telescope filtration
`Γ_n`, increasing and exhausting; `block` is the family `P_i` of block
subgroups, each finite of order `512`; `blockAction` is the permutation action
of the telescope on the block set.

**Design invariant --- do not strengthen a field past it.**  Every finiteness
or residual-finiteness field below is indexed either by a single level `n`
(`level_finite_orbits`, `level_residuallyFinite`) or by a finite block set `J`
(`subAmalgam_residuallyFinite`), and `block_finite` is per-block.  No field
asserts finiteness quantified over all of `Tel`, and no field mentions the
vertical group `V = T ⋊ ⟨τ⟩` at all.  That is not tidiness; it is what makes
the bundle satisfiable.

In every finite quotient of `V` all telescope levels have one image, so `B` is
not separable in `V` and the site set collapses in every `V`-equivariant finite
model.  The obvious "simplifications" of this structure are exactly the ones
that walk into that collapse and are false: replacing `level_finite_orbits` by
finiteness of the `Tel`-orbit of a block, or asking the restricted action of
all of `Tel` on `M_J` to have finite range.  What is safe is what is written,
because the collapse is a `T`-phenomenon invisible inside a single level ---
`B` has finite index in `Γ_n`, so it *is* separable there, and the block models
live in one `Γ_n` by construction.

The finite quotients this file actually produces are quotients of a *level* by
the finite-index kernel of its action on `sites(J)`.  They are never finite
quotients of `V`, of `T`, or of the core. -/
structure TelescopeCoreData (Lamp : Type) (Tel : Type u) (Block : Type v)
    [Group Lamp] [Group Tel] where
  /-- (S1) The action of the telescope on the lamp kernel. -/
  action : Tel →* MulAut Lamp
  /-- (S2) The block subgroups of the lamp kernel. -/
  block : Block → Subgroup Lamp
  /-- (S2) The permutation action of the telescope on the block set. -/
  blockAction : Tel →* Equiv.Perm Block
  /-- (S1) The telescope levels `Γ_n`. -/
  level : ℕ → Subgroup Tel
  /-- The block family is equivariant for the two actions. -/
  block_equivariant : ∀ (g : Tel) (i : Block), ∀ x ∈ block i,
    action g x ∈ block (blockAction g i)
  /-- (S2) The blocks generate the lamp kernel. -/
  block_span : blockSpan block Set.univ = ⊤
  /-- (S2) Each block is finite --- for the literal group, of order `512`. -/
  block_finite : ∀ i : Block, (block i : Set Lamp).Finite
  /-- (S1) The levels increase. -/
  level_mono : Monotone level
  /-- (S1) The levels exhaust the telescope. -/
  level_exhausts : ∀ g : Tel, ∃ n, g ∈ level n
  /-- (S3) Every level has finite orbits on the block set. -/
  level_finite_orbits : ∀ (n : ℕ) (i : Block),
    (Set.range fun h : level n ↦ blockAction (h : Tel) i).Finite
  /-- (M) The finitely supported sub-amalgams `M_J` are residually finite. -/
  subAmalgam_residuallyFinite : ∀ J : Set Block, J.Finite →
    Group.ResiduallyFinite (blockSpan block J)
  /-- The telescope levels are residually finite. -/
  level_residuallyFinite : ∀ n : ℕ, Group.ResiduallyFinite (level n)

variable {Lamp : Type} {Tel : Type u} {Block : Type v}
  [Group Lamp] [Group Tel]

/-- **The telescope core `E_T = N_E ⋊ T`.** -/
abbrev telescopeCore (D : TelescopeCoreData Lamp Tel Block) :=
  Lamp ⋊[D.action] Tel

/-- **Theorem 4.1.**  Every finitely generated subgroup of the telescope core
is residually finite.

"Locally" is load-bearing: `E_T` is *not* residually finite (Theorem 4.1a of
`notes/LITERAL_GROUP_IS_SOFIC_2026-08-14.md` --- in any homomorphism to a
finite group the image of `ℤ[1/2]³` is `2`-divisible and finite, hence of odd
order, so `φ(T) = φ(B)`, all same-level lamps are identified, and `w` dies).
No residual finiteness of the core is claimed anywhere in this file. -/
theorem telescopeCore_locallyResiduallyFinite
    (D : TelescopeCoreData Lamp Tel Block) :
    ∀ Q : Subgroup (telescopeCore D), Q.FG → Group.ResiduallyFinite Q :=
  locallyResiduallyFinite_blockTelescope D.action D.block D.blockAction D.level
    D.block_equivariant D.block_span D.block_finite D.level_mono
    D.level_exhausts D.level_finite_orbits D.subAmalgam_residuallyFinite
    D.level_residuallyFinite

/-- The telescope core is LEF.  A group all of whose finitely generated
subgroups are residually finite is locally embeddable into finite groups; the
local embedding of a window is the exact finite model of the window's own
`M_J ⋊ Γ_n`, at whatever dimension that group's residual finiteness
provides. -/
theorem telescopeCore_isLEF (D : TelescopeCoreData Lamp Tel Block) :
    IsLEF (telescopeCore D) :=
  isLEF_of_locallyResiduallyFinite (telescopeCore_locallyResiduallyFinite D)

/-- The telescope core is sofic.  Local embeddings are exact permutation
models: multiplicative defect `0` and Hamming separation `1`. -/
theorem telescopeCore_isSofic (D : TelescopeCoreData Lamp Tel Block) :
    IsSofic (telescopeCore D) :=
  isSofic_of_isLEF (telescopeCore_isLEF D)

/-- The telescope core is operator MF.  This is the `E`-level companion of
`lamp-telescope-base-is-lef`: an LEF group has exact finite models on every
window, and those give the norm-matrix-corona property. -/
theorem telescopeCore_isOperatorMF (D : TelescopeCoreData Lamp Tel Block)
    [Countable (telescopeCore D)] :
    IsOperatorMF (telescopeCore D) :=
  isOperatorMF_of_isLEF (telescopeCore_isLEF D)

end Core

end LiteralTelescopeCoreLEF
end GroupApproximation
