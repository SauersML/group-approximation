import GroupApproximation.Sofic.TorsionFreeFullMFRadical
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
import Mathlib.Data.List.Rotate

/-!
# The bespoke small-cancellation router, specification first

The one-paper program reduces the Main Theorem — a two-generated,
finitely presented, torsion-free property-(T) group equal to its own MF
radical — to a single unconditional term of `DefectRoutingData`.  This
module builds the router that is meant to produce that term, from the
top down: the interface is frozen first, the reduction to
`DefectRoutingData` is machine-checked second, and the word
combinatorics is laid from normal forms upward, so that exactly one
combinatorial lemma remains.

Three layers.

* `RoutingLemmaData` is the frozen OUTPUT of the hoped-for bespoke
  small-cancellation lemma, stated for an arbitrary source group, an
  arbitrary designated normal subgroup, and an arbitrary protected
  element — decoupled from the Fournier--Facio skeleton.  Two of the
  program's demands are enforced structurally: nontriviality of the
  protected element is DERIVED from injectivity on the protected set
  (`route_protected_ne_one`), and property (T) is DERIVED from the
  Kazhdan partner's surjection (`kazhdan`); neither is a stored field.

* The keystone `RoutingLemmaData.toDefectRoutingData` certifies that
  the interface's conclusion list is exactly sufficient: instantiated
  at the compression defect and protected simple-factor element of any
  `FournierFacioDefectData`, it yields the `DefectRoutingData` consumed
  by the already-checked full-MF-radical machine.  The converse adapter
  `RelativeCommonQuotientData.toRoutingLemmaData` shows the abstraction
  loses nothing against the literature-shaped interface.

* The word-level foundation works over a free group with Mathlib's
  reduced words: the symmetrization of a relator family (all rotations
  of relators and their formal inverses), the sanity theorem that the
  symmetrization presents the same quotient
  (`normalClosure_symmetrization`), pieces, the metric condition
  `C'(λ)`, and the Greendlinger conclusion.  From the Greendlinger
  conclusion alone we prove the two facts the router's protected-set
  field needs: nontrivial elements of the relator subgroup are longer
  than half of some relator (`norm_bound_of_greendlinger`), and the
  presented quotient is injective on any set whose differences are
  short against all relators (`injOn_mk'_of_greendlinger`).

One lemma remains, and only one: `GreendlingerGate`, the classical
metric small-cancellation theorem that `C'(1/6)` families satisfy the
Greendlinger conclusion.  Following the library's data-not-axiom
doctrine, the gate is consumed as an explicit hypothesis
(`protected_injOn_of_gate`), never as an axiom; its future proof — and
the relative refinement over `Monoid.CoprodI` words and
`HNNExtension.NormalWord` Britton forms that the final router will use
in place of the free-group alphabet — slots into this single site
without disturbing anything downstream.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

universe u

/-! ## The word-level foundation -/

section Words

variable {α : Type*}

/-- The symmetrization of a relator family: every rotation of every
relator and of every formally inverted relator.  Rotation of the letter
list realizes cyclic permutation, and `FreeGroup.invRev` is the formal
inverse word. -/
def symmetrization (R : Set (List (α × Bool))) : Set (List (α × Bool)) :=
  {w | ∃ r ∈ R, ∃ n : ℕ,
    w = r.rotate n ∨ w = (FreeGroup.invRev r).rotate n}

theorem subset_symmetrization (R : Set (List (α × Bool))) :
    R ⊆ symmetrization R :=
  fun r hr => ⟨r, hr, 0, Or.inl (List.rotate_zero r).symm⟩

/-- Rotating a letter list conjugates the free-group element it spells. -/
theorem isConj_mk_rotate (w : List (α × Bool)) (n : ℕ) :
    IsConj (FreeGroup.mk w) (FreeGroup.mk (w.rotate n)) := by
  rcases eq_or_ne w [] with rfl | hw
  · rw [List.rotate_nil]
  · rw [← List.rotate_mod]
    have hlen : w.length ≠ 0 := fun h => hw (List.length_eq_zero_iff.mp h)
    have hlt : n % w.length < w.length :=
      Nat.mod_lt _ (Nat.pos_of_ne_zero hlen)
    rw [List.rotate_eq_drop_append_take hlt.le, isConj_iff]
    refine ⟨(FreeGroup.mk (w.take (n % w.length)))⁻¹, ?_⟩
    have hsplit : FreeGroup.mk w =
        FreeGroup.mk (w.take (n % w.length)) *
          FreeGroup.mk (w.drop (n % w.length)) := by
      rw [FreeGroup.mul_mk, List.take_append_drop]
    rw [← FreeGroup.mul_mk, hsplit, inv_inv]
    group

/-- Every member of the symmetrization spells a conjugate of a relator
or of an inverted relator. -/
theorem exists_isConj_of_mem_symmetrization {R : Set (List (α × Bool))}
    {w : List (α × Bool)} (hw : w ∈ symmetrization R) :
    ∃ r ∈ R, IsConj (FreeGroup.mk r) (FreeGroup.mk w) ∨
      IsConj (FreeGroup.mk r)⁻¹ (FreeGroup.mk w) := by
  obtain ⟨r, hr, n, h | h⟩ := hw
  · refine ⟨r, hr, Or.inl ?_⟩
    rw [h]
    exact isConj_mk_rotate r n
  · refine ⟨r, hr, Or.inr ?_⟩
    rw [h, FreeGroup.inv_mk]
    exact isConj_mk_rotate (FreeGroup.invRev r) n

/-- **Symmetrizing does not change the presented group.**  The normal
closure of the symmetrization is the normal closure of the relators. -/
theorem normalClosure_symmetrization (R : Set (List (α × Bool))) :
    Subgroup.normalClosure (FreeGroup.mk '' symmetrization R) =
      Subgroup.normalClosure (FreeGroup.mk '' R) := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨r, hr, hconj | hconj⟩ := exists_isConj_of_mem_symmetrization hw
    · obtain ⟨c, hc⟩ := isConj_iff.mp hconj
      rw [← hc]
      exact Subgroup.normalClosure_normal.conj_mem _
        (Subgroup.subset_normalClosure
          (show FreeGroup.mk r ∈ FreeGroup.mk '' R from ⟨r, hr, rfl⟩)) c
    · obtain ⟨c, hc⟩ := isConj_iff.mp hconj
      rw [← hc]
      exact Subgroup.normalClosure_normal.conj_mem _
        (inv_mem (Subgroup.subset_normalClosure
          (show FreeGroup.mk r ∈ FreeGroup.mk '' R from ⟨r, hr, rfl⟩))) c
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨r, hr, rfl⟩
    exact Subgroup.subset_normalClosure
      ⟨r, subset_symmetrization R hr, rfl⟩

/-- A piece: a common prefix of two distinct members of the symmetrized
family.  With rotations present, prefixes capture occurrences at every
position. -/
def IsPiece (S : Set (List (α × Bool))) (p : List (α × Bool)) : Prop :=
  ∃ w₁ ∈ S, ∃ w₂ ∈ S, w₁ ≠ w₂ ∧ p <+: w₁ ∧ p <+: w₂

/-- A finite relator family has a strict uniform ceiling on the lengths of its
pieces.  This is deliberately only a finiteness bound: obtaining a useful
small-cancellation ratio still requires the ceiling to be small compared with
the shortest relator. -/
theorem exists_piece_length_ceiling {R : Set (List (α × Bool))}
    (hR : R.Finite) :
    ∃ C : ℕ, ∀ p, IsPiece (symmetrization R) p → p.length < C := by
  classical
  have hlength : ∃ C : ℕ, ∀ r ∈ R, r.length < C := by
    induction R, hR using Set.Finite.induction_on with
    | empty =>
        exact ⟨1, by simp⟩
    | @insert r R hr hR ih =>
        obtain ⟨C, hC⟩ := ih
        refine ⟨max (r.length + 1) C, ?_⟩
        intro w hw
        rcases Set.mem_insert_iff.mp hw with rfl | hw
        · omega
        · exact lt_of_lt_of_le (hC w hw) (Nat.le_max_right _ _)
  obtain ⟨C, hC⟩ := hlength
  refine ⟨C, ?_⟩
  intro p hp
  obtain ⟨w₁, hw₁, -, -, hp₁, -⟩ := hp
  obtain ⟨r, hr, _, hrot | hrot⟩ := hw₁
  · have hpLen : p.length ≤ w₁.length := by
      obtain ⟨t, rfl⟩ := hp₁
      simp
    have hwLen : w₁.length = r.length := by
      rw [hrot, List.length_rotate]
    omega
  · have hpLen : p.length ≤ w₁.length := by
      obtain ⟨t, rfl⟩ := hp₁
      simp
    have hwLen : w₁.length = r.length := by
      rw [hrot, List.length_rotate, FreeGroup.invRev_length]
    omega

/-- The metric condition `C'(λ)`: every piece occupies less than a
`λ`-fraction of every symmetrized relator it prefixes.  For positive
`λ` this in particular forces the relators to be nonempty, matching the
classical convention. -/
def MetricSmallCancellation (R : Set (List (α × Bool))) (lam : ℚ) : Prop :=
  ∀ p, IsPiece (symmetrization R) p →
    ∀ w ∈ symmetrization R, p <+: w →
      (p.length : ℚ) < lam * (w.length : ℚ)

/-- The Greendlinger conclusion for a relator family: every nonempty
reduced word spelling an element of the normal closure of the relators
contains, as a contiguous subword, more than half of some symmetrized
relator. -/
def GreendlingerConclusion (R : Set (List (α × Bool))) : Prop :=
  ∀ w : List (α × Bool), FreeGroup.IsReduced w → w ≠ [] →
    FreeGroup.mk w ∈ Subgroup.normalClosure (FreeGroup.mk '' R) →
    ∃ r ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: r ∧ r.length < 2 * u.length

/-- **The Greendlinger conclusion at the sharp constant.**  The same statement
as `GreendlingerConclusion`, with the arc bounded by `(1 - 3·lam)·|r|` instead
of by `|r|/2`.

At `lam = 1/6` the two agree exactly — `1 - 3/6 = 1/2` — so the half-form is
that reading of this one; below `1/6` this is strictly stronger.  The strength
is spent by the torsion descent, whose residual case is arithmetically empty at
`lam ≤ 1/8` given this form and open given the half-form.

It lives here, beside the conclusion it generalizes, because it is a property of
a relator family and not of either lane that consumes it: the gate lane proves
it and the torsion lane spends it, and a definition owned by one of them would
be a definition the other could only match by hand. -/
def GreendlingerConclusionSharp (R : Set (List (α × Bool))) (lam : ℚ) : Prop :=
  ∀ w : List (α × Bool), FreeGroup.IsReduced w → w ≠ [] →
    FreeGroup.mk w ∈ Subgroup.normalClosure (FreeGroup.mk '' R) →
    ∃ r ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: r ∧ (1 - 3 * lam) * (r.length : ℚ) < (u.length : ℚ)

/-- Nontrivial elements of the relator subgroup are longer than half of
some symmetrized relator. -/
theorem norm_bound_of_greendlinger [DecidableEq α]
    {R : Set (List (α × Bool))} (hG : GreendlingerConclusion R)
    {g : FreeGroup α} (hg : g ≠ 1)
    (hmem : g ∈ Subgroup.normalClosure (FreeGroup.mk '' R)) :
    ∃ r ∈ symmetrization R, r.length < 2 * FreeGroup.norm g := by
  have hred : FreeGroup.IsReduced g.toWord := FreeGroup.isReduced_toWord
  have hne : g.toWord ≠ [] := fun h => hg (FreeGroup.toWord_eq_nil_iff.mp h)
  have hmem' : FreeGroup.mk g.toWord ∈
      Subgroup.normalClosure (FreeGroup.mk '' R) := by
    rw [FreeGroup.mk_toWord]
    exact hmem
  obtain ⟨r, hr, u, hu_inf, -, hlen⟩ := hG g.toWord hred hne hmem'
  refine ⟨r, hr, ?_⟩
  have h1 : u.length ≤ g.toWord.length := hu_inf.sublist.length_le
  have h2 : FreeGroup.norm g = g.toWord.length := rfl
  omega

/-- **Protected injectivity from the Greendlinger conclusion.**  The
presented quotient is injective on every set whose pairwise differences
are short against all symmetrized relators.  This is the router's
protected-set obligation in exactly the shape the interface consumes:
survival of protected elements is a structural theorem of the word
combinatorics, never an asserted boolean. -/
theorem injOn_mk'_of_greendlinger [DecidableEq α]
    {R : Set (List (α × Bool))} (hG : GreendlingerConclusion R)
    (P : Set (FreeGroup α))
    (hshort : ∀ r ∈ symmetrization R, ∀ x ∈ P, ∀ y ∈ P,
      2 * FreeGroup.norm (x / y) ≤ r.length) :
    Set.InjOn
      (QuotientGroup.mk' (Subgroup.normalClosure (FreeGroup.mk '' R)))
      P := by
  intro x hx y hy hxy
  by_contra hne
  have hker : x / y ∈ (QuotientGroup.mk'
      (Subgroup.normalClosure (FreeGroup.mk '' R))).ker := by
    rw [MonoidHom.mem_ker, map_div, hxy, div_self']
  rw [QuotientGroup.ker_mk'] at hker
  have hne1 : x / y ≠ 1 := fun h => hne (div_eq_one.mp h)
  obtain ⟨r, hr, hlt⟩ := norm_bound_of_greendlinger hG hne1 hker
  have hs := hshort r hr x hx y hy
  omega

/-- **The single remaining combinatorial lemma, frozen as a gate.**
Classical metric small cancellation: a `C'(1/6)` family of cyclically
reduced relators satisfies the Greendlinger conclusion.  Following the
library's data-not-axiom doctrine this is consumed only as an explicit
hypothesis; proving it — by Greendlinger's original reduced-diagram
count, or by the elementary Dehn-reduction induction — is the router
program's one open combinatorial obligation over a free group.  The
relative refinement replaces letters by `Monoid.CoprodI` syllables. -/
def GreendlingerGate (α : Type*) : Prop :=
  ∀ R : Set (List (α × Bool)),
    (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) →
    MetricSmallCancellation R (1 / 6) →
    GreendlingerConclusion R

/-- Under the gate, a `C'(1/6)` presentation is injective on every
protected set that is short against its relators. -/
theorem protected_injOn_of_gate [DecidableEq α]
    (hgate : GreendlingerGate α) {R : Set (List (α × Bool))}
    (hcyc : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r)
    (hmetric : MetricSmallCancellation R (1 / 6))
    (P : Set (FreeGroup α))
    (hshort : ∀ r ∈ symmetrization R, ∀ x ∈ P, ∀ y ∈ P,
      2 * FreeGroup.norm (x / y) ≤ r.length) :
    Set.InjOn
      (QuotientGroup.mk' (Subgroup.normalClosure (FreeGroup.mk '' R)))
      P :=
  injOn_mk'_of_greendlinger (hgate R hcyc hmetric) P hshort

end Words

/-! ## The abstract router interface -/

/-- The frozen output of the bespoke small-cancellation routing lemma,
decoupled from the Fournier--Facio skeleton: a source group `E`, a
designated normal subgroup `N`, one protected element `s`, and a
finitely presented Kazhdan partner `B` are routed onto a common
quotient in which `N` fills everything and `s` survives.

Nontriviality of the routed protected element and property (T) of the
quotient are deliberately NOT fields: they are theorems of the
interface, derived from `protected_injOn` and from `partner_surjective`
respectively. -/
structure RoutingLemmaData
    (E : Type u) [Group E] (N : Subgroup E) [N.Normal] (s : E)
    (B : Type) [Group B] where
  /-- The routed common quotient. -/
  Quotient : Type
  [groupQuotient : Group Quotient]
  /-- The routing epimorphism from the source. -/
  route : E →* Quotient
  /-- The routing map is onto. -/
  route_surjective : Function.Surjective route
  /-- The epimorphism from the Kazhdan partner. -/
  partner : B →* Quotient
  /-- The partner map is onto. -/
  partner_surjective : Function.Surjective partner
  /-- The routed quotient is finitely presented. -/
  [finitelyPresented : Group.IsFinitelyPresented Quotient]
  /-- The designated normal subgroup maps onto the whole quotient. -/
  defect_top : N.map route = ⊤
  /-- The routing map is injective on the protected set. -/
  protected_injOn : Set.InjOn route ({1, s} : Set E)
  /-- First generator produced by the routing stage. -/
  generatorOne : Quotient
  /-- Second generator produced by the routing stage. -/
  generatorTwo : Quotient
  /-- The two produced elements generate the quotient. -/
  generates :
    Subgroup.closure ({generatorOne, generatorTwo} : Set Quotient) = ⊤
  /-- Torsion-freeness of the routed quotient, in power form. -/
  torsionFree : IsPowerTorsionFree Quotient

namespace RoutingLemmaData

variable {E : Type u} [Group E] {N : Subgroup E} [N.Normal] {s : E}
    {B : Type} [Group B] (R : RoutingLemmaData E N s B)

local instance routerQuotientGroup : Group R.Quotient := R.groupQuotient

/-- The routed quotient is two-generated by the produced elements. -/
theorem isTwoGenerated : IsTwoGenerated R.Quotient :=
  ⟨R.generatorOne, R.generatorTwo, R.generates⟩

/-- **Derived, not stored**: the protected element survives routing.
Nontriviality of the routed witness is a consequence of injectivity on
the protected set — the structural form least likely to conceal an
error in an informal quotient construction. -/
theorem route_protected_ne_one (hs : s ≠ 1) : R.route s ≠ 1 := by
  intro h
  apply hs
  apply R.protected_injOn (Set.mem_insert_of_mem _ rfl) (Set.mem_insert _ _)
  rw [h, map_one]

/-- **Derived, not stored**: property (T) of the routed quotient is
inherited through the Kazhdan partner's surjection. -/
theorem kazhdan (hB : HasKazhdanPropertyT.{0, 0} B) :
    HasKazhdanPropertyT.{0, 0} R.Quotient :=
  HasKazhdanPropertyT.of_surjective R.partner R.partner_surjective hB

end RoutingLemmaData

/-- **The keystone reduction.**  The abstract router output,
instantiated at the compression defect and the protected simple-factor
element of a Fournier--Facio defect datum, is exactly the routed data
consumed by the full-MF-radical machine.  This certifies that the
bespoke lemma's conclusion list is sufficient: whoever proves the
routing lemma has proved the Main Theorem. -/
def RoutingLemmaData.toDefectRoutingData
    {P : Type} {E : Type u} [Group P] [Group E]
    (D : FournierFacioDefectData P E) {B : Type} [Group B]
    (hB : HasKazhdanPropertyT.{0, 0} B)
    (R : RoutingLemmaData E D.core.defectNormal D.s B) :
    DefectRoutingData D where
  Quotient := R.Quotient
  groupQuotient := R.groupQuotient
  quotient := R.route
  quotient_surjective := R.route_surjective
  finitelyPresented := R.finitelyPresented
  kazhdan := R.kazhdan hB
  defect_surjective := R.defect_top
  protected_ne_one := R.route_protected_ne_one D.s_ne_one
  generatorOne := R.generatorOne
  generatorTwo := R.generatorTwo
  generates := R.generates
  torsionFree := R.torsionFree

/-- The literature-shaped relative common-quotient output is an
instance of the abstract router interface: the abstraction loses
nothing. -/
def _root_.GroupApproximation.RelativeCommonQuotientData.toRoutingLemmaData
    {P : Type} {E : Type u} [Group P] [Group E]
    {D : FournierFacioDefectData P E} {B : Type} [Group B]
    (C : RelativeCommonQuotientData D B) :
    RoutingLemmaData E D.core.defectNormal D.s B where
  Quotient := C.Quotient
  groupQuotient := C.groupQuotient
  route := C.source
  route_surjective := C.source_surjective
  partner := C.kazhdanMap
  partner_surjective := C.kazhdanMap_surjective
  finitelyPresented := C.finitelyPresented
  defect_top := C.defect_surjective
  protected_injOn := C.protected_injective
  generatorOne := C.generatorOne
  generatorTwo := C.generatorTwo
  generates := C.generates
  torsionFree := C.torsionFree

/-- Any inhabitant of the abstract router interface at the
Fournier--Facio data discharges the frozen endpoint's single
hypothesis. -/
theorem nonempty_defectRoutingData
    {P : Type} {E : Type u} [Group P] [Group E]
    (D : FournierFacioDefectData P E) {B : Type} [Group B]
    (hB : HasKazhdanPropertyT.{0, 0} B)
    (h : Nonempty (RoutingLemmaData E D.core.defectNormal D.s B)) :
    Nonempty (DefectRoutingData D) := by
  obtain ⟨R⟩ := h
  exact ⟨R.toDefectRoutingData D hB⟩

end SmallCancellationRouter
end GroupApproximation
