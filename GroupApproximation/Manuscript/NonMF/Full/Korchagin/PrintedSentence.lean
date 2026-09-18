import GroupApproximation.Manuscript.NonMF.Full.Korchagin.DirectLimit
import GroupApproximation.Manuscript.OneSidedMFRadical.AmenableTraceTheorem
import GroupApproximation.Meta.AxiomGuard

/-!
# The printed Korchagin sentence about `W_0`

Manuscript `non_mf_groups_exist.tex`, discussion after `thm:amenable-trace`
(tex lines 284--286):

> Since $W_0$ is a direct limit of residually finite groups, it is
> MF~\cite[Corollary~10 and Proposition~13]{Korchagin}.

Clause-by-clause map (`W₀ = CliffordWitnessLocallyRFByInt.ShiftKernel`, the
group called `W_0` in `thm:amenable-trace`; see
`AmenableTraceTheorem.manuscriptShiftKernelIsOperatorMF`):

* "$W_0$ is a direct limit of residually finite groups":
  `IsDirectLimitOfResiduallyFinite W₀`.  The limit is Mathlib's `DirectLimit`
  of a directed system of residually finite groups, up to isomorphism
  (`shiftKernel_isDirectLimitOfResiduallyFinite`).
* "Since ..., it is MF [Korchagin, Cor. 10 and Prop. 13]": a countable direct
  limit of residually finite groups is MF
  (`isOperatorMF_of_isDirectLimitOfResiduallyFinite`).  This is proved here
  and not assumed.  The connecting maps need not be injective
  (`Full/Korchagin/DirectLimit.lean`).
* "it is MF": `Countable W₀ ∧ IsOperatorMF W₀`.  MF is a notion for countable
  groups (tex 87).  The closed proof derives this conjunct from the two
  clauses above, following the manuscript's "Since".
-/

namespace GroupApproximation.Full.NM09

/-- "`G` is a direct limit of residually finite groups": `G` is isomorphic to
the Mathlib direct limit of a directed system of residually finite groups. -/
def IsDirectLimitOfResiduallyFinite (G : Type) [Group G] : Prop :=
  ∃ (ι : Type) (_ : Preorder ι) (_ : IsDirectedOrder ι) (_ : Nonempty ι) (A : ι → Type)
    (_ : ∀ i, Group (A i)) (f : ∀ i j, i ≤ j → A i →* A j) (_ : DirectedSystem A (f · · ·)),
    (∀ i, Group.ResiduallyFinite (A i)) ∧ Nonempty (DirectLimit A f ≃* G)

/-- **Korchagin, Corollary 10 + Proposition 13** (`non_mf_groups_exist.tex`,
tex 284--286): a countable direct limit of residually finite groups is MF. -/
theorem isOperatorMF_of_isDirectLimitOfResiduallyFinite {G : Type} [Group G] [Countable G]
    (hG : IsDirectLimitOfResiduallyFinite G) : IsOperatorMF G := by
  obtain ⟨ι, _, _, _, A, _, f, _, hRF, ⟨e⟩⟩ := hG
  haveI : Countable (DirectLimit A f) := e.injective.countable
  exact CommensurabilityInvariance.isOperatorMF_of_mulEquiv e
    (isOperatorMF_directLimit_of_residuallyFinite f hRF)

section Union

variable {G : Type} [Group G] (K : ℕ → Subgroup G) (hmono : Monotone K)

/-- The inclusion `K i → K j` of an increasing sequence of subgroups. -/
def unionStep (i j : ℕ) (h : i ≤ j) : ↥(K i) →* ↥(K j) :=
  Subgroup.inclusion (hmono h)

/-- The inclusions of an increasing sequence of subgroups form a directed
system. -/
instance unionDirectedSystem :
    DirectedSystem (fun n : ℕ => ↥(K n)) (fun i j h => ⇑(unionStep K hmono i j h)) where
  map_self := fun _ _ => Subtype.ext rfl
  map_map := fun _ _ _ _ _ _ => Subtype.ext rfl

theorem unionCompat (i j : ℕ) (h : i ≤ j) (x : ↥(K i)) :
    (K i).subtype x = (K j).subtype (unionStep K hmono i j h x) :=
  rfl

/-- The comparison map from the direct limit of the subgroups to the group. -/
noncomputable def unionToGroup :
    DirectLimit (fun n : ℕ => ↥(K n)) (unionStep K hmono) →* G where
  toFun := DirectLimit.lift (unionStep K hmono) (fun n => ⇑((K n).subtype))
    (unionCompat K hmono)
  map_one' := DirectLimit.lift_one (fun n => (K n).subtype) (unionCompat K hmono)
  map_mul' := DirectLimit.lift_mul (fun n => (K n).subtype) (unionCompat K hmono)

theorem unionToGroup_injective : Function.Injective (unionToGroup K hmono) :=
  DirectLimit.lift_injective (unionStep K hmono) (fun n => ⇑((K n).subtype))
    (unionCompat K hmono) fun _ _ _ hab => Subtype.ext hab

theorem unionToGroup_surjective (hcov : ∀ g : G, ∃ n, g ∈ K n) :
    Function.Surjective (unionToGroup K hmono) := by
  intro g
  obtain ⟨n, hn⟩ := hcov g
  exact ⟨⟦⟨n, ⟨g, hn⟩⟩⟧, rfl⟩

/-- An increasing union of subgroups is the direct limit of the subgroups. -/
noncomputable def unionEquiv (hcov : ∀ g : G, ∃ n, g ∈ K n) :
    DirectLimit (fun n : ℕ => ↥(K n)) (unionStep K hmono) ≃* G :=
  MulEquiv.ofBijective (unionToGroup K hmono)
    ⟨unionToGroup_injective K hmono, unionToGroup_surjective K hmono hcov⟩

/-- An increasing union of residually finite subgroups is a direct limit of
residually finite groups. -/
include hmono in
theorem isDirectLimitOfResiduallyFinite_of_union (hcov : ∀ g : G, ∃ n, g ∈ K n)
    (hRF : ∀ n, Group.ResiduallyFinite (K n)) : IsDirectLimitOfResiduallyFinite G :=
  ⟨ℕ, inferInstance, inferInstance, inferInstance, fun n => ↥(K n), fun _ => inferInstance,
    unionStep K hmono, unionDirectedSystem K hmono, hRF, ⟨unionEquiv K hmono hcov⟩⟩

end Union

/-- **"$W_0$ is a direct limit of residually finite groups"** (tex 284--285).
Enumerate `W₀ = ShiftKernel` as `e 0, e 1, …`.  The subgroups
`K n = ⟨e 0, …, e (n-1)⟩` increase and exhaust `W₀`.  They are finitely
generated, hence residually finite, because `W₀` is locally residually finite
(`thm:amenable-trace`). -/
theorem shiftKernel_isDirectLimitOfResiduallyFinite :
    IsDirectLimitOfResiduallyFinite CliffordWitnessLocallyRFByInt.ShiftKernel := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat CliffordWitnessLocallyRFByInt.ShiftKernel
  refine isDirectLimitOfResiduallyFinite_of_union
    (fun n => Subgroup.closure
      (((Finset.range n).image e : Finset CliffordWitnessLocallyRFByInt.ShiftKernel) :
        Set CliffordWitnessLocallyRFByInt.ShiftKernel))
    ?_ ?_ ?_
  · intro n m h
    exact Subgroup.closure_mono
      (Finset.coe_subset.mpr (Finset.image_subset_image (Finset.range_subset_range.mpr h)))
  · intro g
    obtain ⟨k, rfl⟩ := he g
    exact ⟨k + 1, Subgroup.subset_closure
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem e (Finset.mem_range.mpr (Nat.lt_add_one k))))⟩
  · intro n
    exact CliffordWitnessLocallyRFByInt.shiftKernel_isLocallyResiduallyFinite
      (Subgroup.closure ((((Finset.range n).image e :
        Finset CliffordWitnessLocallyRFByInt.ShiftKernel)) :
          Set CliffordWitnessLocallyRFByInt.ShiftKernel))
      ⟨(Finset.range n).image e, rfl⟩

/-- **The printed sentence** (`non_mf_groups_exist.tex`, tex 284--286): "Since
$W_0$ is a direct limit of residually finite groups, it is MF [Korchagin,
Corollary 10 and Proposition 13]."  The conjuncts are, in order: `W₀` is a
direct limit of residually finite groups; countable direct limits of residually
finite groups are MF (the cited result); `W₀` is countable and MF. -/
def PrintedKorchaginDirectLimitSentence : Prop :=
  IsDirectLimitOfResiduallyFinite CliffordWitnessLocallyRFByInt.ShiftKernel ∧
    (∀ (G : Type) [Group G] [Countable G],
      IsDirectLimitOfResiduallyFinite G → IsOperatorMF G) ∧
    Countable CliffordWitnessLocallyRFByInt.ShiftKernel ∧
    IsOperatorMF CliffordWitnessLocallyRFByInt.ShiftKernel

/-- **The printed sentence, closed.**  The last conjunct comes from the first
two, as the manuscript's "Since" says. -/
theorem manuscriptSentence_korchaginDirectLimit : PrintedKorchaginDirectLimitSentence :=
  ⟨shiftKernel_isDirectLimitOfResiduallyFinite,
    by
      intro _ _ _ hG
      exact isOperatorMF_of_isDirectLimitOfResiduallyFinite hG,
    inferInstance,
    isOperatorMF_of_isDirectLimitOfResiduallyFinite shiftKernel_isDirectLimitOfResiduallyFinite⟩

#audit_axioms isOperatorMF_of_isDirectLimitOfResiduallyFinite
#audit_axioms shiftKernel_isDirectLimitOfResiduallyFinite
#audit_closed_axioms manuscriptSentence_korchaginDirectLimit

end GroupApproximation.Full.NM09
