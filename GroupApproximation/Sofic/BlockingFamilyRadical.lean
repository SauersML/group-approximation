import GroupApproximation.Sofic.ActualCoronaMFRadical

/-!
# A blocking family always contains a radical element

The multi-mover arguments produce a *blocking family*: a set `B ⊆ G` such that
every corona representation of `G` kills at least one of its members.  The
member may vary with the representation, and the dossier notes record that as
an obstruction — the conclusion was read as purely existential, giving "some
mover dies in each model" but no single element of the radical.

**That reading is refuted by the universal representation.**
`ActualCoronaMFRadical.exists_actualCoronaRepresentation_ker_eq_actualCoronaMFResidual`
supplies one corona representation whose kernel is exactly the radical.  Feed
the blocking hypothesis that representation and the member it kills lies in the
kernel, hence in the radical.  The family therefore meets the radical outright,
with no hypothesis on `B` beyond the blocking property — `B` need not be
finite, and nothing is assumed about how the killed member varies.

What survives of the original caution is weaker and different: the argument
names *a* member of the family lying in the radical, not *which* member.

There is no pigeonhole and no passage to a subsequence anywhere here, so the
corona-versus-ultraproduct difficulty that §6 of the dossier isolates — that
vanishing along a subsequence does not give vanishing in the corona — never
arises.  The quantifier `∀ρ ∃b` is instantiated exactly once.

## Naming a prescribed member

Fixing the member is a separate, purely algebraic question, and the answer is
exact.  The radical is fully invariant — if every corona representation kills
`x` then it kills `φ x` for any endomorphism `φ`, since `ρ ∘ φ` is again a
corona representation.  So if `b₀` lies in the fully invariant closure of every
member of `B`, it lies in the radical.

That criterion is optimal given only "the radical is fully invariant and meets
`B`": if `b₀` escapes the fully invariant closure of some `b ∈ B`, that closure
is itself a fully invariant subgroup meeting `B` and omitting `b₀`.  The useful
special case is that when endomorphisms act transitively on `B`, *every* member
is in the radical.

Note where the symmetry is applied.  `Sofic/MultiMoverUniversalUpgrade` observes
that precomposing a *fixed* representation `Θ` by an automorphism `σ` carrying
one mover to another yields `(Θ ∘ σ)(w i₀) = 1` — information about the
composite, not about `Θ` — and concludes that a transitive symmetry cannot give
the upgrade.  That is a correct warning about that route and an incorrect
verdict on the question.  Full invariance is a property of the radical, which is
an intersection over *all* representations, so the symmetry is applied after the
intersection rather than inside it and no representation is moved anywhere.
`forall_mem_of_endomorphism_transitive` below is the resulting upgrade, and it
is strictly more general than the inner case that module proves, since it asks
only for endomorphisms.
-/

namespace GroupApproximation
namespace BlockingFamilyRadical

universe u

variable {G : Type u} [Group G]

/-! ## Blocking families -/

/-- `B` blocks the corona representations of `G` when every one of them kills
some member of `B`.  The member is allowed to depend on the representation. -/
def Blocks (B : Set G) : Prop :=
  ∀ (X : ℕ → FiniteModel), ∀ hX : ∀ n, 0 < Fintype.card (X n),
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    ∀ rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
      ∃ b ∈ B, rho b = 1

/-- **A blocking family meets the radical.**  No finiteness, and no control
over which member each representation kills. -/
theorem exists_mem_actualCoronaMFResidual [Countable G] {B : Set G}
    (hB : Blocks B) :
    ∃ b ∈ B, b ∈ actualCoronaMFResidual G := by
  obtain ⟨X, hX, rho, hker⟩ :=
    exists_actualCoronaRepresentation_ker_eq_actualCoronaMFResidual (G := G)
  letI : ∀ n, Nonempty (X n) :=
    fun n ↦ Fintype.card_pos_iff.mp (hX n)
  obtain ⟨b, hbB, hb1⟩ := hB X hX rho
  exact ⟨b, hbB, hker ▸ MonoidHom.mem_ker.mpr hb1⟩

/-- The radical of a nontrivial blocking family is itself nontrivial, provided
the family avoids the identity. -/
theorem actualCoronaMFResidual_ne_bot [Countable G] {B : Set G}
    (hB : Blocks B) (hone : (1 : G) ∉ B) :
    actualCoronaMFResidual G ≠ ⊥ := by
  obtain ⟨b, hbB, hbR⟩ := exists_mem_actualCoronaMFResidual hB
  intro hbot
  rw [hbot, Subgroup.mem_bot] at hbR
  exact hone (hbR ▸ hbB)

/-- A blocking family avoiding the identity obstructs the CDE embedding
property outright.  This is the form the multi-mover argument is actually used
in: the finite family is enough to rule out an injective corona representation,
without naming which member dies. -/
theorem not_isCDEOperatorMF [Countable G] {B : Set G}
    (hB : Blocks B) (hone : (1 : G) ∉ B) :
    ¬ IsCDEOperatorMF G := by
  rw [isCDEOperatorMF_iff_actualCoronaMFResidual_eq_bot]
  exact actualCoronaMFResidual_ne_bot hB hone

/-! ## Full invariance, and naming a member -/

/-- **The radical is fully invariant.**  Precomposing a corona representation
with an endomorphism is again a corona representation. -/
theorem map_mem_actualCoronaMFResidual {x : G} (φ : G →* G)
    (hx : x ∈ actualCoronaMFResidual G) :
    φ x ∈ actualCoronaMFResidual G := by
  intro X hX
  letI : ∀ n, Nonempty (X n) :=
    fun n ↦ Fintype.card_pos_iff.mp (hX n)
  intro rho
  exact hx X hX (rho.comp φ)

/-- The smallest fully invariant subgroup containing an element: the subgroup
generated by all of its endomorphic images. -/
def fullyInvariantClosure (b : G) : Subgroup G :=
  Subgroup.closure {y | ∃ φ : G →* G, φ b = y}

theorem self_mem_fullyInvariantClosure (b : G) :
    b ∈ fullyInvariantClosure b :=
  Subgroup.subset_closure ⟨MonoidHom.id G, rfl⟩

theorem map_mem_fullyInvariantClosure (φ : G →* G) (b : G) :
    φ b ∈ fullyInvariantClosure b :=
  Subgroup.subset_closure ⟨φ, rfl⟩

/-- A radical element drags its whole fully invariant closure into the
radical. -/
theorem fullyInvariantClosure_le_of_mem {b : G}
    (hb : b ∈ actualCoronaMFResidual G) :
    fullyInvariantClosure b ≤ actualCoronaMFResidual G := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨φ, rfl⟩
  exact map_mem_actualCoronaMFResidual φ hb

/-- **Naming a prescribed member.**  An element inside the fully invariant
closure of *every* member of a blocking family lies in the radical, whichever
member the family happens to contribute. -/
theorem mem_of_mem_iInter_fullyInvariantClosure [Countable G] {B : Set G}
    (hB : Blocks B) {b₀ : G}
    (hb₀ : ∀ b ∈ B, b₀ ∈ fullyInvariantClosure b) :
    b₀ ∈ actualCoronaMFResidual G := by
  obtain ⟨b, hbB, hbR⟩ := exists_mem_actualCoronaMFResidual hB
  exact fullyInvariantClosure_le_of_mem hbR (hb₀ b hbB)

/-- **The transitive case.**  If every member of a blocking family is an
endomorphic image of every other, all of them are invisible. -/
theorem forall_mem_of_endomorphism_transitive [Countable G] {B : Set G}
    (hB : Blocks B)
    (htrans : ∀ b ∈ B, ∀ b' ∈ B, ∃ φ : G →* G, φ b = b') :
    ∀ b' ∈ B, b' ∈ actualCoronaMFResidual G := by
  intro b' hb'
  obtain ⟨b, hbB, hbR⟩ := exists_mem_actualCoronaMFResidual hB
  obtain ⟨φ, hφ⟩ := htrans b hbB b' hb'
  exact hφ ▸ map_mem_actualCoronaMFResidual φ hbR

/-- The automorphism form, which is how a symmetry of the construction usually
presents itself.  An automorphism is in particular an endomorphism, so this is
a special case. -/
theorem forall_mem_of_mulEquiv_transitive [Countable G] {B : Set G}
    (hB : Blocks B)
    (htrans : ∀ b ∈ B, ∀ b' ∈ B, ∃ σ : G ≃* G, σ b = b') :
    ∀ b' ∈ B, b' ∈ actualCoronaMFResidual G := by
  refine forall_mem_of_endomorphism_transitive hB fun b hb b' hb' => ?_
  obtain ⟨σ, hσ⟩ := htrans b hb b' hb'
  exact ⟨σ.toMonoidHom, hσ⟩

/-- Restated as a containment: under a transitive symmetry the whole blocking
family sits inside the radical. -/
theorem subset_actualCoronaMFResidual_of_endomorphism_transitive [Countable G]
    {B : Set G} (hB : Blocks B)
    (htrans : ∀ b ∈ B, ∀ b' ∈ B, ∃ φ : G →* G, φ b = b') :
    B ⊆ (actualCoronaMFResidual G : Set G) :=
  fun _ hb => forall_mem_of_endomorphism_transitive hB htrans _ hb

end BlockingFamilyRadical
end GroupApproximation
