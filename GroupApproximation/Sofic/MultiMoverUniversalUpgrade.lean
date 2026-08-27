import GroupApproximation.Sofic.ActualCoronaMFRadical

/-!
# From "one of these movers dies" to "this element dies"

The multi-mover collapse criterion is existential: it produces a finite family
`w : ι → G` such that *every* corona representation kills *some* member, with
the member depending on the representation.  That is weaker than membership of
any one `w i` in the MF radical, and the repo records the gap deliberately.
Compression-form arguments deliver the universal conclusion directly; the
question is when the existential form can be upgraded to it.

There is an exact answer, and it costs nothing analytic.  A kernel is normal,
so a representation that kills `w i` kills the whole normal closure
`⟨⟨w i⟩⟩`.  Whichever `i` the representation happens to choose, it therefore
kills everything lying in *every* `⟨⟨w i⟩⟩` at once.  So the universal content
of an existential multi-mover obstruction is precisely

  `⨅ i, ⟨⟨w i⟩⟩ ≤ Res_MF(G)`,

and the upgrade is available exactly when that intersection is nontrivial.  No
hypothesis on the family is needed for the inclusion itself; hypotheses only
enter when one wants to exhibit a nontrivial element of the intersection.

Two sufficient conditions drop out, and they are the two the dossier gestures
at:

* **Conjugate movers.**  If the `w i` are pairwise conjugate the normal
  closures coincide, so the intersection contains `w i₀` itself and the
  designated mover is in the radical
  (`mem_actualCoronaMFResidual_of_forall_conj`).
* **A symmetry permuting the movers.**  Chasing a *fixed* representation `Θ`
  does not work, and the failure is worth stating because it is the natural
  first attempt.  Given a `Θ` that kills `w i`, an automorphism `σ` carrying
  `w i₀` to `w i` yields `(Θ ∘ σ)(w i₀) = 1` -- which says the *composite*
  kills the designated mover, not that `Θ` does.  Along that route symmetry
  moves the representation, and the quantifier `∀Θ ∃i` is exactly the statement
  that one may not move it.

  Conjugation survives that route unaided, because it is inner: conjugate
  movers have *equal* normal closures, so no transport is needed at all.

  A general symmetry *also* gives the upgrade, but by a different route, and an
  earlier version of this note wrongly read the failure above as a verdict that
  it does not.  The fix is to stop fixing a `Θ`.  Apply the symmetry after the
  intersection over all representations rather than inside it: the radical is
  fully invariant, so an endomorphism carrying a radical element to `w i` puts
  `w i` in the radical, with no representation moved anywhere.  Combined with
  the universal representation -- whose kernel *is* the radical, so `∀Θ ∃i`
  instantiates once and names a radical member of the family -- this yields
  *every* member of a transitively permuted family, and for endomorphisms
  rather than merely automorphisms.  See
  `Sofic/BlockingFamilyRadical.forall_mem_of_endomorphism_transitive`, which
  supersedes the negative reading of this bullet.

The negative half is equally clean: when `⨅ i, ⟨⟨w i⟩⟩` is trivial the
existential statement has no universal consequence beyond `1 ∈ Res_MF`, so no
argument that uses only the multi-mover conclusion can place a fixed element in
the radical.  Anything stronger must use more than the collapse criterion --
which is what the compression form does.
-/

namespace GroupApproximation

universe u

variable {G : Type u} [Group G]

/-- **The MF radical is preserved by every automorphism.**  Functoriality gives
one inclusion, and applying it to the inverse gives the other.

This is what a symmetry of a mover family buys: the intersection of the normal
closures is carried to itself, so it is the object a symmetric argument may
test.  What it does *not* do is transport a victim between representations --
that route fails, as the module docstring explains.  Applied to the radical
rather than to any one kernel, this same invariance is what promotes a
transitively permuted blocking family into the radical member by member
(`Sofic/BlockingFamilyRadical`). -/
theorem map_actualCoronaMFResidual_mulEquiv (σ : G ≃* G) :
    (actualCoronaMFResidual G).map σ.toMonoidHom = actualCoronaMFResidual G := by
  refine le_antisymm (map_actualCoronaMFResidual_le _) ?_
  intro x hx
  have hsymm : σ.symm.toMonoidHom x ∈ actualCoronaMFResidual G :=
    map_actualCoronaMFResidual_le σ.symm.toMonoidHom
      (Subgroup.mem_map_of_mem _ hx)
  exact ⟨σ.symm x, hsymm, by simp⟩

/-- **The universal content of an existential multi-mover obstruction.**

If every corona representation kills at least one member of the family `w`,
then every element lying in all of the normal closures `⟨⟨w i⟩⟩` is invisible
to every corona representation.

The hypothesis is written out rather than named, so that it is a statement
about `G` and `w` and not a new predicate standing unproved in the corpus. -/
theorem iInf_normalClosure_le_actualCoronaMFResidual {ι : Type*} (w : ι → G)
    (hmulti : ∀ (X : ℕ → FiniteModel), ∀ hX : ∀ n, 0 < Fintype.card (X n),
      letI : ∀ n, Nonempty (X n) := fun n ↦ Fintype.card_pos_iff.mp (hX n)
      ∀ rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
        ∃ i, rho (w i) = 1) :
    (⨅ i, Subgroup.normalClosure {w i}) ≤ actualCoronaMFResidual G := by
  intro x hx X hX
  letI : ∀ n, Nonempty (X n) := fun n ↦ Fintype.card_pos_iff.mp (hX n)
  intro rho
  obtain ⟨i, hi⟩ := hmulti X hX rho
  have hmem : x ∈ Subgroup.normalClosure {w i} := Subgroup.mem_iInf.mp hx i
  have hle : Subgroup.normalClosure {w i} ≤ rho.ker :=
    Subgroup.normalClosure_le_normal
      (Set.singleton_subset_iff.mpr (MonoidHom.mem_ker.mpr hi))
  exact hle hmem

/-- **The two-mover case**, written out because it is the shape the collapse
criterion actually produces and the indexed form obscures it: if every corona
representation kills `w₁` or kills `w₂`, then everything lying in *both* normal
closures is invisible to all of them. -/
theorem inf_normalClosure_le_actualCoronaMFResidual (w₁ w₂ : G)
    (hmulti : ∀ (X : ℕ → FiniteModel), ∀ hX : ∀ n, 0 < Fintype.card (X n),
      letI : ∀ n, Nonempty (X n) := fun n ↦ Fintype.card_pos_iff.mp (hX n)
      ∀ rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
        rho w₁ = 1 ∨ rho w₂ = 1) :
    Subgroup.normalClosure {w₁} ⊓ Subgroup.normalClosure {w₂}
      ≤ actualCoronaMFResidual G := by
  intro x hx X hX
  letI : ∀ n, Nonempty (X n) := fun n ↦ Fintype.card_pos_iff.mp (hX n)
  intro rho
  obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.mp hx
  rcases hmulti X hX rho with h | h
  · exact Subgroup.normalClosure_le_normal
      (Set.singleton_subset_iff.mpr (MonoidHom.mem_ker.mpr h)) hx₁
  · exact Subgroup.normalClosure_le_normal
      (Set.singleton_subset_iff.mpr (MonoidHom.mem_ker.mpr h)) hx₂

/-- The object the criterion produces is itself a normal subgroup, so it is a
candidate piece of the radical and not merely a set of elements.  An
intersection of normal subgroups is normal, and each `⟨⟨w i⟩⟩` is. -/
instance iInf_normalClosure_normal {ι : Type*} (w : ι → G) :
    (⨅ i, Subgroup.normalClosure {w i}).Normal :=
  Subgroup.normal_iInf_normal fun _ => Subgroup.normalClosure_normal

/-- **Conjugate movers upgrade.**  If every member of the family is conjugate
to a designated one, the designated one is itself in the MF radical: the
representation's choice of victim is immaterial, because killing any conjugate
kills them all. -/
theorem mem_actualCoronaMFResidual_of_forall_conj {ι : Type*} (w : ι → G)
    (hmulti : ∀ (X : ℕ → FiniteModel), ∀ hX : ∀ n, 0 < Fintype.card (X n),
      letI : ∀ n, Nonempty (X n) := fun n ↦ Fintype.card_pos_iff.mp (hX n)
      ∀ rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
        ∃ i, rho (w i) = 1)
    (i₀ : ι) (hconj : ∀ i, ∃ g : G, w i = g * w i₀ * g⁻¹) :
    w i₀ ∈ actualCoronaMFResidual G := by
  refine iInf_normalClosure_le_actualCoronaMFResidual w hmulti ?_
  refine Subgroup.mem_iInf.mpr fun i => ?_
  obtain ⟨g, hg⟩ := hconj i
  have hbase : w i ∈ Subgroup.normalClosure ({w i} : Set G) :=
    Subgroup.subset_normalClosure rfl
  have hconjmem : g⁻¹ * w i * g⁻¹⁻¹ ∈ Subgroup.normalClosure ({w i} : Set G) :=
    Subgroup.normalClosure_normal.conj_mem _ hbase g⁻¹
  rw [inv_inv] at hconjmem
  have : g⁻¹ * w i * g = w i₀ := by rw [hg]; group
  rwa [this] at hconjmem

end GroupApproximation
