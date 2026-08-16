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

  `⨅ i, ⟨⟨w i⟩⟩ ≤ Rad_MF(G)`,

and the upgrade is available exactly when that intersection is nontrivial.  No
hypothesis on the family is needed for the inclusion itself; hypotheses only
enter when one wants to exhibit a nontrivial element of the intersection.

Two sufficient conditions drop out, and they are the two the dossier gestures
at:

* **Conjugate movers.**  If the `w i` are pairwise conjugate the normal
  closures coincide, so the intersection contains `w i₀` itself and the
  designated mover is in the radical
  (`mem_actualCoronaMFResidual_of_forall_conj`).
* **A symmetry permuting the movers.**  An automorphism permuting the family
  permutes the normal closures and so fixes their intersection setwise; the
  intersection is the canonical symmetric object to test, which is why a
  symmetry helps at all.

The negative half is equally clean: when `⨅ i, ⟨⟨w i⟩⟩` is trivial the
existential statement has no universal consequence beyond `1 ∈ Rad_MF`, so no
argument that uses only the multi-mover conclusion can place a fixed element in
the radical.  Anything stronger must use more than the collapse criterion --
which is what the compression form does.
-/

namespace GroupApproximation

universe u

variable {G : Type u} [Group G]

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
