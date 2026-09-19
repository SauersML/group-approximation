import GroupApproximation.Sofic.ActualCoronaMFRadical

/-!
# One relation generates a simple-lamp invisible kernel

Section 51 of the ascending-HNN dossier observes that when the lamp group is
finite nonabelian simple, the whole approximation-invisible kernel is the normal
closure of a *single* nontrivial one-site lamp; for `A₅` that element may be
taken to be an involution.  Adding the one relation `r = 1` then turns a sofic
non-MF group into the residually finite MF skeleton, while changing none of the
finite, profinite, compact, linear or corona target data.

The mathematics has nothing to do with lamps, coronas, or the HNN skeleton, so
it is proved here in the form in which it is used: a subgroup of `W` that is the
supremum of a family of *simple* subgroups which `W` permutes transitively by
conjugation is normally generated in `W` by any one nontrivial element of any
one member of the family.

Two steps.  A normal subgroup `N ⊴ W` meeting some `S i` nontrivially contains
all of `S i`, because `N.subgroupOf (S i)` is normal in the simple group `S i`
and is not trivial, so it is everything.  Transitivity of the conjugation action
spreads that from one index to all of them.

The corona statement at the end is the only part mentioning MF, and it is an
implication: the analytic input "the family lies in the MF radical" is a
separate theorem and belongs to its own module.  What is recorded here is that
*given* that input, one element carries the whole kernel.
-/

namespace GroupApproximation

universe u

variable {W : Type u} [Group W]

/-- **A normal subgroup meeting a simple member absorbs it.**  Viewed inside
`S`, the subgroup `N` traces out a normal subgroup of the simple group `S`;
simplicity leaves only `⊥` and `⊤`, and a nontrivial intersection rules out
`⊥`. -/
theorem le_of_normal_of_inf_ne_bot {N S : Subgroup W} (hN : N.Normal)
    (hS : IsSimpleGroup S) (hne : N ⊓ S ≠ ⊥) : S ≤ N := by
  rcases hS.eq_bot_or_eq_top_of_normal (N.subgroupOf S) (hN.subgroupOf S) with
    hbot | htop
  · exact absurd (disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp hbot)) hne
  · exact Subgroup.subgroupOf_eq_top.mp htop

/-- **A single nontrivial element normally generates every member.** -/
theorem le_normalClosure_of_transitive_simple {ι : Type*} (S : ι → Subgroup W)
    (hsimple : ∀ i, IsSimpleGroup (S i)) (i₀ : ι)
    (htrans : ∀ i, ∃ g : W, (S i₀).map (MulAut.conj g).toMonoidHom = S i)
    {r : W} (hr : r ∈ S i₀) (hrne : r ≠ 1) (i : ι) :
    S i ≤ Subgroup.normalClosure ({r} : Set W) := by
  have hNnormal : (Subgroup.normalClosure ({r} : Set W)).Normal :=
    Subgroup.normalClosure_normal
  -- the member containing `r`
  have hbase : S i₀ ≤ Subgroup.normalClosure ({r} : Set W) := by
    refine le_of_normal_of_inf_ne_bot hNnormal (hsimple i₀) ?_
    intro hbot
    have hrmem : r ∈ Subgroup.normalClosure ({r} : Set W) ⊓ S i₀ :=
      ⟨Subgroup.subset_normalClosure rfl, hr⟩
    rw [hbot, Subgroup.mem_bot] at hrmem
    exact hrne hrmem
  -- transport along the conjugation carrying `S i₀` onto `S i`
  obtain ⟨g, hg⟩ := htrans i
  intro y hy
  rw [← hg] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  have hzN : z ∈ Subgroup.normalClosure ({r} : Set W) := hbase hz
  simpa using hNnormal.conj_mem z hzN g

/-- **The supremum form.** -/
theorem iSup_le_normalClosure_of_transitive_simple {ι : Type*} (S : ι → Subgroup W)
    (hsimple : ∀ i, IsSimpleGroup (S i)) (i₀ : ι)
    (htrans : ∀ i, ∃ g : W, (S i₀).map (MulAut.conj g).toMonoidHom = S i)
    {r : W} (hr : r ∈ S i₀) (hrne : r ≠ 1) :
    (⨆ i, S i) ≤ Subgroup.normalClosure ({r} : Set W) :=
  iSup_le fun i =>
    le_normalClosure_of_transitive_simple S hsimple i₀ htrans hr hrne i

/-- **Exactly the normal closure.**  One inclusion is the lemma above; the other
is minimality of a normal closure among normal subgroups containing `r`. -/
theorem normalClosure_eq_of_transitive_simple {ι : Type*} (S : ι → Subgroup W)
    (hsimple : ∀ i, IsSimpleGroup (S i)) (i₀ : ι)
    (htrans : ∀ i, ∃ g : W, (S i₀).map (MulAut.conj g).toMonoidHom = S i)
    {r : W} (hr : r ∈ S i₀) (hrne : r ≠ 1)
    {L : Subgroup W} (hLnormal : L.Normal) (hL : L = ⨆ i, S i) :
    Subgroup.normalClosure ({r} : Set W) = L := by
  haveI := hLnormal
  refine le_antisymm ?_ ?_
  · refine Subgroup.normalClosure_le_normal ?_
    rw [Set.singleton_subset_iff, hL]
    exact le_iSup S i₀ hr
  · rw [hL]
    exact iSup_le_normalClosure_of_transitive_simple S hsimple i₀ htrans hr hrne

/-- **The corona reading.**  Given that the family lies inside the MF radical,
the single element `r` normally generates that whole invisible kernel: every
corona representation already forces the relation `r = 1`. -/
theorem normalClosure_le_actualCoronaMFResidual_of_mem
    {ι : Type*} (S : ι → Subgroup W) (i₀ : ι) {r : W} (hr : r ∈ S i₀)
    (hle : (⨆ i, S i) ≤ actualCoronaMFResidual W) :
    Subgroup.normalClosure ({r} : Set W) ≤ actualCoronaMFResidual W := by
  refine Subgroup.normalClosure_le_normal ?_
  rw [Set.singleton_subset_iff]
  exact hle (le_iSup S i₀ hr)

end GroupApproximation
