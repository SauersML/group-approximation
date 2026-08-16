import GroupApproximation.Sofic.ActualCoronaMFRadical

/-!
# A simple non-MF group is its own MF radical

"Is there a finitely presented group whose entire group is its MF radical --
one for which every corona representation is trivial?" is on the dossier's list
of high-payoff questions.  The radical-theoretic half of it is immediate and
worth recording, because it says the question is not really about radicals at
all.

`actualCoronaMFResidual G` is a *normal* subgroup, and it is trivial exactly
when `G` is MF.  In a simple group a normal subgroup is `⊥` or `⊤`, and `⊥` is
excluded by non-MF.  So for simple groups there is no middle case:

  **simple and not MF  ⟹  the radical is everything.**

Hence the question reduces to the existence of a *finitely presented simple
non-MF group*, with no separate computation of a radical required.  That is a
statement about the construction lane, not about the radical: the endpoint
`FullMFRadicalEndpoint.exists_group_with_every_nontrivial_quotient_not_isCDEOperatorMF`
is the routed form of the same target, and simplicity is the cheapest way to
get the "every nontrivial quotient" clause, since there is only one such
quotient to check.

The contrapositive is the useful direction when hunting for examples: a simple
group with even one nontrivial corona representation is MF outright.  So in the
simple case, "some finite-dimensional shadow survives" and "the group is MF"
are the same statement, and there is nothing in between to engineer.
-/

namespace GroupApproximation

universe u

variable {G : Type u} [Group G]

/-- **Simple and non-MF forces the full radical.**  The MF radical is normal,
so in a simple group it is `⊥` or `⊤`; `⊥` says the group is MF. -/
theorem actualCoronaMFResidual_eq_top_of_isSimpleGroup [Countable G]
    (hsimple : IsSimpleGroup G) (hnot : ¬ IsCDEOperatorMF G) :
    actualCoronaMFResidual G = ⊤ := by
  rcases hsimple.eq_bot_or_eq_top_of_normal (actualCoronaMFResidual G)
      inferInstance with hbot | htop
  · exact absurd (isCDEOperatorMF_iff_actualCoronaMFResidual_eq_bot.mpr hbot) hnot
  · exact htop

/-- Every element of such a group is invisible to every corona representation:
the representations are all trivial. -/
theorem actualCoronaMFInvisible_of_isSimpleGroup [Countable G]
    (hsimple : IsSimpleGroup G) (hnot : ¬ IsCDEOperatorMF G) (x : G) :
    ActualCoronaMFInvisible x := by
  have hmem : x ∈ actualCoronaMFResidual G := by
    rw [actualCoronaMFResidual_eq_top_of_isSimpleGroup hsimple hnot]
    exact Subgroup.mem_top x
  exact hmem

/-- **The hunting criterion, contrapositive.**  A simple group admitting a
single nontrivial corona representation is MF.  In the simple case there is no
intermediate radical to engineer. -/
theorem isCDEOperatorMF_of_isSimpleGroup_of_exists_nontrivial [Countable G]
    (hsimple : IsSimpleGroup G)
    (hx : ∃ x : G, ¬ ActualCoronaMFInvisible x) :
    IsCDEOperatorMF G := by
  by_contra hnot
  obtain ⟨x, hxne⟩ := hx
  exact hxne (actualCoronaMFInvisible_of_isSimpleGroup hsimple hnot x)

end GroupApproximation
