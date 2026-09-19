import GroupApproximation.Sofic.ActualCoronaMFRadical
import GroupApproximation.Sofic.CDEOperatorMF
import GroupApproximation.Sofic.OperatorMFPositiveControls

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
statement about the construction lane, not about the radical. The hereditary
theorems on `DefectRoutingData` give the routed form of the same target, and
simplicity is the cheapest way to get the "every nontrivial quotient" clause,
since there is only one such quotient to check.

The contrapositive is the useful direction when hunting for examples: a simple
group with even one nontrivial corona representation is MF outright.  So in the
simple case, "some finite-dimensional shadow survives" and "the group is MF"
are the same statement, and there is nothing in between to engineer.

`eq_one_of_isSimpleGroup_of_target_isCDEOperatorMF` states the question in its
own words -- *every* homomorphism to *any* countable MF group is trivial -- and
proves it without mentioning a radical: the kernel is normal, so it is `⊥` or
`⊤`, and `⊥` would embed `G` into an MF group, which passes to subgroups.  The
target is unconstrained apart from being countable and MF, and may sit in
another universe.
-/

namespace GroupApproximation

universe u v

variable {G : Type u} [Group G]

/-- **The dichotomy, before any hypothesis on MF-ness.**  The MF radical is
normal, so in a simple group it is `⊥` or `⊤` and nothing else.  Everything
below is this dichotomy plus the reading of each side. -/
theorem actualCoronaMFResidual_eq_bot_or_eq_top_of_isSimpleGroup
    (hsimple : IsSimpleGroup G) :
    actualCoronaMFResidual G = ⊥ ∨ actualCoronaMFResidual G = ⊤ :=
  hsimple.eq_bot_or_eq_top_of_normal (actualCoronaMFResidual G) inferInstance

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

/-- **The canonical MF quotient is trivial.**  Every corona representation of
such a group factors through `G ⧸ Res_MF`, and that quotient is a point, so
every corona representation is trivial and there is no nontrivial MF target to
map to.  This is the "entire group is its MF radical" property in the form the
dossier's question asks for. -/
theorem subsingleton_quotient_actualCoronaMFResidual_of_isSimpleGroup
    [Countable G] (hsimple : IsSimpleGroup G) (hnot : ¬ IsCDEOperatorMF G) :
    Subsingleton (G ⧸ actualCoronaMFResidual G) := by
  have h : actualCoronaMFResidual G = ⊤ :=
    actualCoronaMFResidual_eq_top_of_isSimpleGroup hsimple hnot
  haveI : Subsingleton (G ⧸ (⊤ : Subgroup G)) :=
    QuotientGroup.subsingleton_quotient_top
  exact Equiv.subsingleton (QuotientGroup.quotientMulEquivOfEq h).toEquiv

/-- **Every homomorphism to an MF group is trivial.**  This is the dossier's
question in its own words, and it needs no radical at all: the kernel is normal,
so by simplicity it is `⊥` or `⊤`.  If it were `⊥` the map would embed `G` into
an MF group, and MF passes to subgroups, so `G` would be MF.  Hence the kernel
is everything.

Note the target may live in any universe and is not assumed simple, or
finitely generated, or anything else -- only countable and MF. -/
theorem eq_one_of_isSimpleGroup_of_target_isCDEOperatorMF
    [Countable G] (hsimple : IsSimpleGroup G) (hnot : ¬ IsCDEOperatorMF G)
    {H : Type v} [Group H] [Countable H] (hH : IsCDEOperatorMF H)
    (f : G →* H) (g : G) : f g = 1 := by
  rcases hsimple.eq_bot_or_eq_top_of_normal f.ker inferInstance with hbot | htop
  · -- an injective map into an MF group would make `G` itself MF
    exact absurd
      (((isCDEOperatorMF_iff_isOperatorMF G).mpr
        (((isCDEOperatorMF_iff_isOperatorMF H).mp hH).comap f
          ((MonoidHom.ker_eq_bot_iff f).mp hbot)))) hnot
  · have hg : g ∈ f.ker := by rw [htop]; exact Subgroup.mem_top g
    exact MonoidHom.mem_ker.mp hg

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
