# Verification record: Shulman, *The MF property for amalgamated free products*

arXiv:2603.13564v2, 22 Mar 2026 (paper dated March 24, 2026), Tatiana Shulman.
Read from the PDF this session (cairn-quotient-mf, 2026-08-14): abstract,
introduction, and Section 2.1--2.2.  Statements below are transcribed
verbatim from the introduction; the numbering in parentheses is the paper's
own forward reference to the body.

## Abstract (verbatim)

> A C*-algebra (or a group) is called MF (matricial field) if it admits
> finite dimensional approximate unitary representations which are
> approximately injective, where approximately is meant with respect to the
> operator norm.  It is proved that for any MF C*-algebra `A` and its
> C*-subalgebra `C`, `A *_C A` is MF.  For general amalgamated free products,
> `A *_C B`, a necessary and sufficient condition for being MF is given.  It
> is shown that the following groups -- amalgamated free products of amenable
> groups, semidirect products of amenable groups by free groups, and
> `Z^2 x| SL_2(Z)` -- all have MF full group C*-algebra.  It is shown that
> the class of MF C*-algebras is closed under maximal tensor products with
> `C*(F_n)`.

## Theorem 10 (verbatim)

> Let `A` be a separable MF C*-algebra and let `C` be any C*-subalgebra of
> `A`.  Then `A *_C A` is MF.

## Theorem 20 (verbatim) — the general criterion

> Let `A, B, C` be separable C*-algebras and `theta_A : C -> A`,
> `theta_B : C -> B` be inclusions.  Then `A *_C B` is MF if and only if
> there exist embeddings `phi_A : A -> prod M_n / (+) M_n` and
> `phi_B : B -> prod M_n / (+) M_n` such that
> `phi_A o theta_A = phi_B o theta_B`.

Attribution recorded in the same paragraph: for `A *_F B` with `F` a common
**finite-dimensional** C*-subalgebra the condition is due to Li and Shen;
Shulman proves the same condition stays necessary and sufficient for
arbitrary amalgamated subalgebras.  Hadwin--Li--Shen proved free products of
MF C*-algebras are MF; Li--Shen proved `A *_F A` MF for `A` separable MF and
`F` finite-dimensional.

## Other statements read

- **Theorem 23.**  If `G_1` and `G_2` are amenable groups and `H` is their
  common subgroup, then `C*(G_1 *_H G_2)` is MF.
- **Corollary 34.**  `C*(Z^2 x| SL_2(Z))` is MF.
- **Corollary 35.**  For any semidirect product `G x| F_n` of an amenable
  group `G` by a free group `F_n`, `C*(G x| F_n)` is MF.
- **Theorem 28 / Theorem 29.**  MF C*-algebras are closed under maximal
  tensor products with `C*(F_n)`, and under **central** HNN-extensions.
- **Section 2.1**, closing sentence: the C*-algebraic and group-theoretic
  amalgamated free products agree, `C*(G_1 *_H G_2) = C*(G_1) *_{C*(H)} C*(G_2)`.
- **Definition 2.**  A C*-algebra is MF if it embeds into
  `prod M_n / (+) M_n`.
- **Introduction, group bridge:** "Since a discrete group `G` embeds into
  `C*(G)` and `C*_r(G)`, there is the following connection between the
  C*-algebraic MF property and the group theoretic one: if either `C*(G)` or
  `C*_r(G)` is MF, so is `G`."

## Priority datum

The introduction states, as of March 2026:

> There are no examples of groups whose full or reduced C*-algebra is not
> MF, and at the same time there are not so many examples of non-amenable
> groups whose C*-algebras are known to be MF, at least in the case of full
> group C*-algebras.

This repository's Theorem A supplies exactly such an example (`E`, and the
witness `W`, for which neither the full nor the reduced group C*-algebra is
MF).  Flagged for `notes/CREDIT_AND_PRIORITY_AUDIT.md`; not acted on here.

Quote discipline: the sentence must be taken from this file, not from any
message quoting it — the trailing clause "at least in the case of full group
C*-algebras" is part of it and a truncated version misstates the record.  And
the defensible phrasing downstream is "Shulman records in March 2026 that no
such example was known", not "no such example existed": this is one author's
introduction, not a survey or a non-existence proof.  The dating is what
carries the weight.

One-step derivation of the C*-level statement (cairn-archivist).  The
parenthetical above needs none of this repository's separate reduced-algebra
work.  Contrapose the bridge lemma transcribed above — if `C*(G)` or
`C*_r(G)` is MF then `G` is MF — against `literal-group-fails-mf-conventions`,
which is established in exactly the CDE operator-norm group convention that
Shulman uses.  Every step is then either Theorem A or a sentence from the
paper being answered.

## Scope caution

Theorem 20 is a statement about **C*-algebras**.  Group MF in the
Carrion--Dadarlat--Eckhardt sense used by this repository is weaker than
MF of `C*(G)`; the implication runs `C*(G)` MF `=>` `G` MF and not back.
Any route built on Theorem 20 therefore proves more than the group claim
needs, and inherits the requirement that both vertex algebras be MF.
