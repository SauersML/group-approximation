# Surjunctive nonsofic groups: proof, literature, and credit review

Reviewed September 13, 2026 by Codex (AI review). Scope: the finitely generated
separation theorem in the withdrawn Palomar candidate
`6738ce3d092e23a5976f6d45042f4d92c12bf5b0`, and its written surjunctivity proof.

**Finding.** No mathematical defect was identified in the argument examined.
The previously completed Lean/NanoDa checks support the exact formal endpoint.
The literature search found no earlier group separation or prior permanence
theorem making it an immediate corollary. Bibliographic and historical claims
needed corrections, recorded below. These findings are bounded review results,
not a guarantee of error-free mathematics or absolute priority.

**Status.** Submission `5ad9mr3alq1c` is withdrawn and was never registered.
Reviewing or updating the preparation branch does not resubmit it.

## The question and its history

The question is: does there exist a surjunctive group which is not sofic?
The result gives a finitely generated example. It is the converse problem to
the sofic-implies-surjunctive theorem of
[Gromov (1999)](https://ems.press/journals/jems/articles/102) and
[Weiss (2000)](https://www.jstor.org/stable/25051326).

The earliest occurrence supported by this audit is **Ceccherini-Silberstein
and Coornaert, 2010, OP-11**. The evidence is retrospective but explicit:
their second edition, p. 527, says the listed questions appeared in the first
edition and retains OP-11. The original first-edition page was not retrieved.
See the [2010 publication record](https://doi.org/10.1007/978-3-642-14034-1),
[second edition](https://doi.org/10.1007/978-3-031-43328-3), and
[searchable reproduction of its text](https://dokumen.pub/cellular-automata-and-groups-2nbsped-9783031433276-9783031433283.html).
This does not establish who first posed the question, or rule out an earlier
appearance. Describe it as an older question recorded by these authors;
do not call Bowen and Chapman its original proposers.

Earlier sources checked include Gromov (1999), Weiss (2000),
[Ceccherini-Silberstein–Coornaert's 2006 survey, Section 2](https://www.mathnet.ru/php/getFT.phtml?jrnid=adm&paperid=254&what=fullt),
[Pestov's 2008 survey, Section 6](https://arxiv.org/abs/0804.3968), and
[Pestov–Kwiatkowska's 2009 notes, Section 8](https://arxiv.org/abs/0911.4266).
No explicit formulation of this converse was located in those sources.
Their statements of universal surjunctivity, nonsofic-group existence, or
the forward implication do not establish authorship of the converse.

[Arzhantseva–Gal, original preprint (December 30, 2013), p. 3](https://arxiv.org/pdf/1312.7682v1)
explicitly records the same unknown existence question.
[Bowen–Chapman (2025), Problem 1.1](https://arxiv.org/html/2511.06586v1)
restates the converse; their Theorem 1.2 concerns invariant random subgroups,
not a surjunctive nonsofic group.

[Gottschalk (1973), *Some general dynamical notions*](https://doi.org/10.1007/BFb0061728)
belongs in the historical credits for surjunctivity. His universal
surjunctivity question is a different problem. The present separation does
not answer it.

## Closest prior results and the apparent competing proof

**Arzhantseva–Gal.** The correct authors are Goulnara Arzhantseva and
Światosław R. Gal. The paper appeared in *Annales Mathématiques Blaise Pascal*
27(1) (2020), 125–130, after its 2013 preprint; 2014 was incorrect.
[Theorems 1 and 7](https://doi.org/10.5802/ambp.386) cover a split extension
with finitely generated residually finite kernel and surjunctive quotient.
The fold kernel of our double is free on the non-base cosets and has infinite
rank: the polynomial subgroup has infinite index in the Laurent ambient
group. For example, elementary matrices with coefficients x_1^(-n) give
distinct cosets. Thus the theorem's kernel hypothesis fails. Knowing only
that each finitely generated part of the kernel is residually finite does
not supply an invariant finite quotient for the whole action.

**Shahryari.** The abstract of *A note on surjunctive groups* can look like
the needed locally-finite-kernel permanence theorem. But
[v1, Theorem 1, p. 4](https://arxiv.org/pdf/2002.05352v1) explicitly makes
the surjunctive factor K normal and the locally finite factor H the actor.
Theorem 2 likewise has surjunctive kernel and locally finite quotient.
The lamp-wreath construction has the opposite arrangement. The author
[withdrew the preprint on February 23, 2020](https://arxiv.org/abs/2002.05352),
citing Arzhantseva–Gal's prior result. The withdrawal is not evidence that
the theorem is false; its actual hypotheses are what prevent its use here.

**Other nearby work.** Results about linear or additive cellular automata
do not establish full surjunctivity. For example,
[Bradford–Fournier-Facio](https://doi.org/10.1007/s00209-024-03589-3) study
Hopficity of wreath products and stable finiteness, including the relation
between additive and linear surjunctivity. That is not the arbitrary local
rule assertion proved here. Likewise, soficity of regular wreath products
does not cover an arbitrary nonsofic coset wreath or double.

## Proof review

Read in full:

- [Wreath-product proof](rf-lamp-wreath-surjunctivity-2026-09-11.md), including the finite-memory inverse lemma and the subset induction.
- [Finitary split-extension proof](finitary-split-extension-surjunctivity-2026-09-11.md), including the explicit double isomorphism and the noncommutative fiber extension.
- The candidate's exact-commit `Palomar/BowenChapmanSolution.lean` and `GroupApproximation/BowenChapman/Endpoint.lean`.

The following checks address the places where an apparent short proof could
silently assume soficity or use an invalid quotient.

1. **Coset models.** H is normal in the fold kernel N; it need not be normal
   in the whole semidirect product. The construction uses the right action
   on the set H\W, not a quotient group W/H. Pullback intertwines the
   automaton and transfers injectivity. Finite-pattern separation plus
   compactness transfers surjectivity back to W.
2. **Double kernel.** With e_(x_0)=1, the formula
   alpha_g(e_x)=e_(gx)e_(g x_0)^(-1) respects composition. The displayed
   maps between the double and the split extension are mutual inverses.
   Including x_0 in every word's support is essential. The stabilizer
   condition works both when x_0 belongs to S and when it does not.
3. **Fiber extensions.** Q_V need not be normal in Q_U. Acting separately
   on left cosets is well defined by fiber equivariance. These extensions
   preserve composition and inverses and are transitive. This justifies
   the passage from product fibers to noncommutative finite quotients of
   free groups.
4. **Subset induction.** Fix one order refining cardinality. Enlarge the
   observation window by the memories of all earlier corrections and
   their support windows. Outside the final intersection of enlarged
   strata, the active subset V is proper. Corrections indexed by subsets
   outside V fix the required coordinates. Corrections within V form
   rho_V, and the stage V cancels it. No commutativity of corrections is
   assumed. The shrinking windows are necessary for this argument.
5. **Final inverse.** The residual support is a finite union of right
   cosets of G_U. Add the finitely many boundary cosets read by the map
   as fixed tracks. This produces an injective cellular automaton over
   G_U with a finite alphabet. Subgroup surjunctivity gives its inverse;
   finite memory follows from the cellular-automaton characterization.
6. **Degenerate cases.** An empty alphabet gives an empty full shift over
   a group, so surjectivity is automatic. Handling this first makes the
   configuration-extension choices explicit. Empty support and repeated
   memory entries cause no difficulty.
7. **One witness throughout.** The checked endpoint uses q=2 and r=d=3
   in the Kun–Thom pair. The integral elementary actor equals SL_3(Z).
   Both copies of a finite generating set of G generate the double.
   No finite presentation assertion is part of this endpoint. The README's
   separate rank-six finite-presentation argument is outside this audit.
8. **Nonsoficity hypothesis.** Kun–Thom's normalization input is for free
   sofic representations, or the corresponding faithful asymptotic
   sequences. The earlier AI review identified the danger of replacing
   this with arbitrary injective representations. The checked endpoint
   uses the sequential normalization theorem; its final declarations have
   no remaining normalization hypothesis.

## Mathematical credit

| Ingredient | Credit and source |
| --- | --- |
| Previously constructed pair and nonsofic double | [Kun–Thom, Theorems A and E](https://arxiv.org/abs/2608.06222v3). Our contribution is its surjunctivity, not its construction or nonsoficity. |
| Centralizer normalization | Kun–Thom, Theorem 4.1, with the component machinery of [Alekseev–Thom](https://arxiv.org/abs/2608.05362). |
| Expander and almost-automorphism ancestry | [Kun, 2016 preprint, v5 (2019)](https://arxiv.org/abs/1606.04471v5); [Kun–Thom, 2019 preprint, v3 (2026)](https://arxiv.org/abs/1901.03963v3). These supplement the direct inputs. |
| Property (T) for the elementary groups | [Ershov–Jaikin-Zapirain (2010)](https://doi.org/10.1007/s00222-009-0218-2). |
| Residually finite groups are surjunctive; subgroup heredity | Wayne M. Lawton (1972), credited in *Cellular Automata and Groups*, Chapter 3 notes. |
| Local characterization and finite-memory inverse | Curtis–Hedlund–Lyndon; [Hedlund (1969)](https://doi.org/10.1007/BF01691062), with the arbitrary-group formulation in *Cellular Automata and Groups*. |
| New surjunctivity argument | The September 11 finitary split-extension and wreath-product artifacts linked above. |

Lawton's abstract has conflicting page references: Gottschalk's publisher
bibliography gives A-376, while Gromov and later authors give A375. The original
AMS scan could not be accessed during this audit. The metadata therefore
credits the author, title, year, and journal without asserting the page.
No claim of a personal acknowledgment or consultation with any cited author
is made. Existing Astra, Claude, and Codex process credits are separate from
these mathematical credits and from the human author's responsibility.

## Verification and remaining limits

At `6738ce3d092e23a5976f6d45042f4d92c12bf5b0`:

- [Comparator and NanoDa passed](https://github.com/SauersML/group-approximation/actions/runs/34785942633).
- [Submission, statement, and axiom checks passed](https://github.com/SauersML/group-approximation/actions/runs/34785945798).
- Both selected declarations have axiom closure exactly
  `[propext, Classical.choice, Quot.sound]`.

These are repository verification runs, not Palomar editorial acceptance.
The current pass read the recorded logs and source; it did not run Lean or
project code again. Documentation revisions preserve the mathematical source.
Any future submission must identify its actual commit and verification status.

Searches covered the exact converse question, surjunctive nonsofic groups,
OP-11, semidirect products, wreath products, doubles, and amalgams, followed
by reading the relevant primary statements and their hypotheses. The priority
comparison concerns literature available by the initial argument's commit
timestamp below, September 12 UTC (September 11 in Chicago).
No later independent solution is included in the account.

The written artifacts are dated September 11. GitHub records the initial
wreath-product argument in commit
[05a8aff7a](https://github.com/SauersML/group-approximation/commit/05a8aff7a5a8402f8e49a776384638b47a34c27d),
whose author and committer timestamp is September 12, 2026, 03:24:31 UTC
(September 11 in Chicago). The formal endpoint commit
[92ad0059d](https://github.com/SauersML/group-approximation/commit/92ad0059d60f813ad3e96a00c2345526f7c48c10)
is dated September 12, 22:43:09 UTC. These are commit timestamps, not
independent proof of when the commits first became publicly accessible.

The main unresolved historical point is the first proposer or an occurrence
before 2010. Lawton's abstract pagination also remains unverified. Neither
point is needed for the mathematical inference, and neither should be filled
in by guessing. No human expert review or exhaustive literature certification
is claimed.
