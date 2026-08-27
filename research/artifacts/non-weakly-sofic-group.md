# There exists a group that is not weakly sofic

Former Cairn claim `non-weakly-sofic-group`, demoted because the document
explicitly identifies this famous open problem as an adjacent landmark, not
a goal of the present program.

There is an abstract discrete group admitting no `(Phi,eps,alpha)`-model into
finite groups with bi-invariant metrics, for any fixed `alpha>0`.  This is
Glebsky--Rivera Conjecture 4.5.  **OPEN as of 2026-08-17.**

Weak soficity is the weakest finite approximation property in play in this
graph: sofic implies weakly sofic, residually finite implies weakly sofic,
and by Glebsky's 2023 permanence theorem weakly-sofic-by-residually-finite
extensions stay weakly sofic.  So a non-weakly-sofic group would be a strictly
larger landmark than a nonsofic one, and no group currently known to this
corpus is a candidate.

## Status, and why it is not settled by August 2026's nonsofic results

Nonsofic groups now exist unconditionally, and the corpus carries them
(`openai-leavitt-unit-nonsofic` first, then `kun-thom-nonsofic-wreath`, and
`nonsofic_groups_exist` in `Endpoint/MainResults.lean` independently of
both); Fournier-Facio, *A torsion-free non-sofic
group*, arXiv:2608.02025 (2026-08-04), even gives a finitely presented
torsion-free one.  **None of this bears on weak soficity**, and the corpus
already proves why: `weakly-sofic-not-sofic` shows the Kun--Thom wreath
product is weakly sofic and nonsofic, so the nonsofic endpoint cannot be
promoted by renaming its target.  See
`weak-soficity-survives-every-corpus-obstruction` for the full list of
obstructions in this repository that a weakly sofic group already realizes.

## Not this program's goal, and not root-marked

Recorded because the corpus repeatedly gestures at it — the `WeakSoficModel`
name in `Sofic/SoficAmplification.lean`, the finite-quotient kill theorem for
`E`, the finite quasi-identity, the Clifford wall — and every one of those
gestures is refuted (see `weak-soficity-survives-every-corpus-obstruction`
and `literal-mark-conjugacy-width-unbounded`).  Having the target as a node
with its exact certificate attached is what stops the gestures recurring.

It is deliberately **not** marked `root: true` or `goal: true`: it is an
adjacent landmark, not one of `q3-4-resolved`'s two answers, and goal
selection is a user decision.

## The only admissible route

`non-weakly-sofic-from-word-certificate`.  There is no known second mechanism.
In particular the following are **not** admissible and must not be added as
routes; each is refuted, with the counterexample named:

```text
non-MF                       => non-weakly-sofic     FALSE (E is sofic)
nonsofic                     => non-weakly-sofic     FALSE (Kun--Thom wreath)
non-residually-finite        => non-weakly-sofic     FALSE (E)
mark dies in every finite Q  => non-weakly-sofic     FALSE (E's mark)
violates a finite quasi-id.  => non-weakly-sofic     FALSE (E's quasi-identity)
abstract Clifford wall       => non-weakly-sofic     FALSE (E_S is weakly sofic)
```
