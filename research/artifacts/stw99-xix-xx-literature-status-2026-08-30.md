# STW Problems XIX and XX: current literature status (2026-08-30)

## Outcome

The two uniform-property-Gamma nodes have opposite answers in the current
primary literature.

* **Problem XIX is false.** Andrew S. Toms constructs a unital simple
  separable nuclear non-elementary AH algebra without uniform property Gamma.
* **Problem XX is true.** Andrea Vaccaro proves that the Villadsen algebras of
  the first type have uniform property Gamma.

These are status imports, not new proofs of the source theorems.  The Cairn
routes below record only the exact logical consequences of the cited results.

## Repository-first and novelty audit

Before importing either result, the canonical graph and prose corpus were
searched with `bin/cairn search --notes` and `rg` for the two titles, authors,
and arXiv identifiers `2606.12188` and `2604.24682`.  Cairn contained the two
STW problems and several internal sufficient conditions, but no mention of
either resolving preprint and no existing counterexample to Problem XIX.

The arXiv records expose the complete papers (including their final sections
and references) and list no supplementary computation or released source
code.  GitHub code searches for both identifiers and exact titles found no
mathematical implementation on which either theorem depends.  This is the
appropriate certificate boundary: both imports are theorem citations, not
computational-exhaustion claims.

## Problem XIX: Toms's counterexample

Primary source:

* Andrew S. Toms, *Schubert Calculus and uniform property Gamma*,
  [arXiv:2606.12188v2](https://arxiv.org/abs/2606.12188), revised
  2026-07-26.  See Theorem 1, Proposition 4, and especially Theorem 5.

Theorem 5 states that the simple point-evaluation limit `B` is a simple,
separable, unital, nuclear AH algebra without uniform property Gamma.
Proposition 4(1) records that the limit is non-elementary, and its proof
records that the connecting maps are injective.  The one hypothesis not
spelled out in the theorem's adjective list is automatic from the displayed
construction: every homogeneous building block

```text
s_i (C(X_i) tensor K) s_i
```

is stably finite, and stable finiteness passes to an injective inductive
limit.  Thus the source example has every hypothesis of Problem XIX:

| Problem XIX hypothesis | Toms's example |
| --- | --- |
| unital, simple, separable, nuclear | Proposition 4(1), Theorem 5 |
| non-elementary | Proposition 4(1), Theorem 5 proof |
| stably finite | injective AH limit of homogeneous stably finite blocks |
| uniform property Gamma | fails by Theorem 5 |

Theorem 1 and the introduction explicitly say that this resolves STW
Question XIX negatively.  No extrapolation from the geometric obstruction is
used in Cairn: the imported proposition is exactly the existence statement
proved in Theorem 5.

## Problem XX: Vaccaro's positive theorem

Primary source:

* Andrea Vaccaro, *Stable rank one, tracial local homogeneity and uniform
  property Gamma*, [arXiv:2604.24682v2](https://arxiv.org/abs/2604.24682),
  revised 2026-05-03.  See Theorem A and Corollary 4.1.

Theorem A states that every simple unital non-elementary AH algebra of stable
rank one has uniform property Gamma and names the non-elementary Villadsen
algebras of the first type as examples.  The introduction explicitly says
that the theorem solves STW Problem XX affirmatively.  It also records the
hypothesis match: AH algebras are locally homogeneous and the Villadsen
first-type algebras have stable rank one by Villadsen's Proposition 10.

Toms's later v2 introduction independently uses this status: it says that the
first Villadsen family has uniform property Gamma by Vaccaro, in contrast to
Toms's new higher-stable-rank AH counterexample.

## Version-conflict audit

The May 2026 v2 of Schafhauser--Tikuisis--White,
[arXiv:2506.10902](https://arxiv.org/abs/2506.10902), still contains an
addendum reporting a negative answer to XIX and XX from an early version of
Elliott--Niu, arXiv:2504.03611.  That is not the current source status.
Elliott--Niu's current
[v3](https://arxiv.org/abs/2504.03611), revised 2026-08-13, has a different
abstract and comments: the earlier equivalence with ambient uniform property
Gamma for diagonal AH algebras is no longer asserted.  Stale mirrors still
show the superseded abstract.  The later primary sources resolve the actual
statuses: Vaccaro proves XX positively, while Toms supplies a different AH
example proving XIX false.

## Residual trust boundary

Both resolving sources are current arXiv preprints rather than journal-final
versions.  Cairn therefore imports their stated theorems with exact version
dates and does not claim an independent verification of their long proofs.
The short hypothesis matching above is independent of those proofs.  Problem
XX cannot be used as the counterexample to Problem XIX; Toms's example has
stable rank strictly greater than one and supplies the separate refuter.
