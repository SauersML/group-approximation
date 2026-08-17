---
rg: 2
id: glebsky-rivera-w-sofic-criterion-citation
kind: route
title: Read the 2008 Glebsky--Rivera paper and reconstruct both directions of Theorem 4.3
target: glebsky-rivera-w-sofic-criterion
requires: []
artifacts:
  - research/artifacts/non-weakly-sofic-audit-2026-08-17.md
---

Two independent passes, both recorded in the artifact.

**Pass 1 — reconstruction.**  An external audit delivered 2026-08-17 proves
the criterion from scratch, without consulting the source, as its Lemma 2.2
(weak soficity `<=>` finite separability of `N`) plus Lemma 2.3 (finite
separability `<=>` the closure condition).  Sections 1--3 of the artifact
carry both proofs in full, including the capped-length construction and the
`3R` word-length budget in the converse.

**Pass 2 — source verification.**  arXiv:0709.0026v2 (the arXiv version of
J. Algebra **320** (2008), no. 9, 3512--3518) was fetched and read in full on
2026-08-17.  Verbatim:

> **Definition 4.1** A group `G` is called w-sofic if there exists `alpha>0`
> such that for any finite set `Phi subset G`, for any `epsilon>0` there
> exists a finite group `H` with a bi-invariant metric `d` and a
> `(Phi,epsilon,alpha)`-homomorphism to `(H,d)`.

> **Remark 4.2** In Definition 4.1 we do not ask the metric to be normalized.
> So, `alpha` may be any fixed positive number.

> **Theorem 4.3** Let `F` be a finitely generated free group and `N normal F`.
> Then `F/N` is w-sofic if and only if for any finite sequence
> `g_1,g_2,...,g_k` from `N` one has
> `closure([g_1]^F[g_2]^F...[g_k]^F) subseteq N`.

The paper's Definition 3.1 is the `(Phi,eps,alpha)`-homomorphism used above,
and its Section 6 proves Theorem 4.3 through Definition 6.1 (`N` is
`(r,eps,delta)`-separated by `phi`; `N` **finitely separable** if some
`delta>0` works for all `r` and all `eps`), Lemma 6.2 (`F/N` w-sofic iff `N`
finitely separable) and Lemma 6.4 (finitely separable iff the closure
condition).  Those are exactly the audit's Definition 2.1, Lemma 2.2 and
Lemma 2.3, so the two passes agree line for line on the architecture.  The
only difference is presentational: the paper's invariant length is built from
a **conjugacy class graph** `Gamma(G,C)` (Section 5, item III) with
`d(x,e)=eps*||x||_C` and `k > alpha/eps`, whereas the audit caps and rescales
directly as `min{L_C(h)/n,1}`.  Same object; the graph already carries it
from the 2017 paper as `glebsky-manufactured-invariant-length`.

Also read and recorded, because downstream nodes use them:

> **Corollary 4.4** If there exists a non w-sofic group then there exists a
> finitely presented non w-sofic group.

> **Conjecture 2.1** For a finitely generated free group `F`, there exists a
> sequence `g_1,g_2,...,g_k in F` such that
> `closure([g_1]^F[g_2]^F...[g_k]^F) not-subseteq N(g_1,g_2,...,g_k)`.

> **Conjecture 4.5** There exists a non w-sofic group.

> **Corollary 4.6** Conjecture 4.5 and Conjecture 2.1 are equivalent.

> **Corollary 4.7** The group `F/N` is w-sofic iff `N = Nhat cap F` and the
> group `F/N` is residually finite iff `N = Ntilde cap F`.

(`Nhat` = the minimal normal subgroup of the profinite completion `Fhat`
containing `N`; `Ntilde` = the closure of `N` in `Fhat`; `Nhat <= Ntilde`,
with equality iff `Nhat` is closed.  This is the clean reason residual
finiteness implies weak soficity and not conversely.)

> **Remark 4.8** Let `S = [g_1]^Fhat[g_1^(-1)]^Fhat ... [g_k]^Fhat[g_k^(-1)]^Fhat`.
> Then `Nhat(g_1,...,g_k) = union_(n=1)^infinity S^n`.  So,
> `Nhat(g_1,...,g_k)` is a closed set if and only if
> `Nhat(g_1,...,g_k) = S^n` for some `n`, due to the fact that `S` is a
> compact set.

Remark 4.8 is worth flagging: in the completion, **closed = bounded conjugacy
width**.  That is why no compactness argument can upgrade "every finite
quotient expresses `q(x)` with *some* number of conjugates" to a fixed
number — the upgrade is the open problem.

Note finally that Glebsky and Rivera *conjecture* the escape (Conjecture 4.5
is stated as an expectation, and they suggest Liebeck--Shalev diameters and
Nikolov--Segal I/II as the tools).  The source is not neutral on the
direction; `non-weakly-sofic-group` records that this is an expectation, not
evidence.
