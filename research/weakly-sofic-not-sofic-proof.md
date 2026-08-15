---
rg: 2
id: weakly-sofic-not-sofic-proof
kind: route
title: Combine Glebsky's weak-soficity permanence with the Kun--Thom wreath
target: weakly-sofic-not-sofic
requires: [kun-thom-nonsofic-wreath]
---

Two verified primary sources compose.

**Permanence.** Glebsky, *Extensions of a residually finite group by a
weakly sofic group are weakly sofic*, Rev. Mat. Iberoam. 39 (2023), no. 3,
1097--1104, doi:10.4171/RMI/1368 (open access; read from the published PDF):

> **Theorem 1.1.** Let `H` be a normal subgroup of a group `K`.  If `H` is
> weakly sofic and `G=K/H` is residually finite, then `K` is weakly sofic.

The paper states the corollary explicitly: "In particular,
residually-finite-by-residually-finite extensions are weakly sofic."  See
also the earlier preprint arXiv:1910.08631, *Extension of a residually
finite group by a residually finite group is weakly sofic*.

**Application.** Take `W=(directSum_(G/Gamma) Z/2Z) semidirect G` for the
Kun--Thom pair.  Put `H=directSum_(G/Gamma) Z/2Z`, so `W/H = G`.

- `H` is a restricted direct sum of finite groups, hence residually finite,
  hence sofic, hence weakly sofic.
- `G=EL_r(R) semidirect SL_d(Z)` is residually finite by Kun--Thom
  Theorem E.

Glebsky's Theorem 1.1 therefore makes `W` weakly sofic.  Kun--Thom
Theorem A makes `W` nonsofic.  Hence weak soficity does not imply
soficity.  End proof.

## Provenance note

This deduction is recorded on Fournier-Facio's homepage
(`https://www.fffmaths.com/`) as a consequence of the August 2026 results —
"This also shows that there are weakly sofic groups that are not sofic,
clarifying the relationship between soficity and the other approximation
properties for which non-examples are still to be found" — without a proof
or a citation for the permanence step.

An exhaustive search (2026-08-14) found the deduction **in no paper by
anyone**: "weakly sofic", "Glebsky", "hyperlinear" and "bi-invariant" all
occur zero times in the full PDF of Fournier-Facio arXiv:2608.02025;
"weakly sofic" and "bi-invariant" occur zero times in the full PDF of
Kun--Thom arXiv:2608.06222; and none of Fournier-Facio's fifteen most recent
arXiv abstracts (through 2026-08-03) mentions weak soficity.

So the homepage sentence is an unsupported-in-the-literature remark and must
not be cited as literature.  The claim it asserts is nevertheless true, and
the composition above establishes it from two primary sources that were
read: cite Glebsky (RMI 2023) and Kun--Thom Theorem A, never the homepage.
