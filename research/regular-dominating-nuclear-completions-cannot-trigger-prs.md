---
rg: 2
id: regular-dominating-nuclear-completions-cannot-trigger-prs
kind: claim
title: A nuclear representation completion dominating the regular representation can never trigger the PRS obstruction
distinct_from:
  kazhdan-complement-llp-does-not-weaken-full-llp: that shows one nonnuclear proper completion has exactly the same LLP gate as the full algebra; this excludes the much larger shortcut class obtained from nuclear algebras with automatic LLP.
  regular-dominating-quotients-preserve-amenable-subgroup-algebras: that proves local faithfulness on amenable subgroup algebras for every regular-dominating completion; this uses nuclearity to force amenability of the whole group and hence amenability of every representation.
---

Let `pi` be a unitary representation of a discrete group `G` and assume

```text
lambda_G prec pi,
C^*_pi(G) is nuclear.                                      (RDN1)
```

**THEOREM.**  Then `G` is amenable and `pi` is an amenable
representation.  In particular `(RDN1)` can never satisfy the
nonamenability hypothesis in Paulsen--Rahaman--Samei Theorem 4.6.

**Proof.**  Weak containment supplies a surjective star homomorphism

```text
C^*_pi(G) -> C^*_r(G).                                    (RDN2)
```

Nuclearity passes to C-star quotients, so `C^*_r(G)` is nuclear.  The
Lance theorem then makes `G` amenable.  Every unitary representation of
an amenable group is amenable in Bekka's sense, so `pi` is amenable.

**Search consequence.**  Nuclear algebras have LLP automatically, but
they cannot supply the new exotic-LLP endpoint.  This rules out as direct
PRS candidates all Cuntz, graph-algebra, amenable-crossed-product, and
other nuclear representation completions, even when a group embeds in
their unitary group.  The required completion must be a genuinely
nonnuclear positive LLP example; moreover it must have no amenable trace
(Paulsen--Rahaman--Samei Corollary 4.2).  Thus the familiar abundance of
nuclear LLP algebras does not make the exotic route easy.
