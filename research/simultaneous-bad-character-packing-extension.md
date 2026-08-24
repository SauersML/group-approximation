---
rg: 2
id: simultaneous-bad-character-packing-extension
kind: claim
title: One finite presentation simultaneously packs every forbidden character family
distinct_from:
  single-selected-atom-hs-escape: that chooses one maximal forbidden type inside a reached reducing carrier; this asks for one joint root-level orthogonality system and only more than 2/beta copies per type.
  finite-packet-functoriality-has-positive-regular-profile: that proves ordinary packet multiplicity relations retain a positive regular profile; this asks for literal products of transported idempotents to vanish, which constrains the intertwiners rather than only their multiplicities.
  amenable-edge-graph-corners-cannot-groupify-a-nonce-game: that rules out finite amenable-edge assembly as the first source of nonhyperlinearity; this explicitly requires a joint relation among different context transports and is not a graph of independent finite packet vertices.
  finite-character-hecke-intersection-formula: that gives the exact finite test for pairwise orthogonality of proposed transports; this asks for a joint presentation whose complete intersection-label system passes that test while retaining the prescribed trace.
---

**REFUTED.**  `canonical-trace-forbids-supercritical-character-packing`
gives the universal ceiling

```text
K<=2/beta
```

for the requested simultaneous family whenever the seed-context packet
subgroups embed.  The value in `(SBP2)` is strictly larger, so no such
ordinary group-algebra packing exists.

The former target fixed the robust shared contextual system, its finite Pauli seed,
and forbidden character idempotents

```text
e_i=Q_empty P_i,                    1<=i<=M.            (SBP1)
```

Construct one finite ordinary presentation extending the contextual words,
with a central involution `J`, and fixed words

```text
g_(i,r),                 1<=i<=M, 1<=r<=K,
K=floor(2/beta)+1,                                       (SBP2)
```

such that:

1. it has an exact finite-tracial representation extending the perfect
   contextual trace and sending `J` to `-1`;
2. every transported idempotent

   ```text
   p_(i,r)=g_(i,r)e_i g_(i,r)^(-1)
   ```

   lies below `(1-J)/2`; and
3. in the complex group algebra,

   ```text
   p_(i,r) p_(j,s)=0              whenever (i,r)!=(j,s). (SBP3)
   ```

Had these conditions been consistent, `simultaneous-character-packing-removes-max-loss`
would have implied nonhyperlinearity immediately.  The canonical trace shows
that the stated strict threshold is already inconsistent.

The relation `(SBP3)` must couple the different context transports on their
multiplicity spaces.  Separate finite overgroups amalgamated independently
along the context groups do not impose cross-family orthogonality.  A
solution would have required one joint holonomy or collision relation whose
perfect tracial representation is supported entirely away from the
forbidden family.  The ceiling theorem shows that such a relation cannot
retain the finite context packet embeddings assumed here.

By `finite-character-hecke-intersection-formula`, clause 3 is equivalent to
the following finite condition for every two distinct indices `(i,r)` and
`(j,s)`: the transported forbidden characters disagree on the intersection
of their transported context subgroups.  Hence a candidate can be audited
entirely from its finite subgroup-intersection table and character labels;
no separate operator-algebra estimate is needed for orthogonality.
