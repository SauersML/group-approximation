---
rg: 2
id: bffhz-envelope-closes-exact-actor-host
kind: claim
title: A finitely presented BFFHZ action image closes the exact expanding-character actor host
distinct_from:
  bffhz-action-image-is-finitely-presented: that asks only for finite presentation of the faithful automorphism-action image; this proves that a positive answer supplies the exact groupification half of the expanding-character route.
  sharp-two-t-actor-gives-fp-host: that asks the property-T group itself to be finitely presented and sharply two-transitive; this permits a larger finitely presented highly transitive envelope containing the property-T group.
---

Let `S` be an infinite finitely generated simple property-`(T)` group, take
`n>=2`, and use the BFFHZ action

```text
B=Aut_S(S*F_n)/K   acting faithfully on
X=Hom_S(S*F_n,S) ~= S^n.                               (BFE1)
```

Assume `B` is finitely presented.  Then the binary permutational lamp group

```text
W=C_2^(X) semidirect B                                  (BFE2)
```

is finitely presented, and it has a two-point seed `m_0` satisfying the
aperiodic property `(ICA1)` with a uniform gap supplied by the embedded copy
of `S`.

Indeed `relative-automorphism-action-is-highly-transitive` gives finite
pair-orbit count and finitely generated point stabilizers, so the generalized
permutational-wreath criterion proves finite presentation of `(BFE2)`.
The same theorem says that the translation copy

```text
S <= B
```

acts freely on `X`.  Choose `p in X`, `1!=s_0 in S`, put

```text
q=s_0 p,                 m_0=delta_p+delta_q.             (BFE3)
```

If a character/coloring `chi in (C_2^(X))^` has finite `B`-orbit, it has
finite `S`-orbit.  Simplicity gives no proper finite-index subgroup, so
`chi` is `S`-invariant.  Since `p,q` lie in one `S`-orbit,

```text
chi(m_0)=+1.                                               (BFE4)
```

Thus every seed-visible character has infinite `S`-orbit.  Property `(T)`
of `S` gives one uniform `ell^2` Schreier gap on all those orbits.

Adjoin involutions `z,J`, centralize `J`, and impose

```text
[m_0,z]=J.                                                 (BFE5)
```

The resulting group is finitely presented, `J!=1` in the
character-translation representation, and every exact finite-dimensional
representation kills `J` by `infinite-character-actor-kills-fd-mark`.

Therefore the already-isolated claim
`bffhz-action-image-is-finitely-presented`, applied to an effective
André--Guirardel property-`(T)` simple group, is a precise algebraic closure
of the actor-word lane.  It does not prove normalized-HS same-basis rounding.

## Attempts

- **Higman-embed the action image.**  This embeds the abstract group but the
  induced coset action generally has infinitely many double cosets, so the
  lamp commutators no longer have finitely many orbit relators.
- **Use the direct André--Guirardel lamp action.**  This dies by
  `direct-sharp-actor-wreath-forces-actor-fp`: killing the root lamp would
  finitely present an actor for which no finite presentation is known.
- **Deferred gate.**  Proving `bffhz-action-image-is-finitely-presented`, or
  finding another fp faithful action envelope with finite pair orbits and
  finitely generated stabilizers, is exactly the remaining algebraic attack.
