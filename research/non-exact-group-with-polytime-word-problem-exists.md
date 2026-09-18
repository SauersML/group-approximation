---
rg: 2
id: non-exact-group-with-polytime-word-problem-exists
kind: claim
title: Some finitely generated non-exact group has word problem solvable in polynomial time
distinct_from:
  decidable-graphical-non-exact-groups-exist: that gives non-exact groups with solvable word problem, but only through brute-force labellings with no useful time bound; this asks for a polynomial-time algorithm.
  every-cocf-group-is-exact: that is the claim a non-exact subgroup of V would refute; every coCF group has cubic-time word problem, so this claim is a necessary first step toward such a refutation, and it is strictly weaker.
---

**OPEN.** There is a finitely generated group `G` without property A whose word problem
can be decided in time polynomial in the length of the word.

## Why it matters

- **Necessary for non-exact subgroups of `V`.** Every finitely generated subgroup of `V`
  is coCF (`every-cocf-group-is-exact`), so its word problem is decidable in cubic time,
  by context-free recognition of the co-word problem. A non-exact subgroup of `V`, which
  would show `V` is not exact, would witness this claim. The same holds for any finitely
  presented simple host with a polynomial-time word problem, for example `T`, `V`, and
  the finitely presented Röver--Nekrashevych groups.
- **The known decidable non-exact groups don't give it.** Those are Osajda's groups
  (`decidable-graphical-non-exact-groups-exist`, `decidable-residually-finite-non-exact-group-exists`).
  They are built from labellings found by brute-force or Lovász-local-lemma search, and
  Dehn's algorithm for them must read components with exponentially many vertices in
  `|w|`.

## A pointer

Darbinyan, *The word and conjugacy problems in lacunary hyperbolic groups*, arXiv:1708.04591 (abstract only, via the arXiv API), builds lacunary hyperbolic "monsters" with almost linear-time word problem. Examples are torsion-free Tarski monsters and verbally complete groups. They use classical graded small cancellation with few relators per stage, so they do not carry expanders or large-girth graphs, and they are not known to be non-exact. The obstacle here is specific to graphical families: each component has exponentially many cycles.

## Route

`polytime-non-exact-group-via-decodable-labellings` reduces this claim to two algorithmic
properties of one labelled large-girth family, each checked on single components:
- *decoding*: from a long label word, find a path carrying it;
- *short complements*: between two given vertices, find a path shorter than a given bound
  when one exists.
That route's theorem is `decodable-small-cancellation-families-give-polytime-wp`.

## Attempts

1. **Congruence Cayley graphs of `SL_2(F_p)` (bh-graphical-sc, 09-18).** Take Sanov
   generators `A = [[1,2],[0,1]]`, `B = [[1,0],[2,1]]`, which are free in `SL_2(Z)`.
   Elementary facts:
   - *Girth.* Split a closed word of length `ℓ` in half. If `2·3^(ℓ/2) < p`, the two
     halves have equal integer lifts, so the girth is at least `2 log_3(p/2)`.
   - *Short complements for `ℓ < log_3(p/2)`.* A path shorter than that has an integer
     value with entries `< p/2`. So it is the centred lift of its value mod `p`, and
     ping-pong in `<A,B>` recovers its word in polynomial time.
   - *Long complements.* If `ℓ` exceeds `C·log p`, where `C` is the length constant of a
     polynomial-time lifting procedure from `SL_2(F_p)` into `Γ(2)` with entries
     `poly(p)`, then any lift gives a path of length `≤ C log p`. Such procedures are the
     classical attacks on the Zémor and Tillich--Zémor hash functions. This part is
     heuristic and not proved here.
   - *The gap.* Complements of length between `log_3 p` and `C log p` amount to finding
     a lift of prescribed small norm in a congruence class of `SL_2(Z)`. No polynomial
     algorithm for this is known here: it is the preimage problem for the
     Tillich--Zémor-type hash functions. Greendlinger faces can have complements in
     exactly this range.
   - *Decoding and component separation* (colours distinguishing different `p`) were not
     designed. Stalled.
2. **General obstruction to this method.** The short-complement property must work at the
   diameter scale of each component. Every graph of girth `g` and minimum degree `≥ 3` has
   at least `2^(g/2)` vertices. So this property amounts to near-geodesic computation in
   exponentially large large-girth graphs, which is hard for the known expander-type
   Cayley families. Families with large girth and efficiently computable geodesics are
   what is needed; none is known here.
