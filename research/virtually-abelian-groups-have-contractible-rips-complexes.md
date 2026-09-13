---
rg: 2
id: virtually-abelian-groups-have-contractible-rips-complexes
kind: claim
title: Every finitely generated virtually abelian group has a contractible Rips complex
distinct_from:
  amenable-automatic-groups-have-contractible-rips-complexes: that is Zaremsky Problem 4.1 for all amenable automatic groups; this is its case for virtually abelian groups, the only amenable automatic groups known to this lane
  rips-complexes-of-integer-lattices-are-contractible: that is Virk's theorem for Z^n with its standard generators; this asks for some contractible Rips complex of every virtually abelian group, including those with torsion and nontrivial holonomy
---

**ESTABLISHED** (route `virtually-abelian-groups-rips-via-cat0`).

For every finitely generated virtually abelian group `G` there is a finite generating
set `S` such that `P_1(G,S)`, the flag complex of `Cay(G,S)`, is contractible.
Equivalently some Rips complex of `G` is contractible
(`rips-complex-of-a-group-is-a-flag-cayley-complex`).

Virtually abelian groups are amenable and automatic, so this is the case of
`amenable-automatic-groups-have-contractible-rips-complexes` for every example this
lane knows. With `amenable-automatic-groups-are-virtually-abelian` it would give that
claim (route `amenable-automatic-rips-via-virtually-abelian`).

Remarks:

- The proof goes through Zaremsky's orbit theorem for asymptotically CAT(0) spaces
  (arXiv:1812.10976v3, Proposition 6.1 and Theorem 6.2), which gives no explicit
  scale.
- A self-contained proof with explicit `l^∞` generating sets and every scale `c >= 4`
  holds when the point group consists of signed permutation matrices, glides and
  screws allowed (`linf-preserving-proper-actions-give-contractible-rips`). That
  covers the Klein bottle group and every 3-dimensional space group outside the
  trigonal and hexagonal systems.
- The stronger "type R" reading (a fixed generating set, all large scales) is not
  settled here for general virtually abelian groups. Li–Sánchez Saldaña
  (arXiv:2608.24279, Theorem 1.6) do `Z^n × F`.
