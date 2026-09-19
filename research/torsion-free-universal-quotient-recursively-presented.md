---
rg: 2
id: torsion-free-universal-quotient-recursively-presented
kind: claim
title: The torsion-free universal quotient exists and is recursively presented
distinct_from:
  torsion-free-higman-embedding: that claim embeds a recursively presented torsion-free group into a finitely presented one and changes the group; this one quotients an arbitrary group onto its universal torsion-free quotient and produces no embedding. They come from the same paper and are used together, but neither implies the other.
  defect-normally-generates-torsion-free-quotient: that is a statement about the defect subgroup of a specific construction in this program normally generating a torsion-free quotient; this is the general existence and effectivity of the universal torsion-free quotient functor.
  whitehead-vanishing-recursively-presented-torsion-free: that is a Whitehead vanishing statement quantified over recursively presented torsion-free groups and is open; this is the construction that produces such groups, contains no K-theory, and is established from Chiodo Proposition 3.8.
  torsion-free-finitely-presented-non-mf: that is this program's root asserting a finitely presented torsion-free non-MF group exists; this is a construction producing torsion-free quotients with no approximation property in it, and it neither needs nor provides finite presentation.
  universal-mf-quotient: that is the universal MF quotient -- the quotient by the MF radical, an operator-algebraic construction; this is the universal torsion-free quotient, the quotient by the torsion-free radical. Same "universal quotient by a radical" shape, different radicals and different subjects, and neither is a special case of the other.
artifacts:
  - research/artifacts/whitehead-vanishing-audit-2026-08-17.md
---

Every group `G` has a universal torsion-free quotient `G^tf`: a surjection
`G -> G^tf` with `G^tf` torsion-free, through which every homomorphism from
`G` to a torsion-free group factors uniquely.  Concretely
`G^tf = G / Tor_oo(G) = G / rho(G)`, where `rho(G)` is the torsion-free
radical and

    Tor_0(G) = 1,
    Tor_{i+1}(G) = << { g : g Tor_i(G) is torsion in G/Tor_i(G) } >>,
    Tor_oo(G) = union_i Tor_i(G).

Moreover the construction is **effective**: there is a uniform algorithm
taking a countably generated recursive presentation `P = <X|R>` of `G` and
outputting a countably generated recursive presentation `P^tf = <X|R'>` of
`G^tf` on the same generating set, with `R` contained in `R'`.  In
particular `G^tf` is recursively presented, and finitely generated whenever
`G` is.

Chiodo, arXiv:1107.1489v4: Definition 3.1, Lemma 3.2, Proposition 3.3,
Corollary 3.4 for the universal quotient; Lemmas 3.5--3.7 for the r.e. bound;
Proposition 3.8 for the algorithm.  Read from source this session, quoted in
the audit artifact.

Used by `whitehead-vanishing-recursively-presented-torsion-free`, whose whole
mechanism is that a finitely presented group built from a finite
multiplication table has a recursively presented torsion-free quotient that
still maps to the original torsion-free group.  Note the direction that makes
it work: the universal property gives a map *out* of `G^tf` toward any
torsion-free target, which is the arrow a functorial `K`-theory argument
needs and which no embedding statement provides.
