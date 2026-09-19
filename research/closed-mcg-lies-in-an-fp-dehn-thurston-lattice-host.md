---
rg: 2
id: closed-mcg-lies-in-an-fp-dehn-thurston-lattice-host
kind: claim
title: For g ≥ 2 some finitely presented group D between D_g = ⟨Φ Mod(S_g) Φ^-1, Z^N⟩ and Sym(Z^N), N = 6g − 6, has finitely generated point stabilizers; the natural candidate is the piecewise-affine lattice group PAff_N(Z)
distinct_from:
  rational-projective-full-groups-are-finitely-presented: that is R1's gate, finite presentation of the full group on the ray sphere; this is finite presentation of a lattice host whose behaviour at infinity is of R1's kind, together with a Houghton-type bounded layer.
  mapping-class-ports-are-dehn-thurston-translations-not-twists: that builds D_g and proves the port and stabilizer conditions; this is the one remaining finiteness gate.
  decidable-groups-embed-in-abelian-cofinite-hosts: that is the one-dimensional Higman problem for all decidable inputs; this is its instance at closed mapping class groups, with an explicit port.
---

**OPEN** (posed by lane bh-invent-02, 2026-09-19).

**Statement.** Let `g ≥ 2`, `N = 6g − 6`, and let `Φ`, `T ≅ Z^N` and `D_g` be as in
`mapping-class-ports-are-dehn-thurston-translations-not-twists`. Then some finitely presented `D`
with `D_g ≤ D ≤ Sym(Z^N)` has finitely generated point stabilizers.

**Why it matters.** `T ≤ D` is then a regular port, so `D` is an abelian-cofinite host. By
`cofinite-abelian-subgroups-give-relative-pbh`, `Mod(S_g)` and all its subgroups satisfy relative PBH
(route `closed-mcg-relative-pbh-via-dehn-thurston-lattice-port`).

**The candidate `D = PAff_N(Z)`.**
- It contains `D_g`, `GL_N(Z)`, `Z^N ⋊ GL_N(Z)` and `FSym(Z^N)`.
- Its elements induce, at infinity, rational piecewise-`GL_N(Z)` maps of the ray sphere
  `S^{N−1}`. These are the maps of R1's host `𝒯_{N−1}` (`closed-mcg-embeds-in-rational-projective-full-group`).
- Its bounded-displacement part consists of polyhedral piecewise translations. This part is
  Houghton-like and, for `N = 2`, not finitely generated.

**Calibrations.**
- `N = 1` fails: `PAff_1(Z) = H_2 ⋊ Z/2` is not finitely presented. This is item 4 of the
  source node.
- **First test:** is `PAff_2(Z)` finitely presented? Its behaviour at infinity is governed
  by R1's `𝒯_1`, which is finitely presented, and in the source node's words it is the
  analogue of Brown's `H_n` for `n ≥ 3`.
- A positive answer at `N = 2` would give no mapping class group. It would, however, test
  the Houghton-over-`𝒯` finiteness mechanism before rank `6g − 6`.
