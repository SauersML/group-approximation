---
rg: 2
id: bh-implies-pbh-iff-fp-simple-groups-satisfy-pbh
kind: claim
title: Boone--Higman implies permutational Boone--Higman exactly when every finitely presented simple group embeds in a finitely presented simple highly transitive group
distinct_from:
  permutational-boone-higman-conjecture: that is the universality conjecture over all decidable groups; this is the equivalence between the groupwise implication BH to PBH and a statement about finitely presented simple groups only.
  fp-simple-groups-embed-in-fp-simple-mif-groups: that is BFFHZ Question 3.4, the MIF form; this shows a positive answer to it is necessary as well as sufficient for BH to imply PBH.
  fp-simple-highly-transitive-groups-satisfy-pbh: that is BFFHZ Theorem C, the characterization of PBH for one group; this applies it to the whole class of finitely presented simple groups.
artifacts:
  - research/artifacts/ideas-2026-09-13/bh/bh-abstraction.md
---

**ESTABLISHED** through `bh-implies-pbh-iff-fp-simple-groups-satisfy-pbh-proof`.

The following are equivalent:

1. every finitely generated group with solvable word problem that satisfies
   Boone--Higman (BH) also satisfies permutational Boone--Higman (PBH);
2. every finitely presented simple group satisfies PBH;
3. every finitely presented simple group embeds in a finitely presented simple
   highly transitive group;
4. every finitely presented simple group embeds in a finitely presented simple
   mixed-identity-free (MIF) group, i.e. BFFHZ Question 3.4 has a positive answer.

**Credit.** This is Belk--Fournier-Facio--Hyde--Zaremsky's own framing, stated
here in both directions. From arXiv:2503.21882v2, extracted PDF text on MSI
(`bh-reviewer/2503.21882.txt`), l.146--150: "A fundamental question in this
context is whether BH and PBH are equivalent, which amounts to determining
whether every finitely presented simple group satisfies PBH". After their
Question 3.4 (l.721--723, "Does every finitely presented simple group embed in a
finitely presented simple MIF group?") they write (l.724--726): "If the answer
is yes, then BH is equivalent to PBH, and finitely presented twisted
Brin–Thompson groups are universal among finitely presented simple groups. If
the answer is no, then PBH is false." The equivalence of (2), (3) and (4) is
their Theorem C. No novelty is claimed.

**What the node adds to the graph.** The implication BH to PBH is not merely
implied by a positive answer to Question 3.4; it is equivalent to it. So any
proof of BH to PBH must answer Question 3.4, and a finitely presented simple
group with no finitely presented simple MIF overgroup would refute PBH.

**Known finitely presented simple groups that pass** (BFFHZ Remark 3.5):
- Thompson's group T: not MIF, but T embeds in V, which is highly transitive;
- all finitely presented simple groups of homeomorphisms of the Cantor space
  containing the commutator subgroup of some Higman--Thompson group, including V
  and finitely presented Rover--Nekrashevych commutator subgroups;
- twisted Brin--Thompson groups;
- the finitely presented simple Burger--Mozes groups
  (`burger-mozes-simple-lattices-are-highly-transitive`).

**Open test case.** Per BFFHZ (l.762--765) the only known source of finitely
presented infinite simple groups for which PBH remains open is non-affine
Kac--Moody groups over finite fields: `fp-simple-kac-moody-lattices-are-highly-transitive`.
