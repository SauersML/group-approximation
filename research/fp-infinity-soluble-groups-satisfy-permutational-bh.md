---
rg: 2
id: fp-infinity-soluble-groups-satisfy-permutational-bh
kind: claim
title: Every virtually soluble group of type FP_∞ lies in the permutational Boone--Higman class, and hence so does every elementary amenable group of type FP_∞
distinct_from:
  rf-soluble-minimax-groups-satisfy-permutational-bh: that assumes residual finiteness and finite Prüfer rank; this assumes only the homological finiteness condition FP_∞, and derives those hypotheses from the Kropholler structure theorem.
  fp-metabelian-groups-satisfy-boone-higman: that is finitely presented metabelian groups, of possibly infinite rank; this is soluble groups of any derived length under the stronger condition FP_∞.
  amenable-automatic-va-via-ea-and-soluble-case: that uses FP_∞ structure theory to reduce amenable automatic groups to the soluble case; this turns the same structure theory into Boone--Higman envelopes.
artifacts:
  - research/artifacts/gq-bh-bh-solvable-status.md
---

**ESTABLISHED** by `fp-infinity-soluble-groups-satisfy-permutational-bh-proof` (lane
`bh-solvable`, lane proof). It composes literature imports read at source with landed
nodes. Not independently reviewed. No priority is claimed: this is a direct corollary and
may be folklore.

## Statement

1. Every virtually soluble group `G` of type `FP_∞` (over `Z`) lies in `B_A`, and so embeds in a
   finitely presented simple group.
2. Hence every elementary amenable group of type `FP_∞` lies in `B_A`.

This includes all constructible soluble groups, for example `BS(1,n)`, iterated ascending HNN
extensions of them, and all polycyclic groups.

## Sources

- **Read at source.** C. Martínez-Pérez and B. E. A. Nucinkis, *Virtually soluble groups of
  type FP_∞*, Comment. Math. Helv. 85 (2010) 135–150 (open PDF, copy in
  `gq/src/bh-solvable/`).
  - p. 135: "Kropholler has shown that soluble groups of type FP_∞ are virtually
    torsion-free [17]."
  - **Theorem 1.1** ([10], [15], [17]). "Let `G` be a soluble group. Then the following are
    equivalent: (i) `G` is of type FP_∞. (ii) `G` is a virtual duality group. (iii) `G` is
    virtually torsion-free and vcd `G` = h`G` < ∞. (iv) `G` is virtually torsion-free and
    constructible."
  - p. 136: "Groups satisfying the conditions of the theorem are minimax."
  - p. 137 records that elementary amenable groups of type FP_∞ have a bound on the orders
    of their finite subgroups [17].
- **Also read.** P. H. Kropholler, Bull. London Math. Soc. 25 (1993) 558–566, Theorems B and C.
  Theorem B makes `G/T` constructible-by-finite for a locally finite normal `T`, and leaves
  open whether `T` can be infinite. Martínez-Pérez--Nucinkis attribute virtual
  torsion-freeness to their reference [17], which their bibliography gives as P. H. Kropholler,
  *On groups of type FP_∞*, J. Pure Appl. Algebra 90 (1993) 55–67. With it, `T` is finite in
  every case. That paper was not read here.
- **Secondary only.** The virtual solubility of elementary amenable `FP_∞` groups is
  Kropholler--Martínez-Pérez--Nucinkis, Crelle 637 (2009), carried on main through a secondary
  citation (`elementary-amenable-fp-infinity-groups-virtually-soluble`). The Crelle PDF was not
  reachable from MSI.

## Lesson for general BH

A finiteness condition helps for soluble groups exactly when it forces residual finiteness
plus finite rank. At that point the group is linear, and the linear hosts finish.
- `FP_∞` does this (Kropholler): it forces virtually torsion-free and constructible.
- Finite presentation alone does not: there are finitely presented soluble groups with
  unsolvable word problem (Kharlampovich, cited in BBMZ; not read here).

So homological finiteness never reaches the hard soluble inputs. Those have infinite rank or
divisible torsion, and they need new hosts.
