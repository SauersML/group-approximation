---
rg: 2
id: exactness-separates-boone-higman-iff-fp-simple-groups-exact
kind: claim
title: Exactness disproves Boone--Higman iff every finitely presented simple group is exact, and no class of exact hosts can carry the conjecture
distinct_from:
  hereditary-approximation-disproofs-of-boone-higman: that treats approximation properties (sofic, MF, hyperlinear), where the witnesses are finitely presented simple groups failing (S1) and the decidable side is open; this treats exactness, where the decidable side (S2) is already settled by a residually finite group, and only (S1) remains.
  complexity-bounded-host-classes-are-not-universal: that kills host classes through a shared recursive bound on word-problem complexity; this kills host classes through property A with no complexity hypothesis, and the witness is one fixed decidable group rather than a diagonalization over inputs.
  boone-higman-conjecture: that is the embedding conjecture; this names a live operator-algebraic separator for it and the obstruction every exact host class meets.
  fp-simple-nonexact-group: that is the open existence of a non-exact finitely presented simple group, which the conjecture implies by this node; this is the separator theorem and the host-class kill.
  decidable-residually-finite-non-exact-group-exists: that is the single decidable non-exact witness; this uses it to decide what exactness can and cannot do for the conjecture.
artifacts:
  - research/artifacts/exactness-boone-higman-separator-2026-09-17.md
---

**ESTABLISHED (unreviewed).** Route: `exactness-separates-boone-higman-proof`.

Let `Ex` be the class of countable exact groups, equivalently the countable groups with property A. `Ex` is closed under isomorphism and subgroups. Separation is in the sense of `hereditary-approximation-disproofs-of-boone-higman`:
- (S1) every finitely presented simple group lies in `Ex`;
- (S2) some finitely generated group with solvable word problem does not.

## Theorem

1. **(S2) holds for exactness.** A residually finite Osajda group with solvable word problem is not exact (`decidable-residually-finite-non-exact-group-exists`). So:
   - exactness separates Boone--Higman **iff every finitely presented simple group is exact**;
   - if every finitely presented simple group is exact, `boone-higman-conjecture` is false;
   - if `boone-higman-conjecture` holds, some finitely presented simple group is not exact (`fp-simple-nonexact-group`). It can be taken to contain an infinite finitely generated simple Kazhdan LEF group with solvable word problem that is not exact.
2. **Class kill.** Let `C` be any class of groups whose members are all exact. No route to the conjecture of the form "every finitely generated group with solvable word problem embeds in a member of `C`" can succeed. The same holds for the weaker forms that quantify only over:
   - residually finite decidable inputs;
   - infinite finitely generated simple Kazhdan LEF groups with solvable word problem.

   **Invariant:** property A. **Step:** the universal embedding step. **Witness:** the Osajda group, or its decidable simple Kazhdan LEF host.
   The kill is stable under enlarging `C`:
   - by extensions of members by members, since exact groups are closed under extensions (`exact-groups-are-closed-under-extensions`);
   - by groups that coarsely embed in a property-A metric space (Willett l.540–542).
3. **Instances.** Each of the following is an exact class, so each dies at the universal step, even for residually finite, sofic, decidable inputs:
   - countable subgroups of `GL_n(R)`, for `R` a commutative ring (`commutative-ring-linear-groups-have-property-a`);
   - Gromov hyperbolic groups;
   - groups acting properly cocompactly on a finite dimensional CAT(0) cube complex, including uniform lattices acting properly cocompactly on a product of locally finite trees;
   - groups of finite asymptotic dimension;
   - discrete subgroups of connected Lie groups.

   The first instance is a graph import. The rest are as listed in Willett's notes (quoted in the artifact §1.2), and their primary sources were not re-read here.
4. **Orthogonality to the approximation kill.** The witness is residually finite, hence sofic and hyperlinear. So (S2) for exactness is unconditional, while (S2) for hyperlinearity is open. The difficulty moves entirely to (S1): exactness of every finitely presented simple group. Finitely presented non-exact groups exist by Sapir's theorem, read through its abstract only (context in the artifact §1.4). So the open content is simplicity.

## What this kills, and where

Every host-class route whose hosts are geometric in the property-A sense dies at the universal embedding step. This includes:
- linear hosts;
- hyperbolic or cubulated hosts;
- lattices on products of trees;
- hosts of finite asymptotic dimension.

Many of these already died, conditionally or through residual finiteness. This kill is unconditional and survives residual finiteness of the inputs.

**Survivors.** Any host class that could carry the conjecture must contain non-exact groups. That includes non-exact finitely presented simple groups, if the conjecture holds. Candidates whose exactness is not settled in this graph:
- Thompson's `V` and its relatives (`nV`, twisted Brin--Thompson groups `SV_G`);
- the Leavitt unit group `L^x`;
- topological full groups of ample groupoids that contain `V`.

The kill applies to permutational hosts as well. For the Osajda input, the finitely presented actor of `permutational-boone-higman-conjecture` must itself be non-exact, whatever its action.
