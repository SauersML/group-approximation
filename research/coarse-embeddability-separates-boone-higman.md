---
rg: 2
id: coarse-embeddability-separates-boone-higman
kind: claim
title: Boone–Higman fails if every finitely presented simple group coarsely embeds into Hilbert space, and if it holds some finitely presented simple group coarsely contains an expander
requires:
  - decidable-group-with-coarsely-embedded-expanders-exists
  - hereditary-approximation-disproofs-of-boone-higman
  - exactness-separates-boone-higman-iff-fp-simple-groups-exact
  - haagerup-hosts-carry-no-weak-expander
distinct_from:
  exactness-separates-boone-higman-iff-fp-simple-groups-exact: that separator is property A; this is coarse embeddability into Hilbert space, which is implied by property A, so this refutation criterion has a strictly weaker hypothesis and its necessary consequence under Boone–Higman is strictly stronger.
  fp-simple-nonexact-group-via-boone-higman: that derives a non-exact finitely presented simple group from Boone–Higman; this derives one that coarsely contains an expander, hence is not coarsely embeddable and a fortiori not exact.
---

**ESTABLISHED** (lane proof, short; inputs cited; not independently reviewed). No priority
claimed.

`CE` is the class of countable groups that coarsely embed into Hilbert space, using any proper
left-invariant metric. It is closed under isomorphism and subgroups, since the inclusion of a
subgroup is a coarse embedding. Separation is in the sense of
`hereditary-approximation-disproofs-of-boone-higman`.

## Theorem

1. **(S2) holds for `CE`.** The group `M` of `decidable-group-with-coarsely-embedded-expanders-exists`
   is finitely generated, has solvable word problem, and is not in `CE`. Hence:
   - `CE` separates Boone–Higman **iff every finitely presented simple group coarsely embeds into
     Hilbert space**;
   - if every finitely presented simple group coarsely embeds into Hilbert space,
     `boone-higman-conjecture` is false.
2. **Consequence of Boone–Higman.** If `boone-higman-conjecture` holds, then `M <= S` for some
   finitely presented simple `S`. The inclusion is a coarse embedding, so `S` contains a coarsely
   embedded expander: the LPS family `(Θ_n)` maps into `S` with control functions independent of `n`.
   The same holds with `M` replaced by its simple Kazhdan decidable host, item 2 of that node.
3. **Comparison with exactness.** Property A implies coarse embeddability (Yu; Willett
   l.544–546 as quoted in `research/artifacts/exactness-boone-higman-separator-2026-09-17.md`).
   So:
   - the hypothesis "every f.p. simple group is exact" of
     `exactness-separates-boone-higman-iff-fp-simple-groups-exact` implies the hypothesis of item 1;
   - item 2 implies that node's consequence `fp-simple-nonexact-group`.

   The two separators differ on the known groups in between: Osajda's groups acting properly on
   CAT(0) cube complexes without property A (arXiv:1406.5015, Theorem 2) are in `CE` but not exact.
4. **Class kill.** No class `C` of groups all of which lie in `CE` can be universal for
   Boone–Higman: `M` embeds in no member. Instances, each by the cited node or source:
   - every Haagerup group, since a proper cocycle is a coarse embedding
     (`haagerup-hosts-carry-no-weak-expander`, step 1). This covers:
     - `F <= T <= V` (`thompson-v-has-haagerup-property`);
     - topological full groups of irreducible one-sided SFTs, including `V_{n,r}`
       (`sft-topological-full-groups-have-the-haagerup-property`);
     - groups acting properly on CAT(0) cube complexes, which have the Haagerup property by the
       walls equivalence (Osajda p. 3, quoted there as [HP98, Nic04, CN05]);
   - every exact group, recovering item 2 of `exactness-separates-boone-higman-iff-fp-simple-groups-exact`.

   Unlike the exactness kill, this one also reaches non-exact Haagerup hosts. So a route that
   realizes every decidable input inside V-like or cubulated hosts with the Haagerup property is
   dead at the universal step, whether or not those hosts are exact.

## What survives

A finitely presented simple host for `M` must lie outside `CE`, and so outside every Haagerup
family. Non-Haagerup finitely presented simple groups are known; the one discussed in
`haagerup-hosts-carry-no-weak-expander` is the binary Leavitt unit group `L^x`. Whether any finitely
presented simple group fails `CE`, let alone coarsely contains an expander, is open here.
Items 1 and 2 say that this open question is exactly where the `CE` separator lives.
