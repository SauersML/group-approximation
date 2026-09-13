---
rg: 2
id: almost-actions-of-irs-rigid-simple-groups-are-free-or-trivial
kind: claim
title: Every almost action of an IRS-rigid infinite simple group is asymptotically free off its global fixed points
distinct_from:
  binary-leavitt-unit-group-is-permutation-stable: that uses the full character simplex of one nonsofic group to force every almost action to be trivial; this uses only rigidity of invariant random subgroups, which is weaker than character rigidity, and concludes free-or-trivial rather than trivial.
  kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf: that constrains genuine measure-preserving actions inside amenable orbit full groups; this constrains finite almost actions of any group whose invariant random subgroups are trivial.
  irs-rigid-nonamenable-groups-avoid-amenable-orbit-full-groups: that applies IRS rigidity to realizations in amenable full groups; this applies it to permutation almost-homomorphisms, where it makes every nontrivial model a sofic approximation.
---

**ESTABLISHED.** Let `S` be an infinite simple group with finite generating set `A`, and
write `N` for the kernel of `F(A) -> S`. Assume that every invariant random subgroup of
`S` is a convex combination of `delta_e` and `delta_S`. Let `sigma_n : F(A) -> Sym(d_n)` be
homomorphisms with

```text
d_H(sigma_n(w), 1) -> 0          for every w in N,                 (AF1)
```

where `d_H` is the normalized Hamming distance. Put
`Fix_n = {x : sigma_n(a) x = x for all a in A}`. Then for every `g in F(A) \ N`

```text
|{x : sigma_n(g) x = x} \ Fix_n| / d_n -> 0.                        (AF2)
```

**Consequences.**
1. **Every nontrivial model is a sofic approximation.** `Fix_n` is `sigma_n`-invariant. If
   `|Fix_n| <= (1-c) d_n` along a subsequence with `c > 0`, the restrictions of `sigma_n` to
   the complement of `Fix_n` satisfy `(AF1)` and move every `g notin N` on a proportion of
   points tending to 1. So they are a sofic approximation of `S`.
2. **Soficity test.** `S` is sofic iff some sequence satisfying `(AF1)` has
   `liminf |Fix_n|/d_n < 1`. No tensor amplification is needed: the witness itself is
   already asymptotically free off `Fix_n`.
3. **Free local charts.** If `L <= S` is a finite subgroup given by words, then on the
   complement of `Fix_n` almost every point has trivial `sigma_n(L)`-stabilizer. In any
   finite search for sofic models of such `S`, local finite subgroups may be taken to act
   freely at a cost of `o(d_n)` points.

**Instance.** `km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4`: the `(2,4,6)`
Kac--Moody lattices `Lambda_q/Z`, `q >= 4`. Their sofic question is exactly whether a
finite set carries almost actions with free rank-two charts `SL_2(q)^2`, `Sp_4(q)`,
`G_2(q)` whose overlaps agree on all but `o(d_n)` points.

**Model test.**
- The hypothesis fails for `Z` (not simple), and for the derived topological full group of a
  minimal free Cantor system with an invariant measure: its elements fix clopen sets of
  positive measure without acting trivially, so the stabilizer law of that action is a
  nontrivial ergodic invariant random subgroup (see `fp-infinite-simple-group-with-nontrivial-irs`).
- It holds for `Lambda_q/Z` above, and for the binary Leavitt unit group
  (`research/artifacts/leavitt-irs-rigidity-from-character-simplex-2026-09-08.md`), where
  the conclusion is consistent with, and weaker than, its permutation stability.

**Scope.** The unitary analogue would need rigidity of characters, which is open for
`Lambda_q/Z` (`caprace-thom-v2-leaves-km-character-rigidity-open`). No novelty is claimed:
this is the invariant random subgroup limit of an almost action (as in Becker--Lubotzky--Thom,
Duke Math. J. 168 (2019); theorem numbers not re-read) combined with rigidity.

Proof: `almost-actions-irs-rigid-simple-groups-free-or-trivial-proof`.
