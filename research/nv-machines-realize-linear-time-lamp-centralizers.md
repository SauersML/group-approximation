---
rg: 2
id: nv-machines-realize-linear-time-lamp-centralizers
kind: claim
title: In a Brin-Thompson group nV the lamplighter embeds so that the lamp subgroup U_A over any non-periodic set A whose complement is nondeterministic linear-time is a centralizer, so the Dyson groups L(A) and all identity-edge combinations over U_A lie in B_A
requires:
  - pbh-coset-wreaths-iff-identity-edge-hnns
  - permutational-boone-higman-iff-full-cantor-hosts
  - type-a-action-gives-boone-higman-for-subgroups
distinct_from:
  pbh-coset-wreaths-iff-identity-edge-hnns: that proves centralizer realization (e) is equivalent to the coset-wreath and identity-edge HNN conditions and lists five structural cases (finite, centralizer, retract, fixed subgroup, intersections); this produces a computational case, where the centralizing element runs a clocked machine and the realized subgroups are indexed by linear-time sets, none of them in the structural list.
  centralizer-realizable-subgroups-are-pullback-closed: that realizes subgroups pulled back from B_A quotients; the lamp subgroups here contain no nontrivial normal subgroup of the lamplighter, so no pullback reaches them.
  fp-simple-group-containing-a-non-efrf-residually-finite-group: that was the open existence question for Rauzy-type groups; this theorem answers it through linear-time-rauzy-sets-exist.
---

**ESTABLISHED** by `nv-machines-realize-linear-time-lamp-centralizers-proof` (lane proof,
bh-invent-11, 2026-09-18; not reviewed; no priority claimed).

## Setting

- `L = Z/2 ≀ Z = ⟨a, ε⟩`, with lamps `u_i = a^i ε a^(-i)` and, for `A ⊆ Z`,
  `U_A = ⟨u_i : i ∈ A⟩`.
- A set `S ⊆ Z_{>=1}` is **NLIN₁** (nondeterministic linear time in unary) if there are a
  constant `c` and a deterministic multi-stack machine `V` with the following property. `V`
  reads `1^s` from one stack and a certificate `w ∈ {0,1}^N` from another. Then `s ∈ S` iff some
  `w` makes `V` accept within `c·s` steps. The deterministic case, with no certificate, is
  **LIN₁**.

## Statement

Let `S_+, S_- ∈ NLIN₁`, let `B = S_+ ∪ (−S_-)`, and let `A = Z ∖ B`, so `0 ∈ A`. Assume `A` is not
periodic. Then there are `n`, an embedding `L ↪ nV` and an involution `g ∈ nV` with

```text
C_L(g) = U_A .
```

`nV` lies in `B_A`: it is a full clopen-transitive Cantor host, so it acts with type (A) on its
proper clopen sets (`permutational-boone-higman-iff-full-cantor-hosts`). So condition (e) of
`pbh-coset-wreaths-iff-identity-edge-hnns` holds for `(L, U_A)`. Hence all of the following lie in
`B_A`, and so embed in finitely presented simple groups and have solvable word problem
(`type-a-action-gives-boone-higman-for-subgroups`):
- the coset lamplighter `Z/2 ≀_{L/U_A} L`;
- the identity-edge HNN extension `⟨L, t | [t, u] = 1 (u ∈ U_A)⟩`;
- the free permutational products `L *_{U_A} (U_A × K)` for every `K ∈ B_A`;
- in particular the **Dyson group** `L(A) = L *_{U_A} L`. It has index 2 in
  `L *_{U_A} (U_A × Z/2)`, as recorded in `fp-simple-group-containing-a-non-efrf-residually-finite-group`.

## Corollary: a finitely presented simple group with a non-effectively residually finite subgroup

Take `A` from `linear-time-rauzy-sets-exist`. Its complement is symmetric and in LIN₁, and `A` is
not periodic. By Rauzy's Proposition 1 and §3 (arXiv:2002.02540, read at source), `L(A)` is
finitely generated and residually finite, and has solvable word problem. It is not effectively
residually finite, and its depth function exceeds every recursive function. By the theorem,
`L(A)` embeds in a finitely presented simple group.

This settles `fp-simple-group-containing-a-non-efrf-residually-finite-group`. So the hereditary
class `P_eff` of `effective-residual-finiteness-separator-for-boone-higman` does not separate
Boone–Higman.

## Mechanism (one paragraph)

Points of a Cantor host compute deterministically. Clopen sets compute **nondeterministically**.
- **Clopen orbits.** Let `f ∈ nV` be a reversible multi-stack machine, and let `U_0` be the
  cylinder that fixes the initial state and leaves the stack contents below the read head free.
  Then `f^t(U_0)` is the finite union of the cylinders of every branch, where each branch reads a
  different prefix of that free tail.
- **The detector.** `g` toggles a spare bit exactly in one state `q_W`. So `g` fixes the clopen
  `f^t(U_0)` iff **no** branch is in `q_W` at time `t`.
- **Lamps and branches.** A lamp supported on `U_0` is carried by `f^t` to a lamp supported on
  `f^t(U_0)`. That lamp commutes with `g` iff `g` fixes that clopen.
- **Reading and clocking.** Branches read their input `s` in unary from the free tail, and a
  certificate from a second tail. A clock makes the branch for `s` emit at the exact time `C·s`.
  A mirrored copy handles negative times, and the trace onto `⟨a^C, ε⟩` removes the dilation.

## Scope and limits

- **The bound is forced.** For a fixed host the realizable sets are bounded by the host's word
  problem. The words `u_i` have length `O(|i|)`, and the word problem of `nV` is in coNP (Birget,
  recalled). So any `A` realized this way is in unary coNP. The theorem reaches the part of
  that bound in which the complement is decided in linear rather than polynomial time.
- **No universal compiler.** Arbitrary recursive `A` need hosts of unbounded complexity, as
  `complexity-bounded-host-classes-are-not-universal` requires. This is not a universal compiler.

## Lesson for general BH

The "compiler" that the combination closures of `B_A` need already exists in a fixed finitely
presented host, provided one works at the right level.
- **Why clopens.** Type (A) actions of full Cantor hosts are actions on clopen sets, and the
  orbit of a cylinder under a machine element runs every branch of its unread tail in parallel.
  So clopen stabilizers compute an ∃-projection of a clocked computation.
- **What this gives.** Identity-edge, coset-wreath and doubling permanence over subgroups cut out
  by such computations cost nothing.
- **What it kills.** Non-effective residual finiteness is no obstruction to Boone–Higman. The
  finite quotients of a residually finite subgroup of a finitely presented simple group can be
  hidden at a non-recursive depth, even though the host's own word problem is in coNP.
