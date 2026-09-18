---
rg: 2
id: decidable-groups-embed-in-outer-extensions-of-fp-simple-groups
kind: claim
title: Every finitely generated group with solvable word problem embeds in an extension of a finitely presented nonabelian simple group by a finitely presented group acting faithfully by outer automorphisms
distinct_from:
  boone-higman-conjecture: that asks for a finitely presented simple overgroup, which is the case Q = 1 of this statement; so that implies this.
  every-decidable-group-embeds-in-an-isolated-group: that is Cornulier--Guyot--Pitsch Question 4, which this implies through `outer-extensions-of-fp-simple-groups-are-isolated`; this is a specific sufficient condition for it.
  outer-extensions-of-fp-simple-groups-are-isolated: that is the theorem that such extensions are isolated; this is the open universality statement asking every decidable input to sit inside one.
---

**OPEN.**

**Statement.** For every finitely generated group `G` with solvable word
problem there is an extension `1 → S → I → Q → 1` with
- `S` finitely presented, simple and nonabelian,
- `Q` finitely presented,
- the conjugation homomorphism `Q → Out(S)` injective, and
- `G ≤ I`.

**Implications.**
- Boone--Higman implies this. If `G` embeds in a finitely presented simple
  group, take `S` to be that group and `Q = 1`. If `G` is finite, `S` can be a
  finite alternating group; if `G` is infinite, `S` is infinite and so
  nonabelian.
- This implies `every-decidable-group-embeds-in-an-isolated-group`, by
  `outer-extensions-of-fp-simple-groups-are-isolated`.

**Complexity.** Every such `I` embeds in `Aut(S)`, and its word problem costs at
most one exponential over that of `S`
(`outer-extension-word-problem-is-kernel-bounded`, 2026-09-13). So for one
fixed `S`, or any class of such `S` sharing one recursive bound, split and
non-split extensions alike share one recursive bound, and
`complexity-bounded-host-classes-are-not-universal` excludes them as universal
hosts. The earlier remark that non-split extensions of a fixed `S` escape this
(root Attempt 3) was wrong: the innerness search decides triviality in the
quotient `Q`, while the input sits in `I`.

Consequently this statement implies
`fp-simple-groups-with-arbitrarily-complex-word-problem` (route
`complex-fp-simple-groups-from-outer-extensions`), exactly as
`boone-higman-conjecture` does. The outer-extension route has no complexity
advantage over the conjecture: the simple kernels must themselves be
unboundedly complex.

No construction is known beyond the Boone--Higman cases.

## Attempts

1. **One fixed simple kernel, with non-split outer extensions.** Killed by
   `outer-extension-word-problem-is-kernel-bounded` (2026-09-13, lane
   solve-bh-outer-ext). The kernel's automorphism action decides the word
   problem of `I` after one exponential substitution.
2. **Known Thompson-like kernels.**
   - For `V` and `nV`, whose word problems lie in coNP (Birget,
     arXiv:1902.03852, as recorded on the root
     `fp-simple-groups-with-arbitrarily-complex-word-problem`), all outer
     extensions share one recursive bound, so none is universal.
   - Kernels with hard word problems do exist on main: twisted Brin--Thompson
     groups `SV_G`, whose word problem is governed by the actor
     (`twisted-brin-thompson-wp-equals-actor-orbit-problem`). But an input
     placed in such an actor already satisfies permutational Boone--Higman, so
     outer extensions add nothing there.
   - What remains is a universal supply of finitely presented simple kernels
     of unbounded complexity, each with finitely presented outer extensions
     containing the input outside the kernel. That is at least as hard as the
     complexity root.
3. **Non-MIF residue, word-automorphism half (2026-09-17, swarm-0917-w5-bh-outer).**
   *Settled for circle kernels; the prerequisite that remains is BFFHZ Question 3.2.*
   - `outer-extensions-of-fp-simple-mif-groups-satisfy-pbh` makes the MIF case
     equivalent to pBH. For a non-MIF kernel it leaves two conditions (artifact
     §8, Prop 9): (a) BFFHZ Q3.2 for `S`, and (b) finite normal generation of the
     group `W` of word automorphisms in the enlarged actor's kernel image.
   - `micro-supported-word-automorphisms-are-pointwise-inner` shows that for any
     micro-supported kernel, a word automorphism `r` has
     `Y = ∪_j { r = h_j }` for the coefficients `h_j` of its word. For
     `[T_{n,r},T_{n,r}] <= S <= T_{n,r}`, `r ∈ T_{n,r}`, so (b) holds for every `B`.
   - `thompson-circle-kernel-outer-extensions-reduce-to-bffhz-q32` follows: an
     outer extension of such an `S` lies outside pBH only if Q3.2 fails for `S`.
   - Open: non-PL micro-supported kernels (whether `L(S)/S` is finitely
     generated) and kernels that are not micro-supported. Combined with
     Attempt 1, a universal host family must use unboundedly complex non-MIF
     kernels failing (a) or (b).
