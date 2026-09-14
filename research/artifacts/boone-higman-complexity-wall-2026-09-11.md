# A complexity wall for Boone--Higman target families, 2026-09-11

Third record of the 2026-09-11 Boone--Higman lane, after the MF-radical bridge
and the nonsofic envelope. The conjecture remains open. This one is an
unconditional theorem about what a universal construction is allowed to look
like, plus one consequence of the conjecture.

## The theorem

Write, for a recursive non-decreasing `g`,

```text
F(g) = { L : L decidable in time C*g(C*n) + C*n + C for some C }.
```

> **Wall.** If every finitely generated group in a class `C` has, for some
> finite generating set, word problem in `F(g)`, then some finitely presented
> residually finite group with decidable word problem embeds in no member of
> `C`. Hence `C` contains no Boone--Higman envelope for every admissible
> input.

Recorded as `uniform-wp-bound-excludes-bh-universal-targets`, established via
`uniform-wp-bound-excludes-bh-targets-proof`.

Three steps, none of them long:

1. **Diagonalize.** Reserve one input per pair (machine, constant), clock the
   machine at `c*g(c*n)+c*n+c` steps, and invert its answer. `g` recursive
   makes the clock computable, so the resulting `X` is recursive and outside
   `F(g)`.
2. **Realize.** `kms-arbitrarily-hard-fp-rf-groups`, the import of
   Kharlampovich--Myasnikov--Sapir Theorem 4.21, turns `X` into a finitely
   presented residually finite group `G`, solvable of class three, whose word
   problem is outside `F(g)`. Their Definition 2.2(a) supplies the
   quantitative comparison that makes "outside `F(g)`" transfer.
3. **Transfer.** If `G <= H` with `H` in `C`, rewriting each generator of `G`
   as a word over `H`'s generating set is a length-linear, linear-time
   reduction of `WP(G)` to `WP(H)`. So `WP(G)` would be in `F(g)`.
   Contradiction.

Step 3 uses only that `G` is a subgroup of `H`: no normality, no finite index,
no effectiveness of the embedding.

## What it kills and what it does not

It kills any proposed universal target family with a fixed complexity ceiling
— word problem in `P`, in `coNP`, or in `EXP`. Taking `g(n) = 2^n` and
combining with `rational-homeomorphism-subgroups-have-exponential-wp` recovers
`decidable-fp-groups-need-not-embed-in-rational-group` as the special case.
That existing claim keeps its own route; no second route into it was added,
since two routes proving one target by one argument is a defect this graph has
hit before.

It does **not** touch the twisted Brin--Thompson programme or the shell and
shift compilers, because in all of those the target is built from an actor
containing the input, so the target's complexity rises with the input's and no
uniform `g` is available to apply the wall to.

So the honest reading is a constraint on the *shape* of a universal proof
rather than a refutation of a live route. It sharpens
`compilers-cannot-drop-the-decidability-hypothesis` from "the construction
must consume the decidability algorithm" to "it must consume it in a way that
preserves arbitrarily high complexity" — no step may factor through a family
with a fixed ceiling.

## The consequence of the conjecture

`bh-forces-unbounded-fp-simple-wp-complexity`, a new root: for every recursive
non-decreasing `g` there is a finitely presented simple group whose word
problem is outside `F(g)`. The route is `bh-unbounded-wp-complexity-proof`:
apply the conjecture to the group `G` from step 2, and transfer as in step 3.

The point of recording it is the gap it exposes. Every finitely presented
simple group whose complexity has actually been determined is easy; the
hardest known is `coNP`-complete, by
[Birget, arXiv:1902.03852](https://arxiv.org/abs/1902.03852) for the
Brin--Thompson groups `nV`, which are finitely presented, infinite and simple.
`coNP` is inside `EXP`, hence inside `F(2^n)`. So by the wall the whole family
`{nV}` is non-universal, and the conjecture demands finitely presented simple
groups of a complexity nobody has yet exhibited.

## Addendum, same day: merged with the parallel lane

The parallel Boone--Higman lane had landed the same consequence 18 minutes
earlier, as `fp-simple-groups-with-arbitrarily-complex-word-problem` with route
`complex-fp-simple-groups-from-boone-higman`, and a general non-universality
principle `complexity-bounded-host-classes-are-not-universal` with a
two-generated graph-shift witness. Two roots stating one consequence overstate
the graph, so `bh-forces-unbounded-fp-simple-wp-complexity` and
`bh-unbounded-wp-complexity-proof` were retired in `ad00c87ce`. Section 3's
root is now that surviving node.

`uniform-wp-bound-excludes-bh-universal-targets` is kept as a strict
strengthening of the principle: its excluded input is finitely presented and
residually finite, which lanes restricted to such inputs need. The two nodes
carry `distinct_from` answers to each other.

## Verification boundary

Steps 1 and 3 are elementary and written out in full in the route. Step 2 is a
literature import whose primary source was read for the statement and the
quantitative definition, not re-proved. No Lean certificate is claimed and no
computation was run: the content is a diagonalization and a substitution,
neither of which gives signal from a computer.
