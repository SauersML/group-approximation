---
rg: 2
id: fp-simple-groups-with-arbitrarily-complex-word-problem
kind: claim
root: true
title: For every recursive time bound some finitely presented simple group has a harder word problem
distinct_from:
  simple-envelope-forces-solvable-word-problem: that says every finitely presented simple group has solvable word problem; this asks that those solvable word problems are not uniformly bounded by any recursive time function.
  complexity-bounded-host-classes-are-not-universal: that is the established non-universality theorem for bounded host classes; this is the open existence statement for the specific class of all finitely presented simple groups, which the conjecture would force.
artifacts:
  - research/artifacts/boone-higman-self-similar-and-complexity-2026-09-11.md
---

**OPEN.** For every recursive `T: N -> N` there is a finitely presented simple
group `S` whose word problem has no algorithm running in time
`C*T(C*l) + C*l + C` for any constant `C`.

Every finitely presented simple group has solvable word problem
(`simple-envelope-forces-solvable-word-problem`), so this asks only that the
class have no uniform recursive complexity bound. By
`complex-fp-simple-groups-from-boone-higman` it is a **necessary consequence**
of `boone-higman-conjecture`. A proof of the conjecture must therefore, among
other things, construct finitely presented simple groups beyond every recursive
time bound. That is a concrete test for any proposed universal envelope: its
word problems must be unboundedly complex, i.e. the construction must consume
the input's algorithm, as
`compilers-cannot-drop-the-decidability-hypothesis` already says in a
different form.

It is a root because it is independently well posed, strictly weaker than the
conjecture, and not implied by any established node here.

## What is known

Every finitely presented simple group whose word-problem complexity has been
determined is easy. The hardest known case is due to Birget, *The word problem
of the Brin--Thompson group is coNP-complete*, arXiv:1902.03852, read from the
abstract 2026-09-11: "the word problem of the Brin--Thompson group nV over a
finite generating set is coNP-complete for every n >= 2". Each `nV` is infinite,
finitely presented and simple. coNP lies inside `2^(n^O(1))` time, so the whole
known Thompson-like family sits under one recursive bound. By
`complexity-bounded-host-classes-are-not-universal`, or its finitely presented
residually finite form `uniform-wp-bound-excludes-bh-universal-targets`, that
family is non-universal for Boone--Higman. (This paragraph was carried over from
the retired duplicate root `bh-forces-unbounded-fp-simple-wp-complexity`.)

## Attempts

1. **Twisted Brin--Thompson groups over complex actors.** A finitely
   presented group with a type (A) action whose word problem beats `T` would
   give a simple example through
   `type-a-action-gives-boone-higman-for-subgroups`. The candidate actors in
   this graph are the shift envelope `infinite-shift-higman-compiler`, the
   shell envelopes `perfect-decidable-inputs-have-fp-shell-envelopes`, and the
   fiber-product data `universal-fiber-product-data-for-word-problem-groups`.
   All are open.
2. **Finitely presented self-similar hosts.** Via
   `fp-self-similar-groups-embed-in-fp-simple-groups`, it would suffice to
   embed algorithmically complex finitely presented residually finite groups
   in finitely presented self-similar groups, a special case of
   `every-fp-rf-group-embeds-in-fp-self-similar-group`. By its condition
   (N2) those hosts cannot be automaton groups.
3. **Classical Thompson-like hosts.** *Dies as a method* by
   `complexity-bounded-host-classes-are-not-universal`: any family sharing
   one recursive bound, such as all rational homeomorphism groups, cannot
   supply the needed examples.
4. **Finite germ extensions of `V` certified by the Belk--Hyde--Matucci germ
   corollary.** *Dies as a family, under orbit-preserving transports* (2026-09-13,
   `orbit-preserving-germ-corollary-extensions-of-v-are-rational`).
   - *The theorem.* Let `G` be a finitely generated finite germ extension of `V`
     satisfying, at each singular point, hypothesis (2) of Corollary 2.10 for
     singletons and the either-or of hypothesis (3). If every element maps each
     singular point into its own `V`-orbit (for instance when `sing(G)` is one
     `V`-orbit), every element of `G` is rational, so `G` and all its subgroups
     have word problem in `F(2^n)`.
   - *Where hardness can still enter this branch.* Theorem 2.1 with germ groups
     that normalize no finite-index subgroup of their `V`-germs, as for shell
     envelopes of non-virtually-cyclic inputs; or a singular transport between
     different `V`-orbits, where a germ may apply unboundedly many iterates of a
     fixed annulus map. No finitely presented example of either kind is known.
   - *Provenance.* Birget, arXiv:math/0310335 §1, states this root as a
     consequence of a conjecture he attributes to Higman, reports every analyzed
     finitely presented simple group in `P`, and says neither side "ha[s] much
     evidence". Zaremsky (arXiv:2305.15176) gives the first finitely presented
     simple groups with at least exponential Dehn function; that bounds nothing
     here from below. Pins in `research/artifacts/hl-bh-hard-simple-2026-09-13.md`.
5. **Faithful finite-index HNN extensions of hard vertex groups** (bh-free-02,
   2026-09-18). `finite-index-edge-hnn-embeds-in-fp-simple-group` needs no envelope
   for the vertex group. So one finitely presented residually finite `A` with a hard
   word problem and a faithful HNN extension over finite-index subgroups would settle
   this root.
   - *Scaling shape: dies.* For `A = M ⋊ H` with `M` elementary abelian and a
     scaling fixing `H`, which is the shape a Kharlampovich--Myasnikov--Sapir group
     `T ⋊ H` offers first, faithfulness forces `A` to be linear over `F_p((x))`
     (`equivariant-scaling-hnn-vertex-groups-are-linear`). Linear groups share the
     classical low bound, so this shape cannot supply hard inputs.
   - *Still open:* scalings that move `H`; non-ascending extensions over two proper
     edges whose isomorphism is not the restriction of an automorphism.
   - Notes: `research/artifacts/gq-bh-bh-free-02-complexity-root-notes.md`.
6. **Germ extensions of `V` whose hardness sits in one free tail parameter.**
   *Dies at finite presentation, with no germ hypothesis* (2026-09-17,
   `tail-uniform-germ-extensions-of-v-are-not-fp`).
   - *The class.* `G = < V, g_1, ..., g_m >`, each `g_i` read off one point `x` by
     a finite tail template: prefix replacements plus finitely many relative
     shifts at singular points `a σ^j x`. The model is `h_x`, which shifts the
     annuli `C(x|n ¬x_(n+1))` down by one around `x`. For computable `x` its word
     problem computes `x`, so these groups beat every recursive bound.
   - *Where every member dies.* If `x` is not eventually periodic and some
     singular germ is not a `V`-germ (nonzero tail offset), `G` is not finitely
     presented. Each relation is decided by a finite prefix of `x` (locality), and
     flipping one deep bit gives a marked group satisfying every relator of a
     candidate finite presentation but failing a conjugation relation. This is
     the Grigorchuk `G_ω` mechanism. So every finitely presented member is
     rational and falls under Attempt 3.
   - *What it closes.* The single-tail case of Attempt 4's "singular transport
     between different `V`-orbits", in which the singular points are shifted
     copies of one aperiodic tail. What stays open is germs that apply
     unboundedly many rules at one singular point, and germ groups given by
     other finitely presented groups acting on the tail.
