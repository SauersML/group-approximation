---
rg: 2
id: thickenable-z-pairs-lie-in-the-move-class-of-a-basis-pair
kind: claim
title: Every orientably thickenable Z-pair in F_3 is carried to the basis pair (b, c) by relator-pair AC moves and automorphisms, so the thickenable endpoint certifies exactly the same presentations as the primitive endpoint
distinct_from:
  one-stabilization-ac-trivial-from-thickenable-z-pair: that shows a thickenable Z-pair certifies AC-triviality of the stabilized triple S+ (through Lackenby's theorem on a ball); this shows the pair itself is (P1)/(P2)-equivalent to a basis pair, with no third relator and without Lackenby, and so that the thickenable certificate adds no presentation beyond the primitive one
  one-stabilization-ac-trivial-from-primitive-relator: that is the primitive endpoint; this proves the thickenable endpoint has the same (P1)/(P2)-orbit closure as it
  thickenable-z-pairs-split-quotient-meridian-obstruction: that is a necessary condition on single thickenable pairs and kills one-relator routes; this classifies all thickenable pairs up to the moves and kills the thickenable endpoint as an independent route
  thickenable-balanced-presentations-have-meridional-relators: that is about presentations of the trivial group, whose thickening is a ball; this is the solid-torus analogue of the Heegaard-uniqueness argument
artifacts:
  - experiments/ak3-thick-z-pair-search-2026-09-17/ak3-rank3-cap24.log
  - experiments/ak3-thick-z-pair-search-2026-09-17/ak3-rank2-caps14-24.log
---

**Proposed ESTABLISHED** through `thickenable-z-pairs-move-class-proof`. Unreviewed. The
proof uses two cited results from 3-manifold topology: Heegaard splittings of handlebodies
are standard (Scharlemann–Thompson), and complete disc systems of a compression body are
related by disc slides (the classical outermost-arc argument, written out in the proof).

F = F(a, b, c). A Z-pair (r_1, r_2) and the moves are as in
`one-stabilization-ac-trivial-from-primitive-relator`: (P1) AC moves between r_1 and r_2
(products with conjugates of the other entry, inversion, conjugation, free reduction),
(P2) one automorphism of F applied to both entries. "Thickenable" means that the
presentation 2-complex embeds in an orientable 3-manifold. Unreduced relator words are
allowed in the complex.

## Theorem B

Every orientably thickenable Z-pair (r_1, r_2) is carried to (b, c) by finitely many moves
(P1), (P2).

**Idea.** A regular neighbourhood N of the complex is a solid torus (Steps 1–3 of
`one-stabilization-thickenable-z-pair-criterion-proof`). The handle decomposition
H ∪ h_1 ∪ h_2 is a genus-3 Heegaard splitting of N. Every such splitting is a stabilization
of the genus-1 one, so it is isotopic to the splitting of the pair (b, c). The isotopy
restricts to an automorphism on H, giving (P2). It carries the cores of h_1, h_2 to a
complete disc system of the standard compression body, which differs from the standard
system by disc slides. A disc slide is a band sum of attaching curves, i.e. a (P1) product
with a conjugate.

## Corollaries

**B1 (the two endpoints have the same reach).** For any Z-pair s, the following are
equivalent:
1. s reaches an orientably thickenable Z-pair by moves (P1), (P2);
2. s reaches (b, c);
3. s reaches a Z-pair with a primitive entry.

(1)⇒(2) is Theorem B. (2)⇒(3) is trivial, and (3)⇒(1) because a pair with a primitive
entry is (P1)/(P2)-equivalent to (b, c) (see `one-stabilization-ac-trivial-from-thickenable-z-pair`,
"Why this is a different endpoint"), and (b, c) is thickenable. So Theorem 1 of that
node is recovered without Lackenby's theorem, and the thickenable certificate certifies
no two-generator presentation that the primitive certificate misses. Thickenable
endpoints can only shorten a search: they may be met at a smaller length cap than any
primitive pair.

**B2 (thickenable seeds are the basis orbit).** Every thickenable Z-pair, and so every
"spine of a solid torus" in the sense of a genus-3 handlebody plus two 2-handles, is
generated from (b, c) by band sums of attaching curves (geometric (P1) moves) and
automorphisms. A backward search from thickenable seeds is a backward search from
(b, c) under a subset of the moves. It is not a new target family.

**B3 (bidirectional search at a fixed cap adds nothing).** Fix a total-length cap C and
let Γ_C be the graph of Z-pairs of total length at most C under the capped moves. A
bidirectional search with both sides confined to Γ_C meets exactly when AK(3) and some
thickenable seed lie in one connected component of Γ_C. The component of AK(3) in Γ_24
is exhausted in ranks 2 and 3 with no thickenable pair
(`experiments/ak3-thick-z-pair-search-2026-09-17/ak3-rank3-cap24.log`). So no bidirectional
search confined to cap 24 can meet it, whatever its seeds. A meeting needs cap
at least 25 on both sides. This is where the forward side can no longer be exhausted, and
meet-in-the-middle only helps there.

## What this leaves

The thickenable route and the primitive route for AK(3)⁺ are one route. The obstruction
to both is the same. Any path of elementary moves (those generated in `thzsearch.c`)
from AK(3) to (b, c) passes through a state of total length at least 25.
