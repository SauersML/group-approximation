---
rg: 2
id: left-orderable-non-sofic-group
kind: claim
root: true
title: Exhibit a left-orderable non-sofic group
---

Is there a left-orderable group that is not sofic?

Left-orderability is subgroup-closed and non-soficity passes upward, so this is
not a question that any embedding trick can reach: the witness has to be a
non-sofic group that is *itself* left-orderable, and every subgroup of it is
then left-orderable too.  The same question with "bi-orderable", "locally
indicable" or "unique product" in place of "left-orderable" has the same shape,
and each is implied by the previous one.

This is the cell that blocks `!sofic` against each of `lo`, `li`, `bo` and `up`
in the group-property atlas, and the corresponding cells for `!mf`.  The `!lea`
and `!lef` cells against these four properties are not blocked by it: the
Lodha--Moore group is finitely presented, bi-orderable and not LEA, hence not
LEF (`lodha-moore-group-is-bi-orderable-and-not-lea`).

## Attempts

**Use a known non-sofic group directly.**  This is where the obvious attack
dies, and the reason is uniform across the known examples.  Left-orderability
forces torsion-freeness, so any candidate must be torsion-free, which already
rules out the OpenAI Leavitt unit group and the Kun--Thom group; both contain
torsion.  The torsion-free non-sofic examples that remain all carry property
(T).

That is not a coincidence that can be waited out, because a left-orderable
countable group with property (T) would settle a known open question.  The
dynamical realization of a left order embeds any countable left-orderable group
into `Homeo_+(R)` faithfully.  So a countable left-orderable non-sofic group
with property (T) is in particular an infinite countable Kazhdan group acting
faithfully on the line by orientation-preserving homeomorphisms — and whether
such a group exists is open (it is the interval case of the standard question
about Kazhdan groups acting on one-manifolds; the circle case is open for
homeomorphisms and known to fail for `C^{1+alpha}` diffeomorphisms by Navas).

So the route through the currently known examples is blocked behind that
question, and the honest reading is that this cell needs either a non-sofic
construction that does not go through property (T), or an answer to the Kazhdan
line-action question.

**Weaken to unique product.**  `up` is the weakest of the four and does not
force left-orderability, so a unique-product non-sofic group is formally easier.
It still forces torsion-freeness, so it does not escape the first half of the
obstruction, but it does escape the `Homeo_+(R)` reduction, since unique-product
groups need not be left-orderable.  This looks like the right place to push
first, and it is deferred here rather than attempted.

*Attempted 2026-09-12.*  The weaker cell is now the claim
`unique-product-non-sofic-group`, and property (T) is no obstacle there.
Kionke--Raimbault give virtually diffuse lattices in `Sp(n,1)`.
`non-rf-hyperbolic-group-or-unique-product-nonsofic-group` (reviewed PASS by
ex-verify2-groups) proves
a disjunction: either the hyperbolic Kazhdan Leavitt cover is not residually
finite, or some nonsofic group has unique products.  For the second branch, a
deep normal subgroup of the cover has unique products by Delzant's
injectivity-radius theorem, and the integer-lamp wreath over the restricted
rigid pair is nonsofic.

**The rigid-defect mechanism, made torsion-free (2026-09-12).**  The torsion in
the Kun--Thom group sits only in its lamps.

- *Live, conditional route.*
  `left-orderable-non-sofic-via-integer-lamp-rigid-pair` turns any
  left-orderable group with an infranormal non-normal Kazhdan pair into a
  left-orderable nonsofic group, the integer-lamp wreath or the double.  Its
  input `left-orderable-group-with-rigid-compression-pair` contains an infinite
  left-orderable Kazhdan group.  That is Navas's Question 3
  (`infinite-left-orderable-kazhdan-group`, quoted verbatim from
  arXiv:1712.06462v2).
- *Dead: relative property (T).*  Relative (T) of an abelian subgroup is the
  rigidity ordered groups are known to carry, and it cannot replace (T) in the
  defect criterion.
  `relatively-kazhdan-amenable-pairs-allow-sofic-defects` gives a sofic,
  locally indicable counterexample, and it invalidates
  `left-orderable-non-sofic-via-relative-kazhdan-defect-criterion`.
- *Dead for bi-orderable and locally indicable witnesses.*  They contain no
  nontrivial Kazhdan subgroup, so every mechanism on the shelf is closed to
  them.
- *Dead for PL flow groups.*  Matte Bon--Triestino's left-orderable groups
  `T(phi)`, which include finitely generated simple ones, contain no infinite
  Kazhdan subgroup (arXiv:1811.12256, Theorem F).

**Non-Kazhdan witnesses (2026-09-13).**  Two bi-orderable candidates, both open,
neither behind Navas's Question 3.

- *Live: Thompson's F.*  `left-orderable-non-sofic-via-thompson-f`, input
  `thompson-f-is-not-sofic`.  By `thompson-f-sofic-iff-relator-system-unstable`
  that input is Arzhantseva--Paunescu's permutation-stability question for the
  two relators of `F`.  `F` is bi-orderable (`thompson-f-is-bi-orderable`) and
  has the Haagerup property, so neither a Kazhdan subgroup nor a rigid
  compression defect can be the mechanism.
- *Live: the Lodha--Moore group.*
  `left-orderable-non-sofic-via-lodha-moore-group`, input
  `lodha-moore-group-is-not-sofic`.  It is finitely presented, bi-orderable and
  not LEA, and all its proper quotients are abelian.
- *Dead: embed a torsion-free nonsofic group in a left-orderable group.*  This
  is the opening paragraph again: left-orderability passes to subgroups, so the
  nonsofic subgroup would itself have to be left-orderable.
- *Torsion-free but not orderable: the stability HNN.*  The mechanism of
  `hnn-over-sl2-z-not-sofic-if-sl2-z-inverse-p-p-stable` should run on
  torsion-free congruence subgroups of `SL_2(Z[1/p])` (hand remark, not written
  up).  Congruence quotients still control finite actions, and the `SL_2(Z)` part
  keeps property (tau).  But the output contains a finite-index subgroup of
  `SL_2(Z[1/p])`, and such S-arithmetic groups are reported not left-orderable
  (Lifshitz--Witte Morris, not re-read here).  So it gives no witness.
- *Dead: Gohla--Thom central extensions.*  `gohla-thom-stable-base-nonsofic-extension`
  produces central extensions by a finite abelian group, which have torsion.
- *Untested: random complexes.*  `cocycle-stability-nonsofic-route` would give a
  nonsofic hyperbolic group from random Linial--Meshulam complexes.
  Orderability of those groups is not recorded in this graph.

**A locally indicable witness played against a logic cell (2026-09-17).**  This route needs no Kazhdan subgroup and
does not sit behind Navas's Question 3.

- *Proposed established: the rope is locally indicable.*  `compiler-rope-is-locally-indicable` shows that the
  finite-presentation compiler's positive rope `R_e` is locally indicable, hence left-orderable and
  unique-product.  The proof uses the retraction `u |-> 1`, `H |-> 1` onto `Gamma_e`, whose kernel is a free
  product of copies of `H <= F_2 x F_2`.
- *Reduction, one direction: the dichotomy.*
  `sofic-fp-pi2-complete-or-locally-indicable-nonsofic-group` shows that either `SOFIC_fp` is
  `Pi^0_2`-complete, or some `R_e` is a finitely presented locally indicable nonsofic group.
  - Route: `left-orderable-non-sofic-via-compiler-rope`.
  - Open input: `compiler-positive-rope-is-not-sofic`.
- *Obstacle.*  `R_e` is MF, so a nonsoficity proof must be invisible to operator-norm approximations.
