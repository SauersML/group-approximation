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
`non-rf-hyperbolic-group-or-unique-product-nonsofic-group` (unreviewed) proves
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
