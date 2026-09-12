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
in the group-property atlas, and the corresponding cells for `!mf`, `!lea` and
`!lef`.

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
