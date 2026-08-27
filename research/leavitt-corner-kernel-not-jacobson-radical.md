---
rg: 2
id: leavitt-corner-kernel-not-jacobson-radical
kind: claim
title: The corner evaluation kernel is nonzero, contains an idempotent of augmentation zero, and is not inside the radical
invalidates: [leavitt-unit-algebra-not-directly-finite-by-radical-kernel]
distinct_from:
  leavitt-corner-kernel-is-jacobson-radical: that open claim asserts `ker(pi_e) = J(eAe)`; this one refutes it, and in the strong form that `ker(pi_e)` is not even contained in the radical, so that node should be read as false rather than unattempted.
  leavitt-evaluation-kernel-hits-augmentation-one: that says the whole-algebra kernel is nonzero and meets augmentation one, with the three-term witness `[u]+[v]+[w]`; this says the *corner* kernel is nonzero and meets augmentation *zero*, and the two witnesses are disjoint — the three-term one is annihilated by `e` on both sides.
  leavitt-recursive-kernel-idempotents: that produces an infinite orthogonal family in the whole kernel and is about the family's size; this produces one idempotent in the corner kernel and is about what its existence rules out.
  sofic-radical-soficization: that is an approximation-theoretic radical of a group, the largest quotient visible to sofic approximations; this concerns the Jacobson radical of a ring corner, and the two share only the word radical -- the same disclaimer the refuted node carries.
artifacts:
  - research/artifacts/leavitt-stable-finiteness-audit-2026-08-17.md
  - research/artifacts/verify-s3-corner-2026-08-17.py
---

With `S = F_2[G]`, `G = L_(F_2)(1,2)^x`, `e = [g] + [g^2]`, and
`pi_e : eSe ->> R` the corner evaluation of
`leavitt-corner-idempotent-unital-surjection`, let

    z = [1] + [g] + [g^2],     f = [1] + [u] + [v] + [g],
    q = lambda(z) = delta_*(z) f.

Then `q^2 = q`, `q != 0`, `q in ker(pi_e)`, and `eps(q) = 0`.  Consequently

    ker(pi_e)  is not contained in  J(eSe),

and in particular `ker(pi_e) != J(eSe)`.

## The three facts this puts to rest

**`ker(pi_e) != 0`.**  This is the computation both 2026-08-17 Leavitt audits
named as the next real piece of work, and the answer is no.  It was not
obtainable by restricting the kernel element the graph already had: the
three-term witness `k = [u] + [v] + [w]` of
`leavitt-evaluation-kernel-hits-augmentation-one` satisfies `e k = k e = 0`,
verified exactly in `research/artifacts/verify-s3-corner-2026-08-17.py`.  The
corner is blind to it.  A new element was needed, and it comes from the
recursive embedding of `leavitt-primitive-corner-recursive-extension`.

**The radical hypothesis is false.**  The Jacobson radical of a unital ring
contains no nonzero idempotent: `r^2 = r in J(A)` makes `1 - r` a unit, and
`r(1-r) = 0` then forces `r = 0`.  So a single idempotent in `ker(pi_e)`
kills `leavitt-corner-kernel-is-jacobson-radical` outright, and with it the
route `leavitt-unit-algebra-not-directly-finite-by-radical-kernel`.  Note the
direction: the radical hypothesis fails not because the radical is too small
but because the kernel is too *idempotent-rich* to sit anywhere inside it.

**The kernel is not nilpotent, nil, or radical noise.**  Any picture of the
correction ideal as small perturbation is wrong, and
`leavitt-recursive-kernel-idempotents` sharpens this to an infinite orthogonal
family.  Future attacks should use Peirce and corner structure, not radical
perturbation theory.

## Augmentation zero is the load-bearing half

`eps(q) = eps(z) eps(f) = 1 . 0 = 0`, so `q` lies in `K n ker(eps)` — the
ideal in which any parity-respecting correction has to live, since
`(pi, eps) : S -> R x F_2` is onto with that kernel.  The old witness `k` has
`eps(k) = 1` and is useless for that purpose even where it is nonzero.  This
is the first element the graph owns that is invisible to both maps at once.

## What it does not do

It does not produce a one-sided inverse, and it does not make
`leavitt-corner-one-sided-lift-exists` easier in any measurable way — the
lifting equation `(a + alpha)(b + beta) = e` still needs a solution, and
knowing that `alpha, beta` have a large space to live in is not a step toward
finding one.  It removes a lane rather than advancing one.
