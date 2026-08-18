---
rg: 2
id: leavitt-corner-one-sided-lift-exists
kind: claim
title: A one-sided invertible pair in the Leavitt corner whose defect survives evaluation
distinct_from:
  leavitt-corner-idempotent-unital-surjection: that is the established construction of the corner and its unital surjection; this is the open lifting problem stated inside that corner, and is exactly what the construction does not supply.
  left-invertible-lift-of-s0-in-leavitt-group-algebra: that is the same search run in the whole algebra with the right factor pinned over s_0, which is what the cellular-automaton reading needs; this one runs inside the corner e A e against the corner identity e and pins nothing over pi, so the two have different unknowns, different necessary conditions, and neither implies the other.
  leavitt-rank-three-lift-inverse-support-thirteen: that is a support bound for a factor of the rank-three lift in the whole group algebra; this asks for a pair inside the corner, where the identity is e and the support bound is not known to apply.
artifacts:
  - research/artifacts/kaplansky-direct-finiteness-audit-2026-08-17.md
---

With `A = F_2[R^x]`, `e = [g] + [g^2]` and `pi_e : eAe ->> R` as in
`leavitt-corner-idempotent-unital-surjection`: exhibit `a, b` in `eAe` with

    a b = e        and        pi_e(b a) != 1_R.

**This is the missing theorem of the whole lane.**  It is not a
reformulation of "Kaplansky is false" — it is a specific, finite-looking
identity in one explicitly presented corner, and by
`leavitt-unit-group-algebra-not-directly-finite` it would refute the
conjecture.  The second condition is what makes it usable: `ba != e` alone
would already do, but `pi_e(ba) != 1` is the version one can *check*, since
`pi_e` is evaluation and lands in a ring where the Leavitt normal form
decides equality.

## Why the corner rather than the algebra

Not convenience, though the argument has to be stated carefully.  As recorded
in `leavitt-corner-idempotent-unital-surjection`, the `F_2`-augmentation kills
any hope of realizing the full **Leavitt relations** in `F_2[G]` itself, or in
any corner `fAf` with `eps(f) = 1`.  The corner at `e` has `eps(e) = 0`, so
that obstruction is inactive there — this is the first place in the
construction where the standard two-line no-go stops applying, and it is why
the family route `binary-leavitt-family-lifts-into-unit-corner` has to be
stated here and nowhere more comfortable.

The augmentation does *not* forbid a bare pair with `ab = 1 != ba` in the
whole of `A`; applying `eps` there yields only `eps(a) = eps(b) = 1`.  So this
claim is a corner statement by construction, not by necessity: it is where the
available material points, and a pair found directly in `A` would serve the
same purpose.

## What is known against it

Nothing decisive.  The nearest constraint is
`leavitt-rank-three-lift-inverse-support-thirteen`, which excludes the
smallest completions of the explicit rank-three generator lift in the *whole*
algebra; transporting that floor into the corner is not done and is not
routine, since the corner's identity `e` has support two and its elements are
not free to have arbitrary support patterns.

One strictly stronger target that would settle this is
`binary-leavitt-family-lifts-into-unit-corner` (lift the whole family,
equivalently split `pi_e` by a unital ring section).  There used to be a
second, bypassing this claim entirely via a different route into the same
conclusion — `leavitt-corner-kernel-is-jacobson-radical` — and it is now
refuted (`leavitt-corner-kernel-not-jacobson-radical`), so the corner lane
runs through this claim alone.

## Attempts

**Compress the explicit rank-three lifts, and watch which half survives.**
Take the support-three lifts of `leavitt-rank-three-unit-lift` and push them
into the corner: `a = e t~ e`, `b = e s~ e`.  The *inequality* is then free
and needs no work at all,

    pi_e(b a) = s_0 t_0 != 1_R,

so the second condition of the claim is automatic for any pair lying over
`(t_0, s_0)` in that order — note the order matters, and the opposite
assignment fails the first condition instead.  Everything therefore reduces
to the single equation `a b = e`.

**REFUTED 2026-08-18 — this attempt is dead, not stuck.**  There is no `b` at
all: `leavitt-rank-three-lift-has-no-one-sided-inverse` item 3 shows
`a = e t~ e` has no one-sided inverse in `eAe`.  The reason is that the corner
idempotent's own group element `g` is exactly the third unit `u_3` of the
rank-three lift, so `e` and `t~` are both supported in the virtually free
subgroup `K = (C_2 x C_2) * C_3`, where
`subgroup-supported-one-sided-inverse-rigidity` forces any partner to collapse
back in and make `t_0` a unit.  So the equation `ab - e in ker(pi_e)` below is
not merely hard — it is unsatisfiable for this `a`, and no amount of
kernel-element correction of `b` can help.  **The claim itself survives**: it
quantifies over all pairs in `eAe`, and only candidates whose support
generates a group with directly finite group algebra are excluded.  Applying `pi_e` gives only
`t_0 s_0 = 1`, which is true, so what remains is

    a b - e  in  ker(pi_e),

with no reason for it to vanish.  This is where the attempt dies, and it is
the same wall the whole-algebra lane hits in
`left-invertible-lift-of-s0-in-leavitt-group-algebra`: correcting by kernel
elements, `(a + alpha)(b + beta) = e` with `alpha, beta` in `ker(pi_e)`,
turns the problem into solving one equation in an ideal about which nothing
is known here.

**The kernel is at least not trivial, and one element of it is explicit.**
With `x = s_0t_1`, `y = s_1t_0` as in `leavitt-corner-idempotent-unital-surjection`,
the three elements `u = 1+x`, `v = 1+y`, `w = x+y` are pairwise distinct
units — `w^2 = xy + yx = 1` — and `u + v + w = 0` in characteristic two.  So

    [u] + [v] + [w]   lies in   ker(pi),   and has augmentation 1,

an explicit witness for both parts of `leavitt-evaluation-kernel-hits-augmentation-one`.

**Answered 2026-08-17, and both halves of the answer matter.**  The question
just posed — is `e([u]+[v]+[w])e` nonzero, i.e. does the corner see this
element at all — has the answer **no**: `e k = k e = 0` exactly, certified in
`research/artifacts/verify-s3-corner-2026-08-17.py`.  The corner is blind to
the only kernel element this graph owned, which is why restricting it was
never going to work.

The larger question it gated — is `ker(pi_e) != 0` — also has the answer
**no**, reached from a different direction.
`leavitt-primitive-corner-recursive-extension` embeds the whole extension
`S ->> R` into a primitive subcorner compatibly with evaluation, carrying
`ker(pi)` injectively into `ker(pi_e)`; the image of `z = [1]+[g]+[g^2]` is an
explicit twelve-term **idempotent** of augmentation zero
(`leavitt-corner-kernel-not-jacobson-radical`), and iterating gives an
infinite orthogonal family (`leavitt-recursive-kernel-idempotents`).

So this claim is no longer waiting on that computation.  What it gained is a
description of the ideal the correction has to live in, and the description is
discouraging rather than helpful: `ker(pi_e)` is large, contains idempotents
of augmentation zero, and is not radical, so `alpha, beta` have plenty of room
and no structure that narrows the search.  The one recursive correction the
new embedding makes natural fails at every finite depth, because `lambda` is
injective and group-algebra elements have finite support.  The equation
`(a + alpha)(b + beta) = e` is still the whole problem.

**Not attempted: a bounded search.**  Nothing here has been searched by
machine.  A search would need a presentation of `e A e`, which nobody has
written down; the only quantitative constraint available is
`leavitt-rank-three-lift-inverse-support-thirteen`, and it is a statement
about the whole algebra that is explicitly not known to transfer.

*(2026-08-18.)*  A bounded corner search was run to radius 7 (4604 candidate
group elements) with no solution, and is superseded by the proof above; it is
recorded for the record and nothing depends on it.  The live constraint is no
longer a support bound but a **support-location** bound: by
`subgroup-supported-one-sided-inverse-rigidity`, any surviving `a` must have
support generating a subgroup whose group algebra is not known to be directly
finite — in particular not a sofic one.  A search that enumerates by support
size inside `K` is therefore provably wasted, and the cheapest useful next
step is to find candidates whose support leaves `K`.
