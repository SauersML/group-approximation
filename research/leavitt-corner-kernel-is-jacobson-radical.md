---
rg: 2
id: leavitt-corner-kernel-is-jacobson-radical
kind: claim
title: The kernel of the corner evaluation is exactly the Jacobson radical of the corner
distinct_from:
  leavitt-corner-one-sided-lift-exists: that asks for an explicit pair of elements; this is a structural hypothesis about an ideal, and it reaches the same conclusion without exhibiting anything, which is why it is kept as a separate lane.
  leavitt-corner-idempotent-unital-surjection: that establishes the corner and its evaluation map; this is an open question about the kernel of that map.
  sofic-radical-soficization: that is an approximation-theoretic radical of a group, the largest quotient visible to sofic approximations; this is the Jacobson radical of a ring, and the two share only the word radical.
artifacts:
  - research/artifacts/kaplansky-direct-finiteness-audit-2026-08-17.md
---

With `A = F_2[R^x]`, `e = [g] + [g^2]`, `pi_e : eAe ->> R` as in
`leavitt-corner-idempotent-unital-surjection`:

    ker(pi_e) = J(eAe),

equivalently `R` is the semiprimitive quotient `eAe / J(eAe)`.

## Why the equality and not a containment

Only `ker(pi_e) subseteq J(eAe)` is needed downstream, but the reverse
containment is free, so the hypothesis may as well be stated in its true form.
`R = L_(F_2)(1,2)` is simple, hence `J(R) = 0` (a unital simple ring has no
proper nonzero ideal and `J` is proper); and a surjective ring homomorphism
carries radical into radical, since `f(1 - sx) = 1 - f(s)f(x)` maps units to
units and surjectivity supplies every `f(x)`.  So `J(eAe) subseteq ker(pi_e)`
unconditionally, and the open content is the other inclusion.

Simplicity is available here in the strong two-sided form
(`LeavittSimplicity.exists_mul_mul_eq_one`: every nonzero element divides `1`
on both sides), which is more than enough.

## Honest assessment

This is the weakest-looking lane of the three and is recorded mainly so the
sufficient conditions are not confused with each other.  Read as an equality
it is a strong demand: it says the corner is, modulo its radical, exactly the
Leavitt algebra — a group-algebra corner whose semiprimitive quotient is a
simple purely infinite ring.  Nothing in this repository suggests the radical
of `e F_2[R^x] e` is that large, and no attempt to compute it has been made.
It is a real route only in the sense that it is a *sufficient* condition that
does not require exhibiting a lift; if someone can compute `J(e A e)` at all,
this is where that computation would land.

## Attempts

**Half of it is already proved, and that half is the reverse containment.**
`J(e A e) subseteq ker(pi_e)` holds unconditionally, by simplicity of `R` plus
the fact that surjections carry radical into radical.  So no work remains on
that side, and the open content is entirely `ker(pi_e) subseteq J(e A e)`.

**Where a first attempt starts, and why it has not been taken.**  The
statement collapses in a revealing way at each end.  If `J(e A e) = 0` — the
default behaviour for group algebras and the case one would guess first — the
claim is *equivalent* to `ker(pi_e) = 0`, that is, to `e A e` being isomorphic
to the Leavitt algebra outright.  If instead `ker(pi_e) = 0` fails, the claim
demands a radical as large as that kernel.  So the whole question is gated on
one computation nobody here has done: **is `ker(pi_e)` zero?**  The
corresponding question one level up is settled —
`leavitt-evaluation-kernel-hits-augmentation-one` gives `ker(pi) != 0`, and
`[u]+[v]+[w]` with `u = 1+s_0t_1`, `v = 1+s_1t_0`, `w = s_0t_1+s_1t_0` is an
explicit three-term witness — but whether the corner sees any of it is open.

**Deferred behind that computation.**  No attempt has been made to compute or
bound `J(e F_2[R^x] e)`, and none should be made before `ker(pi_e)` is
understood, since the two ends of the equality are the same unknown. Compared
with `leavitt-corner-one-sided-lift-exists` this lane is the less promising
one and is kept only because it needs no witness.
