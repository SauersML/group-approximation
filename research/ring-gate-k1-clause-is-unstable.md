---
rg: 2
id: ring-gate-k1-clause-is-unstable
kind: claim
title: The ring gate's K_1 clause is stable while the necessary condition is unstable, so failure of stable rational K_1 detection excludes a design only when unstable K_1 injects at that rank
requires: [rational-scalars-obstruct-fp-elementary-hosts, rational-k1-detection-forces-infinite-order-unit-class, frame-designs-for-the-ring-gate-are-bracketed]
distinct_from:
  rational-scalars-obstruct-fp-elementary-hosts: that proves the unstable centre clause and gives the stable kernel as a SUFFICIENT certificate (its part 5); this separates the two, proves the exact comparison in both directions, and audits which landed exclusions are stable-only.
  rational-k1-detection-forces-infinite-order-unit-class: that derives the K_0 consequence from the stable clause; this is about the stable clause versus the unstable one, and derives no K_0 statement.
  frame-designs-for-the-ring-gate-are-bracketed: that lists which frame designs fail the stated budget; this says what such a failure does and does not prove about finite presentation, and names a loophole missing from its (a)-(h).
---

**ESTABLISHED** (lane proof, elementary, not reviewed; no priority claimed).

## Notation

`R` is a nonzero unital ring with a unital map `Q -> R`, `N >= 3`,
`ι : Q^x = K_1(Q) -> K_1(R)`, and

    Λ_N(R) = { λ ∈ Q^x : λ I_N ∈ E_N(R) } .

The *unstable clause* is "`Λ_N(R)` finitely generated"; the *stable clause* is
"`ker ι` finitely generated".

## 1. The comparison

1. **The unstable clause is the necessary one.** If `PE_N(R)` is finitely presented then
   `Λ_N(R)` is finitely generated (`rational-scalars-obstruct-fp-elementary-hosts`, part 2).
   Nothing there requires `ker ι` to be finitely generated.
2. **Stable implies unstable.** `λ ↦ λ^N` maps `Λ_N(R)` injectively into `ker ι`. Indeed
   `λ I_N ∈ E_N(R) ⊆ E(R)` gives `0 = [λ I_N] = N[λ] = ι(λ^N)` in `K_1(R)`, and `λ ↦ λ^N`
   is injective on `Q^x`. A subgroup of a finitely generated abelian group is finitely
   generated, so `ker ι` finitely generated implies `Λ_N(R)` finitely generated. (This
   reproves part 5 of that node without choosing an `s`.)
3. **Unstable implies stable exactly under rank-`N` injectivity.** If
   `GL_N(R)/E_N(R) -> K_1(R)` is injective, then `ker ι ⊆ Λ_N(R)`: `ι(λ) = 0` gives
   `[λ I_N] = N[λ] = 0`, so `λ I_N ∈ E_N(R)` by injectivity. Hence the two clauses are
   then equivalent, up to `N`-th powers. Without injectivity, no implication in this
   direction is available: the gap is exactly `([GL_N, GL_N] ∩ Q^x I_N) / (E_N ∩ Q^x I_N)`
   and its stable analogue.

## 2. Audit of the landed exclusions

The widened gate of `frame-designs-for-the-ring-gate-are-bracketed` asks for `ker ι`
finitely generated, i.e. the stable clause. So:

- **Read as design exclusions, items 1-8 of that node are correct**: a design that also
  declares the stable clause is excluded, and the node says so.
- **Read as non-existence of a finitely presented simple host of that shape, they are not
  yet exclusions.** By item 1 above, the host needs only `Λ_N(R)` finitely generated. A
  ring with `ker ι` not finitely generated, all of whose rational scalars are
  non-elementary at rank `N`, fails the stated budget and is still a candidate host.
- The same distinction applies to clause (c) of
  `ck-sandwich-ring-has-fp-projective-simple-quotient`, which asks for `Z(E_4(U/I))`
  finitely generated. That clause is the unstable one: `Z(E_4(R)) = E_4(R) ∩ {d I_4}`, so
  its rational part is `Λ_4(R)`. It is therefore the correct form, and stable `K_1`
  obstructions do not transfer to it
  (`ck-hole-holds-for-perfect-binary-leavitt-unit-subgroups`, part 2).

## 3. The missing loophole

The list `(a)-(h)` of `frame-designs-for-the-ring-gate-are-bracketed` does not include:

- **(i)** a design with `ker ι` not finitely generated but `Λ_N(R)` finitely generated,
  for some `N >= 3`, i.e. a ring whose rational scalars die in stable `K_1` while staying
  non-elementary at rank `N`.

Such a ring has `GL_N(R)/E_N(R) -> K_1(R)` non-injective on rational scalars, so by item 3
it must have infinite stable range at `N` or a non-`E_N`-perfect `GL_N`. Both are possible
only outside the stably finite world, which is where the gate lives
(`fp-simple-resolvent-ring-with-divisible-unit-class` needs a ring that is not stably
finite). So the loophole is not vacuous for formal reasons.

**What is not claimed.** No such ring is exhibited here, and no obstruction to one is
given. In the two purely infinite hosts on main where both clauses have been computed
(`L_Q(1,2)` and the Leavitt resolvent ring) they fail together, because there
`GL_N = E_N`, hence `Λ_N = Q^x`.
