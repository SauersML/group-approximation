---
rg: 2
id: leavitt-resolvent-derived-units-mod-centre-not-fp
kind: claim
title: The derived unit group of the Leavitt resolvent ring is not finitely presented modulo its centre
distinct_from:
  leavitt-resolvent-derived-units-mod-centre-fp-simple: that is the OPEN assertion that D/Z(D) is finitely presented and simple; this is its negation on the finite-presentation clause, so that assertion is false.
  leavitt-scalar-commutators-block-fp-central-quotients: that is the general obstruction for every ring with an infinite central field and a Leavitt family; this is its instance for the finitely presented ring R_L.
---

**ESTABLISHED** by `leavitt-resolvent-derived-units-mod-centre-not-fp-proof`
(lane proof; referee PASS from `gq-referee-a`, proof-gap lens, report
58d536cf7, and from `gq-referee-b`, citation lens,
`research/artifacts/gq-referee-b-leavitt-scalar-commutators-block-fp-central-quotients.md`,
c81257d90).

**Statement.** Let `R_L` be the ring of
`leavitt-resolvent-ring-is-fp-and-contains-q`, `U = R_L^x` and `D = [U, U]`. Only
its finite presentation data, `Q ⊆ Z(R_L)` and its Leavitt pair are used, not its
simplicity.
Then:
- `D/C` is not finitely presented for any subgroup `C` with `Q^x·1 ≤ C ≤ Z(D)`.
  In particular `D/Z(D)` is not finitely presented.
- The same holds for `U` in place of `D`, and for `E_N(R_L)` with `N >= 2`. The
  `E_N` case additionally rests on `leavitt-gl-equals-el-and-perfect-unit-group`
  (repository-internal Lean node, not checked by the referees).

So `leavitt-resolvent-derived-units-mod-centre-fp-simple` is false, and the route
`gl-n-q-bh-via-leavitt-resolvent-units` does not reach
`gl-n-q-embeds-in-fp-simple-group`.

**Why.** The rational scalars `λ·1`, `λ ∈ Q^x`, are central in `U`. They lie in the
perfect subgroup `L_Q(1,2)^x ≤ U` generated inside `R_L` by the Leavitt family, so
they are commutators of commutators. `Q^x` is not finitely generated. A finitely
presented central quotient would force them into a finitely generated central
subgroup.

**What survives.** A finitely presented simple subquotient of `U` containing
`GL_n(Q)` would have to be `H/M` with `M` not central, or with `H` avoiding a full
copy of `L_Q(1,2)^x` (`leavitt-scalar-commutators-block-fp-central-quotients`,
Consequences).
