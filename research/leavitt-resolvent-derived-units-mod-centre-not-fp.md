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
(lane proof, not independently reviewed; referee requests sent).

**Statement.** Let `R_L` be the ring of
`leavitt-resolvent-ring-is-fp-simple-of-char-zero`, `U = R_L^x` and `D = [U, U]`.
Then:
- `D/C` is not finitely presented for any subgroup `C` with `Q^x·1 ≤ C ≤ Z(D)`.
  In particular `D/Z(D)` is not finitely presented.
- The same holds for `U` in place of `D`, and for `E_N(R_L)` with `N >= 2`.

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
