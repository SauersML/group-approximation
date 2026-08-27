# Verification record: Bekka, *Operator-algebraic superrigidity for SL_n(Z), n >= 3*

arXiv:math/0609102; published Inventiones mathematicae 169 (2007),
doi:10.1007/s00222-007-0050-5.  Abstract read from the arXiv listing this
session (cairn-quotient-mf, 2026-08-14).  Raised by cairn-literal at
search-summary level; verified here before any node cites it.

## What the abstract states

For `Gamma = SL_n(Z)`, `n >= 3`:

> ... a complete description of the tracial states on the full `C*`-algebra
> of `Gamma` ... the full `C*`-algebra of `Gamma` has **no faithful tracial
> state**.

The superrigidity statement itself: for a homomorphism `pi : Gamma -> U(M)`
into the unitary group of a finite factor with `pi(Gamma)'' = M`, either `M`
is finite dimensional, or a finite-index subgroup `Lambda <= Gamma` has
`pi|_Lambda` extending to a homomorphism `U(L(Lambda)) -> U(M)`.

## What the abstract does NOT state

It does **not** contain the words "residually finite dimensional" and does
not mention the congruence subgroup property.  Those appear in secondary
renderings of this result.  Anyone needing the non-RFD statement as a
*citation* must read the body; what follows is a derivation instead, so no
citation is needed.

## Non-RFD as a one-line consequence (derivation, not a citation)

If `C*(Gamma)` were residually finite dimensional it would carry a separating
family of finite-dimensional representations.  That family may be taken
**countable**: `Gamma` is countable, so `C*(Gamma)` is separable, and from a
countable dense set `(a_i)` one picks `pi_{i,k}` with
`||pi_{i,k}(a_i)|| > ||a_i|| - 1/k`, which separates every `a != 0` by
approximating `a` within `||a||/4` and taking `1/k < ||a||/4`.  Index it as
`(pi_k)` and put

```text
tau = sum_k 2^{-k} tr(pi_k( . )),      tr = normalized matrix trace.
```

Each `tr(pi_k( . ))` is a tracial state, so `tau` is one; and it is faithful,
since `tau(a^*a) = 0` forces `tr(pi_k(a^*a)) = 0`, hence `pi_k(a) = 0`, for
every `k`, whence `a = 0` by separation.  The verified sentence above forbids
such a `tau`.  Hence `C*(SL_n(Z))` is not RFD for `n >= 3`, even though
`SL_n(Z)` is residually finite.

(Countability of the separating family was supplied by cairn-literal; without
it the weighted sum is not defined and the derivation has a gap.)

## Why this does not obstruct MF, and what it does mean

A unital MF algebra `A <= prod M_n / (+) M_n` always carries *a* tracial
state — restrict a limit trace `lim_omega tr_n` of the corona — but that
restriction need not be faithful.  So "no faithful tracial state" is
consistent with MF, and Bekka's theorem does **not** refute MF of the vertex
algebras in `literal-mark-quotient-via-shulman-amalgam`.  What it does is
close the exact finite-dimensional side: whatever supplies MF for
`C*(Z^3 sd SL_3(Z))` must be genuinely asymptotic, which is the
representation-theoretic form of the same wall that
`marked-quotients-not-lef` reaches group-theoretically and
`corona-commutant-no-growth` reaches operator-algebraically.

For the status of the positive question, the relevant sentence is Shulman's
own (verified in `shulman-2603-13564-verified.md`): outside the amenable and
RFD classes "it is not clear when full group C*-algebras are MF or at least
stably finite".
