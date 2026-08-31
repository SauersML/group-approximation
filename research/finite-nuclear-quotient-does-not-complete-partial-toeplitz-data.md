---
rg: 2
id: finite-nuclear-quotient-does-not-complete-partial-toeplitz-data
kind: claim
title: Finite nuclear quotients do not complete arbitrary partial Toeplitz data
distinct_from:
  exact-core-multiplicative-domain-does-not-descend-to-normal-quotient: that gives a ucp map on a free-group algebra whose minimal dilation detects a killed normal conjugate; this gives a quantitative nonextension gap for partially positive data even when the desired quotient algebra itself is finite-dimensional and nuclear.
  finite-positive-definite-window-is-a-relative-corner-selector: that proves a full positive-definite finite-group table produces the desired corner; this shows that facewise positivity on a generating pattern does not produce that full table.
---

Let

```text
G = C2 x C2 = <a,b | a^2=b^2=1, ab=ba>,
Delta = {1,a,b}.
```

On the two-dimensional Hilbert space, put

```text
X = [[0,1],[1,0]],       Z = [[1,0],[0,-1]]
```

and define the partial operator-valued function

```text
f(1)=I,        f(a)=X,        f(b)=Z.                   (FNQ1)
```

Then `f` is positive definite on the positivity domain `Delta`.
Nevertheless, if `F:G -> M_2` is a normalized positive-definite function
and

```text
eta = max{ ||F(a)-X||_(2,2), ||F(b)-Z||_(2,2) },
```

then

```text
2 <= 4 eta + 2 sqrt(2 eta),
eta >= (3-sqrt(5))/4.                                  (FNQ2)
```

In particular `f` has no positive-definite extension to `G`, and it
cannot even be approximated by restrictions of full positive-definite
functions with normalized Hilbert--Schmidt error tending to zero.

The target algebra is

```text
C*(G) is isomorphic to C^4.
```

It is finite-dimensional, nuclear, locally reflexive, quasidiagonal, RFD,
MF, and has both LP and LLP. Thus none of those ambient properties, alone
or in combination, upgrades arbitrary facewise-positive generator data to
the full finite Toeplitz certificate required by
`finite-positive-definite-window-is-a-relative-corner-selector`.

The missing hypothesis is complete-order compatibility with the concrete
group Fourier system, equivalently positivity after all difference
identifications and translated relation rows have been inserted. LLP
lifts a ucp map already defined on a concrete operator system; it does not
turn a map which is only ucp on the universal coproduct of its faces into
such a map. MF and quasidiagonality construct existential matrix models of
the algebra or of a scalar trace; they do not repair a prescribed
matrix-valued partial function.

This is the finite quantitative counterpart of
Kakariadis--Leimbach--Todorov--van Suijlekom,
*Operator systems and positive extensions over discrete groups*,
[arXiv:2603.29958](https://arxiv.org/abs/2603.29958), especially Example
5.4, Corollary 5.9, and Theorem 5.21. Their two-axis domain in
`Z^2` separates the universal face coproduct from the concrete commuting
Fourier system; the Pauli square makes the obstruction finite and gives the
explicit gap (FNQ2).

For the authenticated Iwahori problem this is a firewall, not a
counterexample. Its prescribed microstates satisfy additional arithmetic
relations which may force the needed complete-order compatibility. What
cannot be used as the forcing argument is LLP, MF, local reflexivity,
quasidiagonality, or finite-dimensional nuclearity by itself. A successful
proof must exploit those arithmetic relations to control the complete
moving quotient table (equivalently every translated normal-closure row).
The Iwahori gate and the nonhyperlinear-group root remain open.

DERIVATION
pauli-square-positive-extension-gap-proof
