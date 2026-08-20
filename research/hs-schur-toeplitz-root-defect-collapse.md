---
rg: 2
id: hs-schur-toeplitz-root-defect-collapse
kind: claim
title: Toeplitz direct finiteness kills the Schur root mark in normalized-HS microstates
artifacts:
  - research/artifacts/schur-toeplitz-root-defect-envelope-2026-08-20.md
distinct_from:
  leavitt-steinberg-hs-stable: that asks for correction of every almost representation of the simple Leavitt Steinberg group; this asks only for collapse of one named root in the packet-headed Toeplitz envelope.
  finite-window-decoder: that seeks four contractions on a positive-density Pauli corner; this may instead propagate the finite-index root kernel through the one-sided Toeplitz coefficient recurrence.
  toeplitz-tail-retains-contextual-schur-density: that asks for a conditional-expectation survive-or-recurse theorem for packet commutants; this asks for the equivalent coefficient-root defect to disappear directly.
---

OPEN. For the explicit finite presentation and word

```text
(G_f,w_f)=(St_5(R_f),x_12(P_f))
```

from `schur-toeplitz-root-mark-is-fd-invisible`, prove a dimension-free
modulus `omega(epsilon)->0` such that every normalized-HS
`epsilon`-representation on the defining generators satisfies

```text
||phi(w_f)-1||_2 <= omega(epsilon).                         (HST1)
```

The exact proof intersects finite-index kernels of exponent-`p` root groups
and then uses direct finiteness of the resulting finite coefficient quotient.
The approximate proof must replace this dimension-dependent intersection by
a weighted root-character argument. A sufficient recurrence is a sequence
`a_n<=1` measuring the mass on which the transported coefficient ideal still
detects `P_f`, with

```text
a_0 >= c||phi(w_f)-1||_2^2-C sqrt(epsilon),
a_n <= lambda a_(n+1)+C(n+1)^k sqrt(epsilon),
0<lambda<1.                                                (HST2)
```

The relation `P_f=1-xy` supplies the proper-corner orientation exactly; no
linear combination of represented packet words has to be converted into one
group word. Steinberg additivity and multiplication transport the coefficient
through roots. The unresolved step is a dimension-free weighted substitute
for intersecting all root kernels, or equivalently a first-hit decomposition
whose discarded root-character masses are summable.

Establishing `(HST1)` makes `G_f` nonhyperlinear: hyperlinearity would give
microstates converging to the canonical delta trace, while the nontrivial
order-`p` word `w_f` has fixed positive delta-trace distance from the
identity.

Mandatory falsification test: the argument must use the one-sided relation
and the strict defect `P_f`. Any proof based only on the finite packet and
Steinberg covariance would contradict the finite-overgroup and direct
relator-certificate barriers.

## Attempts

- **Intersect rounded root kernels.** For a fixed finite root window, the
  exponent-`p` commuting families can be rounded and jointly diagonalized.
  This does not reproduce the exact proof: the additive codimension of the
  joint kernel grows with matrix dimension, and the word depth required to
  show that its generated ideal contains `P_f` has no uniform bound. A
  forward union bound therefore loses exactly the amplification-invariant
  information the construction needs.
- **Direct relator telescoping.** Writing `x_12(P_f)` as a product of root
  words does not put `P_f` in the defining relator ideal. Such a certificate
  would kill the nonzero mark algebraically and contradict the faithful
  model of `schur-idempotent-is-an-injective-toeplitz-defect`.
- **Active first-hit attack.** In `R_f`, put

  ```text
  e_n=x^n P_f y^n,                 n>=0.
  ```

  The Toeplitz relations give `e_n^2=e_n` and `e_n e_m=0` for `n!=m`.
  Steinberg commutators name `x_ij(e_n)` with word cost polynomial in `n`.
  Decompose the rounded additive-root PVM by the first `n` on which its
  character detects `e_n`. Orthogonality should make the first-hit masses
  summable. The missing inequality is transport: a fixed positive fraction
  of the mass detecting `P_f=e_0` must either pay a defining Steinberg
  relator or move to the next previously unseen first-hit layer. Proving that
  statement with polynomial word loss yields `(HST2)` after exponential
  weighting.
- **Why ordinary Toeplitz truncation is not a counterexample by itself.** In
  truncated unilateral-shift matrices, the rank-one defect has vanishing
  normalized trace. Here the canonical root mark has fixed delta-trace
  distance from the identity. A countermodel must therefore decouple root
  phase mass from coefficient-defect rank; locating or excluding precisely
  that decoupling is the root-character transport problem above.
