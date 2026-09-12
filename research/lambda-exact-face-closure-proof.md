---
rg: 2
id: lambda-exact-face-closure-proof
kind: route
title: Schur support and the exact sixteen-element kernel join give the regular-type Kazhdan floor
target: lambda-exact-face-of-the-collapse-closes
requires:
  - two-power-sector-conjugator-dichotomy
  - odd-congruence-lambda-exact-sector-collapses
  - depth-shifted-regular-overlap-is-exactly-one-sixteenth
---

Fix a level `a >= 3` of the tower, `G = image of Lambda in the
level-a quotient`, `d` the representation dimension; all norms
normalized Hilbert--Schmidt.  Write `A(gamma), B(gamma)` for the
images of `gamma` and `h gamma h^(-1)`.

**Step 1 (the bimodule representation and (T)).**
`rho(gamma) xi = sigma_a(A-side gamma) xi sigma_a(B-side gamma)^(-1)`
is a genuine unitary representation of `Lambda_0` on the
Hilbert--Schmidt space (both assignments are homomorphisms into the
unitaries of the level).  A unitary `V` with intertwining defect
`eta = max_i || rho(A_i) V - V rho'(B_i) ||`-style is an
`(A, eta)`-almost-invariant unit vector, so by the Kazhdan pair
`(A, epsilon_0)` of `Lambda_0`,

```text
dist_2(V, Inv) <= eta / epsilon_0,                              (LEP1)
```

where `Inv = { xi : sigma(A(gamma)) xi = xi sigma(B(gamma)) }` is
the space of intertwiners `Hom(lambda compose B, lambda compose A)`
inside the matrix space.

**Step 2 (structure of the two representations).**  As
representations of `Lambda_0`, the `A`-side is inflated from the
finite quotient `Q_A = Lambda_0 / ker A` and decomposes as a
multiple of copies of representations of `Q_A`; in the regular-type
module every constituent inflated from `Q_A` occurs with the
balanced multiplicities of `[G : im A]` copies of `Reg(Q_A)`, and
in a general module the argument below uses only the following two
facts, valid for any `sigma_a`: (i) every `A`-side constituent
factors through `Q_A` and every `B`-side constituent through `Q_B`;
(ii) the dimension fraction of the `B`-side isotypic part factoring
through any quotient `Q` of `Q_B` is at most
`(dim of Q-part of Reg(Q_B)) / |Q_B| = |Q| / |Q_B|` in the
regular-type case, and in general at most the maximum over
constituents, which the regular-type towers of the sector realize.
(The claim is stated for towers where this fraction bound holds —
regular type and weights uniformly comparable to Plancherel.  An
earlier draft asserted that the regular limit trace FORCES this;
that is not proved: pointwise regularity does not obviously control
isotypic weight concentration, because averaging over growing kernel
subgroups meets sign cancellations.  The gap is isolated as the
shallow-weight escape lemma in the claim's scope paragraph.)

**Step 3 (Schur support).**  A `Lambda_0`-constituent common to the
two sides factors through both `Q_A` and `Q_B`, hence through
`Q_AB = Lambda_0 / (ker A . ker B)` (the join of two normal
subgroups is normal).  By Schur's lemma every intertwiner
`xi in Inv` vanishes between non-isomorphic constituents, so
`xi = P_A xi P_B` where `P_B` is the projection onto the `B`-side
`Q_AB`-factoring part; therefore

```text
|| xi ||_2^2 = tr(P_B xi^* xi P_B)/d <= || xi ||_op^2 . tr(P_B)/d.
```

**Step 4 (the exact one-sixteenth bound).**  Depth bookkeeping for
`ker B = { lambda : h lambda h^(-1) = 1 mod 2^a }`: conjugation by
`h` scales the off-diagonal entries by `2^(w)` with weights
`w = +1, +2, +1, -1, -2, -1` on the six root directions and `0` on
the diagonal, so the `B`-kernel's congruence depths are skewed by
exactly those weights.  The full image of `ker B` in `Q_A` is the
upper-unitriangular packet with `12,23` entries in
`2^(a-1) Z/2^a` and `13` entry in `2^(a-2) Z/2^a`; it has order
`2*2*4=16`.  Transpose-inverse exchanges the two tuples, so
`|Q_B|=|Q_A|`.  Therefore the common fraction is exactly

```text
tr(P_B)/d = |Q_AB| / |Q_B| = 1/16.                              (LEP2)
```

**Step 5 (mean ergodic bound and conclusion).**  The invariant
projection of a unitary lies in the closed convex hull of its
`rho`-orbit (Alaoglu--Birkhoff mean ergodic theorem), which consists
of products of unitaries, so `|| P_Inv(V) ||_op <= 1`; with Steps 3
and 4, `|| P_Inv(V) ||_2^2 <= 1/16`, so `dist_2(V, Inv) >=
sqrt(1 - 1/16) = sqrt(15)/4`.  Combining with `(LEP1)`:

```text
eta >= epsilon_0 . sqrt(15)/4                                   (LEP3)
```

for every unitary at every level — the uniform floor `(LE1)`.  An
exact conjugator in a 2-power ultraproduct would give unitaries of
vanishing defect, contradicting `(LEP3)`; the consolidation bullet
of `two-power-sector-conjugator-dichotomy` reduces every
bounded-gauge corrector to the same conjugacy question, and the
coprime sector is `odd-congruence-lambda-exact-sector-collapses`.
Together the canonical (regular-type) `Lambda`-exact sectors of
`(RC3)` are closed; per the claim's scope paragraph, the surviving
enemy is confined to uniform outliers or to `Lambda`-exact
microstates of genuinely non-regular isotypic weight profile.
