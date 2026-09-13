---
rg: 2
id: bilipschitz-proper-power-conjugates-have-zero-periodic-exponents
kind: claim
title: In a group acting by bi-Lipschitz homeomorphisms, an element conjugate to a proper power has zero asymptotic Lipschitz exponents at every periodic point
distinct_from:
  graph-path-almost-automorphism-proper-power-is-equicontinuous: that proves equicontinuity for almost-automorphism groups of graph path spaces through an exact locally constant exponent cocycle; this is only the periodic-point exponent statement, for any bi-Lipschitz action on a metric space, with no cocycle and no equicontinuity.
  rsg-proper-power-conjugate-germs-torsion-at-finite-orbits: that uses virtually cyclic germ groups at rational points whose orbit under the conjugator is finite; this uses only bi-Lipschitz bounds and holds at every periodic point, whatever its orbit under the conjugator.
---

**ESTABLISHED** (elementary; no novelty claimed).

**Setting.** A group `G` acts by homeomorphisms on a metric space `(X, d)`, and
every `h ∈ G` is bi-Lipschitz: `C_h = sup_(x ≠ y) |log d(hx, hy) - log d(x, y)|`
is finite.

**Exponents.** Put `ℓ_h(x, y) = log d(x, y) - log d(hx, hy)` for `x ≠ y`. Let
`h ∈ G` fix a non-isolated point `z`. For `m ≥ 1` put

`a_m(h, z) = liminf_(y → z, y ≠ z) ℓ_(h^m)(z, y)` and
`b_m(h, z) = limsup_(y → z, y ≠ z) ℓ_(h^m)(z, y)`.

The limits `μ^-(h, z) = lim a_m/m` and `μ^+(h, z) = lim b_m/m` exist and lie in
`[-C_h, C_h]`. If `g^p z = z` with `p ≥ 1`, put `ν^±_z(g) = μ^±(g^p, z)/p`. This
does not depend on the period `p`.

**Statement.** Let `f, g ∈ G` and nonzero integers `k, l` with `|k| ≠ |l|`
satisfy `f g^k f^-1 = g^l`. Then `ν^+_z(g) = ν^-_z(g) = 0` at every
non-isolated point `z` that is periodic for `g`.

**In words.** Near a periodic point, the powers of `g` contract or expand
distances only subexponentially.

**Uses.**
- `bilipschitz-finite-nucleus-rsg-proper-power-germs-are-torsion`: at rational
  points of a finite-nucleus RSG, zero exponent forces a finite-order germ.
- `weighted-similarity-proper-power-conjugates-are-equicontinuous`: with exact
  similarity pieces, a pumping argument turns zero periodic exponents into
  equicontinuity.

The proof is `bilipschitz-periodic-exponents-vanish-proof`.
