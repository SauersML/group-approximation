---
rg: 2
id: promislow-no-up-quotient-from-complex-units
kind: route
title: The Promislow group has no unique-product quotient, from its complex units and its relators
target: promislow-group-has-no-unique-product-quotient
requires:
  - unit-conjecture-fails-over-complex-numbers
artifacts:
  - research/artifacts/up-quotient-unit-reduction-2026-09-16.md
---

The full proof is in the artifact, Proposition 5.3, with Lemmas 1 to 3, 5 and
6 proved in Sections 2 and 3. The required claim supplies two facts: `P` is
torsion-free, and `C[P]` has a nontrivial unit.

**(b) `P` does not have unique products.** Over an integral domain `R`, a
group with unique products has only trivial units in `R[G]` (artifact,
Lemma 6). The proof is a minimal-support argument using Strojnowski's lemma,
and needs no literature. With `R = C`, the nontrivial unit of `C[P]` shows that
`P` is not UP.

**(c) Relations.** Put `x = a^2`, `y = b^2`, `z = (ab)^2`. From the relators:
`b x b^-1 = x^-1` and `a y a^-1 = y^-1`, hence `xy = yx`. Conjugation by `ab`
inverts `x` and `y`, so `z` commutes with both. Also
`a^2 bab · bab = x b (a b^2 a) b = x b y^-1 x b = x y^-1 x^-1 y = 1`, which is
equivalent to `a z a^-1 = z^-1`, and then `b z b^-1 = a^-1 z a = z^-1`. The
conjugation signs on `(x, y, z)` are `+--` for `a`, `-+-` for `b` and `--+` for
`ab`. So `L = <x, y, z>` is abelian and normal. In `P/L` the images of `a`, `b`
and `ab` are involutions, so `[P : L] <= 4`.

**(e) Homomorphisms.** Let `phi: P -> M` with `M` UP, hence torsion-free, and
put `N = ker phi`.
- **`N ∩ L = 1`.** Then `N` embeds in `P/L`, so it is finite, hence trivial.
  So `P` embeds in `M` and has UP, which contradicts (b).
- **Otherwise.** Take `1 != m = x^i y^j z^k in N`. The products of `m` with
  its conjugates by `a`, `b` and `ab` are `x^(2i)`, `y^(2j)` and `z^(2k)`, and
  they lie in `N`. `M` is torsion-free, so `phi(x) = 1`, `phi(y) = 1` or
  `phi(z) = 1`. With `alpha = phi(a)` and `beta = phi(b)`:
  - `alpha^2 = 1` gives `alpha = 1`, and the second relator gives
    `beta^4 = 1`;
  - `beta^2 = 1` gives `beta = 1`, and the first relator gives `alpha^4 = 1`;
  - `(alpha beta)^2 = 1` gives `beta = alpha^-1`, and the first relator gives
    `alpha^4 = 1`.

  In each case `phi` is trivial.

QED

As a consistency check,
`experiments/up-quotient-unit-reduction-2026-09-16/promislow_affine_action.py`
verifies the relators and the sign table in the standard affine action on
`R^3`, in exact arithmetic. The proof does not use it.
