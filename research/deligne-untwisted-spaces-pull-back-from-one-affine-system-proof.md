---
rg: 2
id: deligne-untwisted-spaces-pull-back-from-one-affine-system-proof
kind: route
title: Read an untwisting as the family of its inverse holonomies, which is a point of T^Gamma modulo constants, and check that the cocycle identity makes this map equivariant for one twisted shift
target: deligne-untwisted-spaces-pull-back-from-one-affine-system
requires: [deligne-third-floor-failure-is-continuous-untwisting, deligne-covers-of-sp2g-z-have-finite-residual-2z]
---

Notation of the target. All identities are in `T = R/Z`, written additively.

**Imported, verbatim.** From `deligne-third-floor-failure-is-continuous-untwisting` (ESTABLISHED):
- "A **continuous untwisting** on a compact metrizable `Gamma`-space `K` is a continuous map `c : E_3 x K -> T` with
  `c(gh, y) = c(g, h y) + c(h, y)` (with `E_3` acting through `Gamma`) and `c(z, y) = 1/3` for all `y`."
- "`K` is **finitely approximable** if there are finite `Gamma`-sets `X_n` and maps `pi_n : X_n -> K` with
  `max_(x, s in S) d(pi_n(s x), s pi_n(x)) -> 0`."
- "**(U) Reformulation.** `inf_X mu_(1/3)(X) = 0` (the floor fails) iff some finitely approximable compact metrizable
  `Gamma`-space carries a continuous untwisting."

**Standard facts** (no citation node): the cocycle identity for `beta` quoted in the target; Shapiro's lemma for
the coinduced module `Map(Gamma/Lambda, T)`; uniform continuity of continuous maps on compact metric spaces;
Tychonoff.

## Step 1. (A) is an action and (C) an untwisting

`T^Gamma` carries the product topology and `T^Gamma / T` the quotient topology. It is compact and metrizable, since
`T` acts continuously and freely by adding constants. By (A), each coordinate of `g . omega` is one coordinate of
`omega` plus a constant, so each `g` is an affine homeomorphism of `T^Gamma`. For `g, k, h`:

```text
(g.(k.omega))(h) = omega(k^(-1) g^(-1) h) + beta(h^(-1) g, k) + beta(h^(-1), g)
((gk).omega)(h)  = omega(k^(-1) g^(-1) h) + beta(h^(-1), g k).
```

By the cocycle identity with `(a, b, c) = (h^(-1), g, k)`, the difference is the constant `beta(g, k)`. Also
`e . omega = omega`, since `beta(h^(-1), e) = 0`. So (A) is an action on `T^Gamma / T`. It is not one on `T^Gamma`,
and the defect there is `beta`.

(C) is unchanged by adding a constant to `omega`, so it is well defined, and it is continuous. For the cocycle
identity:

```text
c_U(g, h.[omega]) = (h.omega)(e) - (h.omega)(g^(-1))
                  = omega(h^(-1)) + beta(e, h) - omega(h^(-1) g^(-1)) - beta(g, h)
c_U(h, [omega])   = omega(e) - omega(h^(-1)).
```

The sum is `omega(e) - omega((gh)^(-1)) - beta(g, h) = c_U(gh, [omega]) - beta(g, h)`, which is the required
identity.

**Linear part and translation class.** Write `(g omega)(h) = omega(g^(-1) h)` for the shift. Then
`g . omega = g omega + tau(g)` with `tau(g)(h) = beta(h^(-1), g)`, and Step 1 shows that `delta tau` is the constant
cocycle `beta`. The module `T^Gamma = Map(Gamma, T)` is coinduced from the trivial group, so
`H^n(Gamma; T^Gamma) = 0` for `n >= 1`. The long exact sequence of `0 -> T -> T^Gamma -> T^Gamma / T -> 0` then
gives `H^1(Gamma; T^Gamma / T) = H^2(Gamma; T)`, and `[tau]` maps to `[beta]` up to sign. The dual of `T^Gamma` is
`Z[Gamma]`. The annihilator of the constants is the augmentation ideal, so it is the dual of `T^Gamma / T`.

## Step 2. Universality

Let `c` be a continuous `beta`-untwisting on `K`. Setting `g = h = e` in the identity gives `c(e, y) = 0`. Put
`omega_y(h) = -c(h^(-1), y)`. Each coordinate is continuous in `y`, so `Phi_c(y) = [omega_y]` is continuous. For
`g in Gamma`, the identity with the pair `(h^(-1), g)` at `y` reads
`c(h^(-1) g, y) = c(h^(-1), g y) + c(g, y) + beta(h^(-1), g)`. Hence

```text
omega_(g y)(h) = -c(h^(-1), g y) = omega_y(g^(-1) h) + beta(h^(-1), g) + c(g, y) = (g . omega_y)(h) + c(g, y).
```

So `[omega_(g y)] = g . [omega_y]`, and `Phi_c` is a `Gamma`-map. Finally,
`c_U(g, Phi_c(y)) = omega_y(e) - omega_y(g^(-1)) = -c(e, y) + c(g, y) = c(g, y)`.

## Step 3. Only the class matters

If `beta' = beta + delta lambda`, with `(delta lambda)(g, h) = lambda(g) + lambda(h) - lambda(gh)`, then
`c' = c - lambda` satisfies
`c'(gh, y) = c(g, h y) + c(h, y) + beta(g, h) - lambda(gh) = c'(g, h y) + c'(h, y) + beta'(g, h)`. This is a bijection
between the untwistings of `beta` and of `beta'` on the same `K`. Apply it on `K = U_beta` and use Step 2 in each
direction: each of `U_beta` and `U_beta'` maps equivariantly onto the other.

## Step 4. Images, and the subgroup

**Images.** If `Phi : K -> K'` is a continuous `Gamma`-map and `pi_n` approximate `K`, then `Phi o pi_n` approximate
`K'`, since `d(Phi(pi_n(s x)), Phi(s pi_n(x))) -> 0` by uniform continuity of `Phi`. By Steps 1-2, a class
carries an untwisting on some finitely approximable space iff `U_theta` is finitely approximable.

**Subgroup.**
- *Sums.* If `c_i` untwists `beta_i` on finitely approximable `K_i`, then `c_1(g, y_1) + c_2(g, y_2)` untwists
  `beta_1 + beta_2` on `K_1 x K_2`. The diagonal finite `Gamma`-sets `X_n x X'_n` with `pi_n x pi'_n` approximate
  it in the max metric.
- *Negatives.* `-c` untwists `-beta` on the same space.
- *Zero.* A point untwists the class `0`.

**Classes that vanish on a finite-index subgroup.** Suppose `beta` restricts to a coboundary on a finite-index
`Lambda`. The finite set `X = Gamma/Lambda` is compact and trivially finitely approximable. A `beta`-untwisting on
`X` is a 1-cochain `c` of `Gamma` with values in `Map(X, T)` whose coboundary is the constant cocycle `beta`. It
exists because Shapiro's lemma identifies the image of `[beta]` in `H^2(Gamma; Map(X, T))` with
`res_Lambda [beta] = 0`.

## Step 5. The Deligne class

Present `E_3 = Z/3 x_alpha Gamma`, with a normalized `alpha in Z^2(Gamma; Z/3)` and `z = (1, e)`, so that
`(0,g)(0,h) = z^(alpha(g,h)) (0, gh)`. Take an untwisting `c` in the imported sense and put
`c'(g, y) = c((0,g), y)`. Then

```text
c'(g, h y) + c'(h, y) = c((0,g)(0,h), y) = c(z^(alpha(g,h)), gh y) + c((0,gh), y) = alpha(g,h)/3 + c'(gh, y),
```

so `c'` is a `beta`-untwisting for `beta = -alpha/3`. Here `c(z^j, y) = j/3` follows from `c(z, y) = 1/3` and the
identity, since `z` acts trivially on `K`. Conversely, from a `beta`-untwisting `c'`, the formula
`c((j,g), y) = j/3 + c'(g, y)` satisfies the imported identity (the same computation read backwards), and it has
`c(z, y) = 1/3`.

So a compact space carries an untwisting in the imported sense iff it carries a continuous untwisting of
`-theta_D`. By Step 4 and negation, this happens on some finitely approximable space iff `theta_D in M(Gamma)`.
(U) says that happens iff the floor fails. The uniform `delta_0` in item 5 is the negation of the existence of a
sequence with errors tending to `0`. This proves item 5.

**Calibration remark.** By `deligne-covers-of-sp2g-z-have-finite-residual-2z` (ESTABLISHED) with `n = 2`, the
finite residual of the double cover is generated by `2z = 0`. So the double cover is residually finite. Some
finite quotient keeps `z`, and its kernel maps isomorphically onto a finite-index `Lambda`, over which the
metaplectic class splits. By Step 4 that class lies in `M(Gamma)`. The rest of "What this changes" in the target is interpretation, not a claim.
