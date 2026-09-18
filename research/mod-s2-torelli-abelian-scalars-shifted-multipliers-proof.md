---
rg: 2
id: mod-s2-torelli-abelian-scalars-shifted-multipliers-proof
kind: route
title: Split the Torelli action into eigencharacter orbits, read one orbit as a projective representation of its stabilizer, and induce back
target: mod-s2-torelli-abelian-scalars-are-shifted-maslov-multipliers
requires:
  - genus-two-torelli-freely-generated-by-separating-twists
  - mod-s2-real-untwisting-identifies-deligne-norm-parameters
  - deligne-torelli-character-counts-separating-twists
---

Notation as in the target. Inputs:
- **[Mess]** `genus-two-torelli-freely-generated-by-separating-twists`: `K` is free on separating twists,
  one per splitting `x in X`, and two separating curves induce the same splitting iff they differ by an
  element of `K` (same source). Hence `A = K/[K,K]` is free abelian on the classes `[t_x]`, and every
  separating twist `t_c` has class `[t_x]` with `x` the splitting of `c`: if `c = k(c_x)` with `k in K`,
  then `t_c = k t_(c_x) k^-1`. Since `g t_c g^-1 = t_(g(c))` and `g(c)` has splitting `pi(g) x`,
  `g [t_x] g^-1 = [t_(pi(g) x)]` for `g in M`.
- **[ST1]** `deligne-torelli-character-counts-separating-twists`: all separating twists are conjugate in `M`.
- **[U]** `mod-s2-real-untwisting-identifies-deligne-norm-parameters`: there is `f : M -> R` with
  `df = b o pi`, `f|_K = r sigma`, where `sigma(t_s) = 1`, and `b` is normalized (`b(g,e) = b(e,g) = 0`).

Conventions: for a real 1-cochain `F`, `(dF)(g,g') = F(g) + F(g') - F(gg')`. A projective representation
`u` has multiplier `c` when `u(g)u(g') = c(g,g') u(gg')`. Rescaling `u` by `exp(2 pi i psi)` multiplies
`c` by `exp(2 pi i dpsi)`, so the class of `c` in `H^2(.;T)` is well defined.

## Step 0: the untwisting descends to G

- From `df = b o pi` and normalization, `f(e) = 0` and `f(gk) = f(g) + f(k)` for `k in K`.
- `f(g k g^-1) = f(k)`: expand `f(gk g^-1) = f(g) + f(k) + f(g^-1) - b(pi g, pi g^-1)` and use
  `0 = f(e) = f(g) + f(g^-1) - b(pi g, pi g^-1)`.
- `f|_K = r sigma` is a homomorphism, so it kills `[K,K]`. With `f(gk) = f(g) + f(k)`, `f` descends to
  `fbar : G -> R` with `d fbar = b o pibar` and `fbar(y) = r sigma(y)` for `y in A`.
- By [ST1] and conjugation invariance, `sigma([t_x]) = 1` for every `x`. So `sigma : A -> Z` is the
  augmentation `sum n_x [t_x] -> sum n_x`.

## Step 1: the multiplier of a Torelli character

Let `Gamma' <= Gamma` have finite index, `h : X -> R` be `Gamma'`-invariant (extended linearly to `A`),
and `chi : A -> T` be the character with `chi([t_x]) = lambda exp(2 pi i h(x))`. Then:

1. `chi` is invariant under `G' = pibar^-1(Gamma')`: `chi(g y g^-1) = chi(y)` for `g in G'`, by [Mess]
   and invariance of `h`.
2. `chi(y) = exp(2 pi i (alpha sigma(y) + h(y)))` for all `y in A` (check on the basis, both sides are
   multiplicative).
3. Put `F = fbar o s`. Apply `fbar` to `a(g,g') s(gg') = s(g)s(g')`. Since `a(g,g') in A`,
   `fbar(a s(gg')) = fbar(a) + F(gg')`, and `fbar(s(g)s(g')) = F(g) + F(g') - b(g,g')`. Hence
   ```text
   r sigma(a(g,g'))  =  fbar(a(g,g'))  =  (dF)(g,g') - b(g,g').
   ```
4. Fix a real lift of `alpha`. Then on `Gamma'`
   ```text
   chi o a  =  exp(2 pi i ( h o a  -  (alpha/r) b ))  *  exp(2 pi i d((alpha/r) F)).
   ```
   So the class of `chi o a` in `H^2(Gamma';T)` is `exp(2 pi i (Phi_(Gamma')(h) - (alpha/r)[b]))`.
5. Lift independence: by item 3, `(1/r) b = d(F/r) - sigma o a` with `sigma o a` integer valued, so
   `exp(2 pi i (1/r) b)` is a coboundary. Changing the lift of `alpha` by `1` does not change the class in
   `H^2(Gamma';T)`, so condition (TA2) depends only on `alpha in R/Z`.

`h o a` is a 2-cocycle because `a` is the extension cocycle with values in the `Gamma`-module `A`, and `h`
is a `Gamma'`-map to the trivial module `R`. A change of section changes `a` by a twisted coboundary, and
`h o a` changes by `d(h o c)`. So `Phi` is well defined.

## Step 2: (TA1) implies (TA2)

Let `rho : G -> U(d)` with `||rho(t_s) - lambda I|| <= epsilon < 2`.

1. **Eigencharacters.** `rho(A)` is a commuting family of unitaries, so `C^d = direct sum of W_chi` over
   the finitely many characters `chi` of `A` that occur. For `v in W_chi` and `y in A`,
   `rho(y) rho(g) v = rho(g) rho(g^-1 y g) v = chi(g^-1 y g) rho(g) v`. So `rho(g) W_chi = W_(g.chi)` with
   `(g.chi)(y) = chi(g^-1 y g)`.
2. **Finite-index stabilizer.** The `G`-orbit of `chi` lies in the finite set of occurring characters. `A`
   fixes every character, so the stabilizer is `pibar^-1(Gamma_chi)` with `[Gamma : Gamma_chi]` finite.
3. **Small, invariant `h`.** By [ST1], `rho(t_x)` is unitarily conjugate to `rho(t_s)`, so
   `||rho(t_x) - lambda I|| <= epsilon` and every occurring value satisfies `|chi([t_x]) - lambda| <= epsilon`.
   Write `chi([t_x]) = lambda e^(i theta)` with `|theta| <= pi`. Then `2|sin(theta/2)| <= epsilon`, and
   `|sin(theta/2)| >= |theta|/pi` gives `|theta| <= pi epsilon/2`. So `h_chi(x) := theta/(2 pi)` satisfies
   `|h_chi| <= epsilon/4`. It is `Gamma_chi`-invariant: `g in Gamma_chi` means `chi([t_(g^-1 x)]) = chi([t_x])`
   for all `x`, and the principal logarithm is a function of the value.
4. **The projective representation.** For `gamma in Gamma_chi`, `s(gamma)` stabilizes `chi`, so
   `u(gamma) := rho(s(gamma))|_(W_chi)` is a unitary of `W_chi`, and
   `u(gamma) u(gamma') = rho(a(gamma,gamma')) rho(s(gamma gamma'))|_(W_chi) = chi(a(gamma,gamma')) u(gamma gamma')`.
   So `u` is an exact projective unitary representation of `Gamma_chi` of dimension `m = dim W_chi <= d`,
   with multiplier `chi o a`.
5. By Step 1 (with `h = h_chi`, `Gamma' = Gamma_chi`) its class is
   `exp(2 pi i (Phi(h_chi) - (alpha/r)[b]))`. This is (TA2) with `eta = epsilon/4`.

## Step 3: (TA2) implies (TA1)

Let `Gamma'`, `h : X -> [-eta, eta]`, and `u : Gamma' -> U(m)` be given, with multiplier class
`exp(2 pi i (Phi(h) - (alpha/r)[b]))`. Take `chi` as in Step 1.

1. **Normalize the multiplier.** By Step 1(4), the multiplier of `u` and `chi o a` differ by a multiplicative
   coboundary. Rescale `u` by a function `Gamma' -> T` to get `u'` with
   `u'(gamma) u'(gamma') = chi(a(gamma,gamma')) u'(gamma gamma')`.
2. **An honest representation of `G'`.** Every element of `G'` is uniquely `y s(gamma)`, with `y in A` and
   `gamma in Gamma'`. Put `rho'(y s(gamma)) = chi(y) u'(gamma)`. Using
   `(y s(g))(y' s(g')) = y (s(g) y' s(g)^-1) a(g,g') s(gg')`, the invariance of `chi` from Step 1(1), and
   item 1, one checks `rho'(y s(g)) rho'(y' s(g')) = rho'((y s(g))(y' s(g')))`. So `rho'` is a unitary
   representation of `G'` with `rho'(y) = chi(y) I_m`.
3. **Induce.** Let `rho = Ind_(G')^G rho'`, of dimension `[Gamma : Gamma'] m`, pulled back to `M`. Since `A`
   is normal and contained in `G'`, `rho|_A` is the direct sum over coset representatives `g_i` of
   `(g_i . chi) I_m`. So `rho(K)` is diagonal in a fixed basis, hence abelian, and `rho` is Torelli-abelian.
4. **The estimate.** On block `i`, `rho(t_s)` acts by `chi(g_i^-1 [t_s] g_i) = chi([t_(x_i)]) = lambda e^(2 pi i h(x_i))`
   for some `x_i in X` (by [Mess]). Hence `||rho(t_s) - lambda I|| = max_i |e^(2 pi i h(x_i)) - 1| <= 2 pi eta`.

Taking `eta -> 0` gives (TA1). The consequences listed in the target are immediate from the definitions:
a Torelli-abelian `rho` is honest, so `Z_ab <= Z_hon`, and `Z_hon <= Z_op` with (U4) is recorded in
`mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap`.
