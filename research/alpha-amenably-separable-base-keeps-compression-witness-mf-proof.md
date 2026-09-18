---
rg: 2
id: alpha-amenably-separable-base-keeps-compression-witness-mf-proof
kind: route
title: Push the compression wreath onto the wreath of an amenable HNN quotient, then separate squaring images in F_2 through pro-2 closure of a free factor
target: alpha-amenably-separable-base-keeps-compression-witness-mf
requires:
  - amenable-implies-operator-mf
  - mf-radical-product-and-restricted-sum-formulas
---

Conventions: `t g t^-1 = alpha(g)`, and `V` acts on `X = V/Gamma` by left
multiplication. `K^(X)` is written additively, and `v . f = f(v^-1 .)`.

## 0. Normal form facts in V

Every element of `V` is `t^-m g t^n` with `m, n >= 0` and `g in Gamma`. The
exponent sum `m - n` is the value of the homomorphism `V -> Z` that kills
`Gamma` and sends `t` to 1. If `m = n`, then `t^-m g t^m` lies in `Gamma`
exactly when `g` is in `alpha^m(Gamma)`. The reason is that
`t^m d t^-m = alpha^m(d)` gives `Gamma = t^-m alpha^m(Gamma) t^m`, and
conjugation by `t^m` is injective. The form `t^-m g t^n` is the standard
Britton normal form for ascending HNN extensions.

In particular `gamma0 t Gamma = t Gamma` if and only if
`t^-1 gamma0 t in Gamma`, if and only if `gamma0 in alpha(Gamma)`. So `b != 0`.

## 1. (A): every finite quotient kills b

Let `q : W -> Q` be a homomorphism to a finite group. Since `Q` is finite,
`q(t Gamma t^-1) = q(alpha(Gamma))` is contained in `q(Gamma)` and has the same
cardinality as `q(Gamma)`, because conjugation by `q(t)` is a bijection. So
the two sets are equal, and `q(gamma0) = q(t) q(g') q(t)^-1` for some `g'` in
`Gamma`.

The lamp `e = k delta_Gamma` is fixed by `Gamma`. We have
`delta_{gamma0 t Gamma} = (gamma0 t) . e` and `delta_{t Gamma} = t . e`, so

`q((gamma0 t) . e) = q(t g' t^-1 t) q(e) q(t g' t^-1 t)^-1 = q(t g') q(e) q(t g')^-1 = q(t) q(e) q(t)^-1`.

The last step uses that `g'` fixes `e`. The two lamps have the same image, so
`q(b) = 1`. This is the finite-quotient collapse; no hypothesis on
`Gamma` is used.

## 2. The amenable HNN quotient attached to N

Let `N` be in `N(Gamma, alpha)`, let `P = Gamma/N`, and let `pi` be the
quotient map.

- `alpha(N)` is contained in `N` because `alpha^-1(N) = N`. So `alpha` induces
  `alpha_P` on `P`.
- `alpha_P` is injective: `alpha(g) in N` forces `g in N`.
- Let `V_P` be the ascending HNN extension of `(P, alpha_P)`. It is
  `N_P x| Z`, where `N_P` is a directed union of copies of `P`. So `V_P` is
  amenable, and `P` embeds in it.
- `phi : V -> V_P`, given by `g -> pi(g)` and `t -> t`, respects the defining
  relations, so it is a homomorphism. It maps `Gamma` onto `P`.
- `X -> X_P = V_P/P`, given by `v Gamma -> phi(v) P`, is well defined and
  `phi`-equivariant.
- For abelian `K`, pushforward along this map,
  `(phi_* f)(y) = sum of f(x) over x mapping to y`, is an equivariant
  homomorphism `K^(X) -> K^(X_P)`.

So `Phi(f, v) = (phi_* f, phi(v))` is a homomorphism

`Phi : W -> W_P = K^(X_P) x| V_P`.

`W_P` is abelian-by-amenable, hence amenable.

Separation rule. Take `u = t^-m g t^n` in `V \ Gamma`. The point `phi(u)` is
outside `P` in either of two cases:

- `m != n`: the `Z`-degree of `phi(u)` is `m - n`, which is nonzero;
- `m = n` and `g not in alpha^m(Gamma) N`: the normal form in `V_P` gives
  `phi(u) in P` if and only if `pi(g) in alpha_P^m(P) = pi(alpha^m(Gamma))`,
  that is, if and only if `g in alpha^m(Gamma) N`.

## 3. (B)

Take `N` with `gamma0 not in alpha(Gamma) N` and set `u = t^-1 gamma0 t`.
Section 2 gives `phi(gamma0 t) P != phi(t) P`. So `phi_* b` equals `k` at one
point of `X_P`, equals `-k` at another, and is 0 elsewhere. Thus
`Phi(b) != 1` in the amenable group `W_P`.

By amenable-implies-operator-mf, `W_P` is MF. So `b` is not in `Rad_MF(W)`.

## 4. (C)

Take `w = (f, v) != 1` in `W`. There are finitely many conditions to meet.

- If `v != 1`, write `v = t^-m g t^n`. If `m != n`, any `phi` separates `v`
  from 1 through the `Z`-degree. If `m = n`, then `g != 1`, and there is an `N`
  with `g not in N` because `{1}` is `N`-closed. Then `phi(v) = t^-m pi(g) t^m`
  is nontrivial, since `P` embeds in `V_P`.
- If `v = 1`, then `f != 0`. Choose a point `x0 = v0 Gamma` with
  `f(x0) != 0`, and list the other points `x_i = v_i Gamma` of the support of
  `f`. For each `i`, the element `u_i = v0^-1 v_i` lies outside `Gamma`. By
  Section 2 and the closure hypothesis at the relevant `m`, there is an `N_i`
  with `phi(u_i)` outside `P`.

The family `N(Gamma, alpha)` is closed under finite intersections. Replacing
`N` by a smaller member keeps every non-membership `g not in alpha^m(Gamma) N`.
So one `N` meets all the conditions at once. For that `N`, the map `X -> X_P`
is injective on the support of `f`, so `(phi_* f)(phi(v0) P) = f(x0) != 0` and
`Phi(w) != 1`.

So `W` is residually amenable. Each amenable quotient is MF by
amenable-implies-operator-mf. `W` is countable, so
mf-radical-product-and-restricted-sum-formulas ("every countable group which
is residually MF is MF") gives that `W` is MF, and `Rad_MF(W) = 1`.

## 5. (D): the free group with the squaring map

Let `F = F_2 = <a, b>`, `alpha(a) = a^2`, `alpha(b) = b^2`.

The family used is the integral Magnus kernels. Let `S = Z<<X, Y>>` be
noncommutative power series, and let `J_n` be the ideal of series all of
whose terms have degree at least `n`. Let `mu : F -> S^x` be the map
`a -> 1 + X`, `b -> 1 + Y`, and set `N_n = { g : mu(g) - 1 in J_n }`.

1. **alpha is injective and not surjective.** By step 4 with `m = 1`, `a^2`
   and `b^2` are part of a free basis of a subgroup, so they freely generate
   `alpha(F)`. The image lies in the kernel of `F -> (Z/2)^2`, so `a` is not
   in `alpha(F)`.
2. **N_n is in N(F, alpha).**
   - `N_n` is the kernel of `F -> (S/J_n)^x`, so it is normal.
   - `F/N_n` embeds in the group `1 + (X, Y)/J_n`. The subgroups
     `1 + J_k/J_n` form a central series of that group, because
     `(1+u)(1+v) - (1+v)(1+u) = uv - vu` lies in `J_(i+j)` for `u` in `J_i`
     and `v` in `J_j`. So `F/N_n` is nilpotent, hence amenable.
   - Let `tau` be the continuous ring endomorphism of `S` with
     `X -> (1+X)^2 - 1 = 2X + X^2` and `Y -> 2Y + Y^2`. Then
     `mu o alpha = tau o mu`: both are homomorphisms, and they agree on `a`
     and `b`.
   - `tau` maps `J_n` into `J_n`. Conversely, if `f` has nonzero lowest
     homogeneous part `f_d` with `d < n`, then the degree-`d` part of `tau(f)`
     is `f_d(2X, 2Y) = 2^d f_d != 0`, because `Z` is torsion-free. So
     `tau^-1(J_n) = J_n`.
   - Hence `mu(alpha g) - 1 = tau(mu(g) - 1)` lies in `J_n` exactly when
     `mu(g) - 1` does. That is, `alpha^-1(N_n) = N_n`.

   The `N_n` decrease, so this subfamily is closed under intersections.
2b. **Every finite 2-group quotient of F contains some N_n.** Let
   `q : F -> P` be onto a finite 2-group. The augmentation ideal `w` of
   `F_2[P]` is nilpotent. This is proved by induction on `|P|`. Pick a central
   `z` of order 2. By induction `w^k` lies in the kernel `(z-1) F_2[P]` of
   `F_2[P] -> F_2[P/<z>]`. Since `z - 1` is central and `(z-1)^2 = z^2 - 1 = 0`,
   we get `w^(2k) = 0`.

   Say `w^n = 0`. The ring map `S -> F_2[P]` with `X -> q(a) - 1` and
   `Y -> q(b) - 1` is well defined: reduce mod 2, and every monomial of degree
   at least `n` maps to 0. It kills `J_n`, and it sends `mu(g)` to `q(g)`. So
   `g in N_n` gives `q(g) = 1` in `F_2[P]`, hence in `P`. Thus `N_n` is
   contained in `ker q`.
3. **F is residually a finite 2-group, and {1} is N-closed.** Use the mod-2
   Magnus map, with a complete proof.
   - Let `R = F_2<<X, Y>>` be noncommutative power series, and let `I_n` be
     the ideal of series with every term of degree at least `n`.
   - Send `a -> 1 + X` and `b -> 1 + Y`. These are units, so this defines a
     homomorphism `F -> R^x`.
   - The group `1 + (X, Y)/I_n` of units of `R/I_n` has order a power of 2, so
     reducing mod `I_n` gives maps from `F` into finite 2-groups.
   - Take a reduced word `w = z_1^(e_1) ... z_r^(e_r)` with consecutive letters
     `z_i` in `{a, b}` different and `e_i != 0`. Write `e_i = 2^(j_i) u_i`
     with `u_i` odd.
   - In characteristic 2, `(1+X)^(e) = (1 + X^(2^j))^u = 1 + X^(2^j) +` (terms
     of higher degree in `X` alone). This holds for negative `u` as well.
   - Multiplying the `r` factors, the monomial
     `Z_1^(2^(j_1)) ... Z_r^(2^(j_r))` (with `Z = X` or `Y`) arises only from
     the `2^(j_i)`-terms. Consecutive blocks use different variables, so a
     monomial splits uniquely into single-variable blocks. Its coefficient is
     therefore 1.
   - So `w` survives mod `I_n` for `n > sum_i 2^(j_i)`.

   If `g != 1`, a finite 2-group quotient `F/U` separates it. By step 2b some
   `N_n` lies in `U`, so `g` is not in `N_n`. Hence the intersection of the
   `N_n` is trivial, and `{1}` is `N`-closed.
4. **alpha^m(F) is a free factor of `K_m = ker(F -> (Z/2^m)^2)`.** The Schreier
   graph of `K_m` is the `2^m x 2^m` torus grid, with `a`-edges horizontal and
   `b`-edges vertical. Take as spanning tree the vertical `b`-path from
   `(0,0)` up to `(0, 2^m - 1)` together with every horizontal `a`-path from
   `(0,y)` to `(2^m - 1, y)`. That is `4^m - 1` edges on `4^m` vertices, with no
   cycle, so it is a tree.
   - The non-tree `a`-edge from `(2^m - 1, 0)` to `(0, 0)` gives the Schreier
     generator `a^(2^m)`.
   - The non-tree `b`-edge from `(0, 2^m - 1)` to `(0, 0)` gives `b^(2^m)`.

   Schreier generators of non-tree edges form a free basis of `K_m`, so
   `alpha^m(F) = <a^(2^m), b^(2^m)>` is a free factor of `K_m`.
5. **alpha^m(F) is closed in the pro-2 topology of F.**
   - A free factor `H` of `K_m` is a retract, with retraction `r`.
   - Homomorphisms are continuous for pro-2 topologies, since preimages of
     normal subgroups of 2-power index are such.
   - `K_m` is a subgroup of `F`, so step 3 makes it residually a finite
     2-group, and its pro-2 topology is Hausdorff.
   - So `H = {k : r(k) = k}` is closed in `K_m`: it is the equalizer of two
     continuous maps into a Hausdorff space.
   - Every open subgroup `U` of `K_m` for the pro-2 topology contains an open
     subgroup that is normal in `F` with 2-power index. Take the intersection
     of the finitely many `F`-conjugates of a normal 2-power-index subgroup of
     `K_m` inside `U`; it is normal in `F`, and `F/core` is a 2-group by a
     2-group.
   - Hence `H`, an intersection of `K_m`-open subgroups, is closed in the
     pro-2 topology of `F`. Elements outside `K_m` are separated by `K_m`
     itself, which is normal in `F` of index `4^m`.
6. **Separation.** Take `g not in alpha^m(F)`. By step 5 there is a normal
   `U` in `F` with `F/U` a finite 2-group and `g not in alpha^m(F) U`. By
   step 2b some `N_n` lies in `U`. Hence `g not in alpha^m(F) N_n`.

So `alpha^m(F)` is `N`-closed for every `m`, and (C) applies. The other
properties are immediate:

- `W` is generated by `a`, `b`, `t` and one lamp.
- `W` contains `F_2`.
- The quotients `W_P` are abelian-by-(nilpotent-by-Z), hence solvable, so `W`
  is residually solvable.
- By (A) `b` dies in every finite quotient, so `W` is not residually finite.

## 6. (E)

If `P = Gamma/N` is finite, the injective map `alpha_P` is bijective. Then
`alpha(Gamma) N = Gamma`, and `gamma0` is in `alpha(Gamma) N`. A finitely
generated group with property (T) has only finite amenable quotients, since an
amenable (T) group is compact, hence finite. Then every `N` in
`N(Gamma, alpha)` has `alpha(Gamma) N = Gamma`. A non-amenable simple group
has `N(Gamma, alpha)` equal to `{Gamma}`.
