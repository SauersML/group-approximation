---
rg: 2
id: support-pair-unit-scheme-is-finite-over-z-proof
kind: route
title: Valuative criterion for the unit scheme of a support pair
target: support-pair-unit-scheme-is-finite-over-z
requires: []
---

Notation as in the target. `A` is a finitely generated `Z`-algebra, hence
noetherian. For a commutative ring `R`, the ring maps `A -> R` are the pairs
`(u, v)` in `R[G]` with `supp u in S`, `supp v in T`, `uv = 1` and
`eps(u) = 1`. Such a pair also satisfies `eps(v) = eps(u) eps(v) = eps(uv) = 1`.

**Step 1: valuation rings.** Let `K` be a field, `V` a valuation ring of `K`
with valuation `nu`, maximal ideal `m_V` and residue field `k`, and let
`(u, v)` be a `K`-point of `A`. Then every coefficient of `u` and `v` lies in
`V`.

Both `u` and `v` are nonzero because `uv = 1`.

- **Normalize.** Pick `c in S` with `nu(u_c)` minimal and `d in T` with
  `nu(v_d)` minimal. Put `u' = u_c^(-1) u` and `v' = v_d^(-1) v`. They lie in
  `V[G]`. Their reductions in `k[G]` are nonzero, with coefficient `1` at `c`
  and at `d`.
- **Domain.** `u' v' = lambda` with `lambda = (u_c v_d)^(-1) in K`. The left
  side lies in `V[G]`, so `lambda in V`. If `lambda in m_V`, reducing gives
  `ubar' vbar' = 0` in `k[G]` with both factors nonzero. That contradicts the
  hypothesis on `k`. So `lambda` is a unit of `V`, that is,
  `nu(u_c) + nu(v_d) = 0`.
- **Augmentation.** `eps(u') = u_c^(-1) eps(u) = u_c^(-1)` lies in `V`, so
  `nu(u_c) <= 0`. The same argument with `eps(v) = 1` gives `nu(v_d) <= 0`.
  With the sum `0`, both valuations are `0`, so every `u_s` and `v_t` has
  valuation `>= 0`.

**Step 2: finiteness (item 1).** It suffices that each generator `x` (some
`u_s` or `v_t`) is integral over `Z` in `A`. Then `A` is generated as an
algebra by finitely many integral elements, hence is a finite `Z`-module.

Let `p_1, ..., p_n` be the minimal primes of `A`, and let `K_i` be the
fraction field of `A/p_i`. The composite `A -> A/p_i -> K_i` is a
`K_i`-point, so by Step 1 the image `x_i` of `x` lies in every valuation
ring of `K_i`. Every such ring contains the image of `Z`. The integral
closure of a subring of a field is the intersection of the valuation rings
containing it (Atiyah--Macdonald, Cor. 5.22). So `x_i` satisfies a monic
`f_i in Z[X]` in `K_i`, hence in `A/p_i`.

Then `f_i(x) in p_i` for each `i`, so `f(x) := prod_i f_i(x)` lies in the
intersection of the minimal primes, the nilradical. So `f(x)^N = 0` for some
`N`, and `f^N` is monic. So `x` is integral over `Z`.

**Step 3: items 2 and 3.** Write `A = Z^r (+) F` with `F` finite. Then
`A (x) Q = Q^r` and `A/pA = F_p^r (+) F/pF`, which proves item 3.

For a field `K` of characteristic `0`, `A (x) K` has dimension `r`. So it
has at most `r` maximal ideals, and `A` has at most `r` `K`-points. For
characteristic `p` the same count uses `A (x) K = (A/pA) (x) K`.

By Step 2 the image of `A` in `K` under any point is integral over `Z`, so
every coordinate is an algebraic integer. A point is exactly a normalized
unit on `(S,T)`: `k[G]` is a domain, so `u(vu - 1) = 0` forces `vu = 1` and
`v = u^(-1)`.

**Step 4: item 4.** `A_p := A (x) Z_p` is a finite `Z_p`-algebra. By Hensel's
lemma it is the product of its localizations at its finitely many maximal
ideals, which are the maximal ideals of `A/pA`. Let `B` be the factor at `m`.
`B` is a finite `Z_p`-module with `B/pB = (A/pA)_m`, so by Step 3 applied to
`B`,

    rank_{Z_p} B <= dim_{F_p} (A/pA)_m = ell_p(ubar).

On the other side, `B (x) Qbar_p` is a finite `Qbar_p`-algebra of dimension
`rank_{Z_p} B`. It is the product of the local algebras at its
`Qbar_p`-points, so its dimension is the sum of their lengths.

A `Qbar_p`-point `A -> Qbar_p` takes values in the integral closure `O` of
`Z_p`, by item 2. So it factors through `A_p -> O`. Composing with
`O -> Fbar_p` gives a maximal ideal of `A_p` containing `p`. This ideal is
`m` exactly when the point reduces to `(ubar, vbar)`, which is `F_p`-rational.
So the points reducing to `(ubar, vbar)` are the points of `B`, and their
total length is `rank_{Z_p} B <= ell_p(ubar)`.

**Step 5: item 5.**

- **Local.** The trivial unit `(g, g^(-1))` is a `Q`-point reducing to
  `gbar`, with length `mu(g)`, and length is unchanged by extending scalars to
  `Qbar_p`. If `ell_p(gbar) = mu(g)`, item 4 leaves no room for another point
  reducing to `gbar`. A nontrivial integral unit on `(S,T)` congruent to `g`
  mod `p` would be one, after the sign normalization `eps(u) = 1`.
- **Global.** The total length of all `Qbar`-points is `r`, which is at most
  `dim_{F_p} A/pA` by item 3. If a known list already has total length
  `dim_{F_p} A/pA`, nothing else fits.

**Step 6: item 6.** Let `L <= G` be free abelian of finite index `d`, with
coset representatives `t_1, ..., t_d`, so `K[G] = (+)_i t_i K[L]`. Left
multiplication by `u` is right `K[L]`-linear with matrix `M_u`, where
`u t_j = sum_i t_i (M_u)_{ij}`. The support of `(M_u)_{ij}` lies in the
finite set `E_{ij}(S) = {t_i^(-1) s t_j : s in S} cap L`.

- **Determinant.** If `u` is a unit, `M_u` is invertible over the Laurent
  ring `K[L]`. Its units are the nonzero scalars times monomials, so
  `det M_u = c l_0` with `c in K^x` and `l_0 in L`. `l_0` lies in the finite
  set `D(S)` of `d`-fold products of elements of the `E_{ij}(S)`.
- **Inverse.** `M_{u^(-1)} = c^(-1) l_0^(-1) adj(M_u)`, and the entries of
  `adj(M_u)` are supported in `(d-1)`-fold products. So
  `supp u^(-1) in T(S)`, where `T(S)` is `t_i` times those products times
  `D(S)^(-1)`, over all `i`. `T(S)` is finite and depends only on `S`.
- **Integral units.** A unit of `Z[G]` supported in `S` is, after a sign,
  a `Z`-point of `A_{S, T(S)}`. By item 2 there are at most `r` of them.
  Taking `S = B(r)` in `P` gives `H(r)`, the largest absolute value of a
  coefficient over these finitely many units.
- **Decidability.** A Groebner basis of `I (x) Q` presents `A (x) Q` as a
  finite-dimensional algebra. Its finitely many `Qbar`-points are computable,
  and one can check which are integral. The torsion-free virtually abelian
  hypothesis gives the domain hypothesis by Kropholler--Linnell--Moody (1988).
  QED
