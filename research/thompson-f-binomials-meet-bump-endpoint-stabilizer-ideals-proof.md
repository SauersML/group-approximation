---
rg: 2
id: thompson-f-binomials-meet-bump-endpoint-stabilizer-ideals-proof
kind: route
title: Conjugates by the endpoint stabilizer stay in the product of bump groups; transport each bump to (0,1) and run the one-bump count in all bumps at once with the powers of each bump factored out
target: thompson-f-binomials-meet-bump-endpoint-stabilizer-ideals
requires: [thompson-f-one-bump-binomials-have-common-multiples]
---

Notation as in the target. Composition is right to left, so `t^-1 g t` has support
`t^-1(supp g)`. A finite direct product `F^k` is isomorphic to a subgroup of `F` (for
instance `W_g`), so it is left-orderable and its group rings over fields are domains.

Quoted, and used only as stated there:
- from `thompson-f-one-bump-binomials-have-common-multiples-proof`: Step 0 (the weighted
  coset test), Steps 3 and 4 of Proposition 1 (the survey's Lemma 3.8 transported to
  `F_[1-2^-j,1]`, and `h -> g^-1 h g` acting as `phi^n` near `1`), Lemma 2 (the index-`m`
  conjugacy `psi`), and the dyadic PL identification `theta : [p,q] -> [0,1]` of Item 1;
- from `thompson-f-twisted-x0-binomial-is-ore-with-every-element-proof`, Step 5: the
  normal forms of the positive monoid `M`, the insertion bound, and the estimate
  `|B| <= (4^(D+1)/3)|A_0|` below.

**Step 1 (conjugates by `W_g` stay in the product of bump groups).**
- An element fixing two consecutive points `z < z'` of `∂_g ∪ {0,1}` restricts to a
  dyadic PL homeomorphism of `[z, z']`, so `W_g = prod F_[z,z']` over consecutive pairs.
- Put `E_g = F_[p_1,q_1] × ... × F_[p_k,q_k]` and let `C_g` be the product of the other
  factors, the groups of the nondegenerate fixed intervals of `g`. Then `W_g = E_g × C_g`.
- Since the `p_i, q_i` are dyadic, `g = g_1 ... g_k` with `g_i` in `F_[p_i,q_i]`
  one-bump on `I_i`. Elements of `C_g` have supports disjoint from `supp g`, so they
  commute with `g` and with `E_g`.
- For `t = t_E t_C` with `t_E` in `E_g`, `t_C` in `C_g`:
  `t^-1 g t = t_E^-1 g t_E = prod_i t_(E,i)^-1 g_i t_(E,i)`. Each factor is one-bump on
  `I_i`, because `t_(E,i)` fixes `p_i` and `q_i`.

**Step 2 (reduction to Claim P).** *Claim P:* for every `c = c_1 ... c_k` with `c_i`
one-bump on `I_i`, every `lambda` in `K^x` and every nonzero `y` in `K[E_g]`,
`(1 + lambda c) K[E_g] ∩ y K[E_g] ≠ 0`.
- Assume P. List `supp b = {t_1, ..., t_s}` and put `c_l = t_l^-1 g t_l`, which lies in
  `E_g` by Step 1. Put `v_1 = 1 + lambda c_1`. Given a nonzero `v_(l-1)`, P gives a
  nonzero `v_l` in `(1 + lambda c_l) K[E_g] ∩ v_(l-1) K[E_g]`. Then `v = v_s` is nonzero
  and lies in every `(1 + lambda c_l) R`.
- Since `t_l (1 + lambda c_l) = (1 + lambda g) t_l`, `b v = sum_l b(t_l) t_l v` lies in
  `(1 + lambda g) R`. It is nonzero because `R` is a domain. For `b s`, `b s R = b R`.
- Item 2: `alpha u + beta w = alpha (1 + (beta/alpha) g) u`, and right unit factors do
  not change principal right ideals.

**Step 3 (normalization).** Fix `c` as in P. For each `i`, conjugation by `theta_i`
is an isomorphism `F_[p_i,q_i] -> F` taking `c_i` to a one-bump element on `(0,1)`. If
that element lies above the diagonal, compose with the automorphism
`rho(f)(y) = 1 - f(1 - y)` of `F`, which takes one-bump elements on `(0,1)` above the
diagonal to one-bump elements below it. The product of these isomorphisms is a group
isomorphism `E_g -> F^k` and induces a ring isomorphism of group rings. So P follows from:

*Claim P':* let `c = (c_1, ..., c_k)` in `F^k` with every `c_i` one-bump on `(0,1)` and
`c_i(y) < y`. Then `(1 + lambda c) K[F^k] ∩ y K[F^k] ≠ 0` for every `lambda` in `K^x`
and every nonzero `y`.

**Step 4 (slopes; Proposition 3 of the one-bump route in every factor).** Let `e(f)` be
the germ exponent at `0` and `m_i = -e(c_i) >= 1`. Put `H = H_(m_1) × ... × H_(m_k)` and
`psi = psi_1 × ... × psi_k : H -> F^k`, the product of the isomorphisms of Lemma 2.
- For `s` in `supp y`, `c_s = s^-1 c s` has components `s_i^-1 c_i s_i`, one-bump on
  `(0,1)` below the diagonal with germ exponent `-m_i`. So `c_s` lies in `H`, and
  `psi(c_s)` has components equal to `y -> y/2` near `0`, still one-bump below the
  diagonal.
- Applying Claim P'' (Step 5) successively over `supp y`, as in Step 2, gives a nonzero
  `v'` in `∩_s (1 + lambda psi(c_s)) K[F^k]`.
- `v = psi^-1(v')` lies in `K[H]` and in every `(1 + lambda c_s) K[F^k]`. Since
  `s (1 + lambda c_s) = (1 + lambda c) s`, `y v` lies in `(1 + lambda c) K[F^k]`, and it
  is nonzero.

**Step 5 (Claim P'': the count in all factors at once).** Let `c = (c_i)` in `F^k` with
every `c_i` one-bump on `(0,1)`, `c_i(y) < y`, and `c_i(y) = y/2` near `0`. Let
`lambda ≠ 0`, `mu = -1/lambda` and `J = (c - mu) K[F^k] = (1 + lambda c) K[F^k]`. For
every nonzero `b` in `K[F^k]` we find `v ≠ 0` with `b v` in `J`; then `b v ≠ 0`.
Fix `n_i >= 1` and dyadic `d_i < 1` with `c_i(y) = 1 - 2^(n_i)(1 - y)` on `[d_i, 1]`,
and put `n = max_i n_i`.
- *5a (coset test).* Step 0 of the one-bump route uses only that the group is
  torsion-free, so it holds in `F^k`: `c^a y' - mu^a y'` lies in `J` for every `y'` and
  every integer `a`. Also `c^a J = J`, since `c^a` commutes with `1 + lambda c`.
- *5b (factor out the germs at `0`).* For `f = (f_i)` put
  `gamma(f) = (c_1^(-e(f_1)), ..., c_k^(-e(f_k)))` and `f' = gamma(f)^-1 f`. Since
  `e(c_i) = -1`, every `f'_i` is the identity near `0`. `gamma(f)` commutes with `c`.
  Let `Gamma = {gamma(f) : f in supp b}`, and choose dyadic `eps > 0` such that every
  `f'_i` is the identity on `[0, eps]`.
- *5c (push toward `1`).* Fix `j >= 1` with `1 - 2^-j >= max_i d_i`, and `K_0 >= 0` with
  `c_i^(-K_0)(eps) >= 1 - 2^-j` for every `i`; this exists because `c_i^-1(y) > y` on
  `(0,1)`. Put `b_2 = c^(-K_0) b c^(K_0)`. Conjugation fixes `gamma(f)` and maps each
  `f'_i` to an element supported in `c_i^(-K_0)((eps, 1)) ⊆ (1 - 2^-j, 1)`. So every
  element of `supp b_2` has the form `gamma h` with `gamma` in `Gamma` and `h` in
  `prod_i F_[1-2^-j,1]`. If `b_2 w` lies in `J`, then `b c^(K_0) w = c^(K_0) b_2 w` lies
  in `c^(K_0) J = J`, so `v = c^(K_0) w` works.
- *5d (positive monoid in every factor).* By Step 3 of Proposition 1, applied in each
  factor to the finitely many `h_i` that occur, there is `s = (s_i)` with `s_i` in
  `F_[1-2^-j,1]` and every `h_i s_i` in `M_j`. Put `b_3 = b_2 s`. Every monomial of `b_3`
  is `gamma m` with `gamma` in `Gamma` and `m = (m_i)` in `prod_i M_j`. Also
  `b_3 K[F^k] = b_2 K[F^k]`, and if `b_3 w'` lies in `J` then `w = s w'` works for `b_2`.
- *5e (shift).* By Step 4 of Proposition 1, `c_i^-1 h c_i = phi^(n_i)(h)` for `h` in
  `F_[d,1]` with `d >= d_i`, and `phi^(n_i)` maps `M_(j')` into `M_(j'+n_i)`. Define
  `Phi(gamma m) = gamma (phi^(n_1)(m_1), ..., phi^(n_k)(m_k))` on monomials and extend
  linearly. Since `gamma` commutes with `c`, `b_3 c^a = c^a Phi^a(b_3)` for all `a >= 0`.
- *5f (dependence gives a solution).* Suppose `r_0, ..., r_N` in `K[prod_i M_1]` are not
  all zero and `sum_a Phi^a(b_3) r_a = 0`. Put `w' = sum_a mu^-a c^a r_a`.
  - `b_3 w' = sum_a mu^-a c^a Phi^a(b_3) r_a`, which is congruent to
    `sum_a Phi^a(b_3) r_a = 0` modulo `J` by 5a.
  - `w' ≠ 0`: if `c^a m = c^(a') m'` with `m, m'` in `prod_i M_1 ⊆ prod_i F_[1/2,1]`, then
    `c_1^(a-a')` is the identity on `[0, 1/2]`, so `a = a'`. The supports of the terms
    `c^a r_a` are therefore disjoint.
- *5g (count).* Let every `m_i` occurring in `b_3` have letters `<= I` and degree
  `<= D`. Given `L`, put `delta = floor(L/2)` and `N = floor((L - I - delta - D)/n)`, and
  let `A_0` be the set of normal forms of degree `delta` with letters in `[1, L]`. The
  unknowns are `r_a` in `K[A_0^k]`, `a = 0, ..., N`: a space of dimension
  `(N + 1) |A_0|^k`.
  - For `a <= N`, a monomial of `Phi^a(b_3)` is `gamma (phi^(n_i a)(m_i))_i`. For
    `x = (x_i)` in `A_0^k`, the insertion bound makes each `phi^(n_i a)(m_i) x_i` a normal
    form of degree between `delta` and `delta + D` with letters in
    `[1, I + nN + delta + D] ⊆ [1, L]`.
  - So every product lies in `Gamma · B^k`, where `B` is the set of normal forms of degree
    between `delta` and `delta + D` with letters in `[1, L]`. As in the twisted-`x_0`
    route, `|B| <= (4^(D+1)/3) |A_0|` once `L + 1 >= 2D`.
  - The image of `(r_a) -> sum_a Phi^a(b_3) r_a` has dimension at most
    `|Gamma| (4^(D+1)/3)^k |A_0|^k`, while `N + 1 >= (L/2 - I - D)/n` grows with `L`. For
    large `L` the map has a nonzero kernel, and 5f applies.

**Remark (why the endpoint stabilizer).** Let `c` in `F` move a point `z`, and let `s` be
in `F`. If `c^a f` and `c^(a') f` both lie in `Stab_F(z) s`, then `c^(a-a')` lies in
`Stab_F(z)`. An increasing homeomorphism of `[0,1]` with a periodic point fixes that point,
so `a = a'`. Every right coset `<c> f` thus meets `Stab_F(z) s` in at most one element, and
by the coset test the only element of `(1 + lambda c) R ∩ K[Stab_F(z)] s` is `0`. In the
nesting argument of `thompson-f-rescaled-x0-binomials-have-common-multiples-proof` (Item 1)
the running multiple must lie in the group ring of the next conjugate's local group. For
multi-bump conjugates with different endpoints the running multiple lies in
`(1 + lambda c') R` for an earlier conjugate `c'` that moves those endpoints, so it cannot.

**Trust surfaces.** Quoted: the items listed at the top, and left-orderability of `F`.
Everything else is proved above.
