---
rg: 2
id: kms-hc1-p-power-value-vanishes-on-affine-root-groups
kind: claim
title: At the first deviation of Gamma^A2_p -> I_1 the p-power value Pi is additive on commuting pairs, so torus conjugation kills it on every real affine root group of I_1 at every level; Pi(x21(t^n)) = 0 for all n >= 1 holds whatever V_n is, so the Pi form of Route 2 cannot reach C_nA, C_nB or K_n
distinct_from:
  kms-hc1-virtual-vertex-route-is-conjugation-inert: that claim proves Pi is a class function vanishing on I_1-conjugates of vertex elements, and that the T5 bridge is circular. It leaves open whether Pi vanishes on x21(t^n) for n >= 2, which is not I_1-conjugate to any vertex element. This claim proves that it does, for every n and every p >= 5, by additivity, and shows the answer carries no information on W_n.
  kms-hc1-root-p-powers-die-first-deviation-at-3np: that claim kills the leading-form p-powers of real-root vectors in degree p.deg. This claim kills the full group-level p-power class of every root element in the deviation degree 3np.
artifacts:
  - experiments/kms-hc1-root-group-p-power-2026-09-19/root_conj.py
  - experiments/kms-hc1-root-group-p-power-2026-09-19/root_conj_p5.out
  - experiments/kms-hc1-root-group-p-power-2026-09-19/root_conj_p7.out
  - experiments/kms-hc1-root-group-p-power-2026-09-19/root_conj_p11.out
---

Notation of `kms-hc1-virtual-vertex-route-is-conjugation-inert` (below: the
inertness claim). Fix a prime `p >= 5`, write `G = Gamma^` for the pro-p
completion of `Gamma^A2_p` and `K = ker(phi^ : G -> I_1)`. Let `d0` be the
first Zassenhaus deviation degree, assumed finite, and `Kd0` the kernel of
`gr_(d0) G -> (L_p)_(d0)`. For `y` in `I_1` with `y^p = 1`, `Pi(y)` is the
class of `yt^p` in `gr_(d0) G`, for any lift `yt`. By (FD) of
`kms-hc1-root-p-powers-die-first-deviation-at-3np` (given Open 1),
`d0 = 3np` and `Kd0 = W_n / V_n` with `W_n = span(K_n, C_nA, C_nB)`.

The six real root groups of `I_1` are `X_ij(O)` for `i<j` and `X_ij(tO)`
for `i>j`, with `O = F_p[[t]]` and `X_ij(f) = 1 + f E_ij`.

## Statement

> **(A) Additivity.** If `y, z` in `I_1` commute and `y^p = z^p = 1`, then
> `Pi(yz) = Pi(y) + Pi(z)`. So `Pi(y^k) = k Pi(y)`, and `Pi` restricted to
> any abelian subgroup of exponent `p` of `I_1` is a homomorphism to `Kd0`.

> **(V) Root groups.** `Pi` vanishes on every element of each of the six
> real root groups of `I_1`, at every level. The same holds on every product
> of pairwise commuting root elements, for example on `X_13(O) X_23(O)`,
> `X_12(O) X_13(O)`, `X_21(tO) X_31(tO)`, `X_31(tO) X_32(tO)`,
> `X_21(tO) X_23(O)`, `X_32(tO) X_12(O)`, and on every `I_1`-conjugate of
> such an element. In particular `Pi(x21(t^n)) = 0` for every `n >= 1`.

> **(N) This is new information beyond vertex conjugates.** For `n >= 2`
> the element `x21(t^n)` is not `I_1`-conjugate to any element of
> `phi(U_ab)`, `phi(U_bc)` or `phi(U_ca)`, and neither are `x13(t)`,
> `x12(t)`, `x23(t)`. So (P) of the inertness claim does not apply to them.
> The content ideal of `y - 1` is an `I_1`-conjugacy invariant; it is `(1)`
> or `(t)` on vertex elements and `(t^n)` on `x21(t^n)`.

> **(O) Obstruction to the Pi form of Route 2.** The proof of (V) uses only
> (Z1), (Z2) and (P) of the inertness claim and the torus of `I_1`. It holds
> for every value of `V_n` inside `W_n`. So `Pi(x21(t^n)) = 0`, and
> `Pi = 0` on every root-type element, can decide none of
> `C_nA, C_nB, K_n in V_n`. In particular the question "does `Pi` vanish on
> `x21(t^2)`?" has the answer yes for every `p >= 5`, and it does not settle
> `C_2A`. A Cartan relation can reach `W_n` only through elements of
> infinite order, such as the torus elements `h(1 + t^n)`, whose p-power
> relation `h(1+t^n)^p = h(1+t^(np))` is not a torsion relation.

## Proof idea

- **(A).** `[yt, zt]` lies in `K`, which lies in `D_(d0)`. Modulo
  `D_(d0+1)` this is central, so `<yt, zt>` has class 2 there, and
  `(yt zt)^p = yt^p zt^p [zt, yt]^(p(p-1)/2)`. The last factor is a p-th
  power of an element of `D_(d0)`, so it lies in `D_(p d0)`, which is in
  `D_(d0+1)`.
- **(V).** Let the root be `(i,j)`, with lowest exponent `v0 = 0` if
  `i < j` and `v0 = 1` if `i > j`. The vertex groups contain `x_ij(lam t^v0)`
  for every `lam` in `F_p`: these are `a, b, c` and the centres
  `[a,b] = x13(1)`, `[b,c] = x21(t)`, `[c,a] = x32(t)` (`root_conj.py`).
  The diagonal matrices of `I_1` realize every ratio `d_i/d_j` in `1 + tO`,
  since `p` is odd and square roots exist in `1 + tO`. Write
  `f = t^v0 g`.
  - If `g(0) = lam != 0`, then `x_ij(f) = Ad(d) x_ij(lam t^v0)` with
    `d_i/d_j = g/lam`. This is a vertex conjugate, so `Pi = 0` by (P).
  - If `g(0) = 0`, then `x_ij(f) = x_ij(t^v0 (1+g)) x_ij(-t^v0)`. This is a
    product of two commuting vertex conjugates, so `Pi = 0` by (A).

  Commuting products follow from (A), and conjugates follow from (P).
- **(N).** If `h` is in `GL_3(O)`, then `h(y-1)h^-1` generates the same
  entry ideal. For the `(t)` cases, the leading term `(y-1)/t mod t`
  changes by `Ad` of an element of `B^+(F_p)`. Its orbit on the content-`(t)`
  vertex elements never contains `E13`, `E12` or `E23`, by a rank-one
  image/kernel argument, checked exhaustively in `root_conj.py`.
- **(O).** The proof of (V) never evaluates an element of `W_n`.

## Status

- **Proved, every p >= 5, every level n:** (A), (V), (N), (O). Full proof in
  `kms-hc1-p-power-value-vanishes-on-affine-root-groups-proof`. (A) and (V)
  need only that `d0` is finite, and (FD) is used only to name
  `Kd0 = W_n/V_n`.
- **Checked** (`root_conj.py p 12`, `p = 5, 7, 11`, `ALL OK`):
  - the vertex centres are root elements;
  - 240 random decompositions from (V);
  - the `B^+(F_p)`-orbit computation of (N);
  - the `SL_2` Bruhat identity used in the next step.

## Next step

Route 2 has to use a relator of infinite-order elements. The first
candidate is the Cartan relator of the `12` block. By the Bruhat identity
`x12(u) x21(s) = x21(s/(1+us)) h(1+us) x12(u/(1+us))`, the torus element
`h(1+t^n)` is a word in four root elements. Its relation
`h(1+t^n)^p = h(1+t^(np))` becomes a word relator `R_n` in root elements.
With lifts of the root elements, `R_n` has a class at `3np` equal to
`C_nA` plus the defects of the chosen root lifts. Lifts by `I_1`-conjugation
of vertex elements are canonical modulo `D_(d0+1)` only up to the
centralizer pairing `delta_v(c) = [ct, v] mod D_(d0+1)`, for `c` in
`C_(I_1)(phi v)`. This pairing is a homomorphism in `c` that vanishes on
p-th powers. The falsifiable step is to decide whether `delta_a` vanishes
on the torus `diag(u, u, u^-2)`, `u` in `1 + t^n O`, which centralizes
`a = x12(1)`, and to express the class of `R_n` through these pairings.
