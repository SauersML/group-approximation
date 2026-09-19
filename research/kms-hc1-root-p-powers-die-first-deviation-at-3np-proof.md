---
rg: 2
id: kms-hc1-root-p-powers-die-first-deviation-at-3np-proof
kind: route
title: Torus commutators turn each vertex element of order p into a lift of any higher root vector that commutes with it modulo D_pd, and Hall-Petrescu then kills its p-power; with Lie generation in degree 1 and Open 1, only K_n and the two Cartan p-power defects survive at a first deviation, which must be in a degree 3np
target: kms-hc1-root-p-powers-die-first-deviation-at-3np
requires: [kms-hc1-iwahori-h2-serre-plus-kassel-all-degrees, kms-hc1-level-m-edge-tails-have-order-at-most-two, kms-hc1-witt-carry-syzygy-lifts-by-right-freeness]
artifacts:
  - experiments/kms-hc1-root-p-powers-2026-09-18/torus_comm.py
  - experiments/kms-hc1-root-p-powers-2026-09-18/torus_comm_p5.out
---

Notation of the claim. Write `[x,y] = x^-1 y^-1 x y` and `x^s = s^-1 x s`.

## 1. Vertex elements (input of RP)

The six vertex elements, their images and their `x^p` all come from one
dictionary. Here `beta = e_i - e_j` and `k0` is the t-valuation of the
image.

| vertex x | image phi(x)  | beta    | k0 |
|----------|---------------|---------|----|
| `a`      | `x12(1)`      | `e1-e2` | 0  |
| `b`      | `x23(1)`      | `e2-e3` | 0  |
| `c`      | `x31(t)`      | `e3-e1` | 1  |
| `[a,b]`  | `x13(±1)`     | `e1-e3` | 0  |
| `[b,c]`  | `x21(±t)`     | `e2-e1` | 1  |
| `[c,a]`  | `x32(±t)`     | `e3-e2` | 1  |

- **Coverage.** The positive affine real roots are the pairs `(beta, k)`
  with `k >= k0(beta)`: `k >= 0` for `i < j` and `k >= 1` for `i > j`.
  Each one is `(beta, k0 + m)` for exactly one vertex and one `m >= 0`.
- **Order p.** Every vertex element lies in a Heisenberg vertex group of
  order `p^3`. For odd `p` that group has exponent `p`, so `x^p = 1` in
  `Gamma`.

## 2. Proof of (RP)

Let `y` in `gr_d Gamma^` map to a unit times `t^k E_beta`. Pick the vertex
`x` with `phi(x) = x_beta(u t^(k0))` and put `m = k - k0`.

**Case m = 0.** Then `x` is itself a lift of a unit multiple of `y`, and
`x^p = 1`. So `y^[p] = 0`.

**Case m >= 1.** Build a lift `g` of `y` as follows.

- **The torus element.** `s = diag(...)` has `1+t^m` in slot `i`,
  `(1+t^m)^-1` in slot `j` and 1 elsewhere. It lies in `I_1`. Choose a
  preimage `sigma` of `s` in `Gamma^`.
- **The lift.** Put `g = [x, sigma]`. Then
  `phi(g) = x_beta(u t^(k0))^-1 x_beta(beta(s)^-1 u t^(k0))`, where
  `beta(s) = (1+t^m)^2`.
- **Its image.** So `phi(g) = x_beta(((1+t^m)^-2 - 1) u t^(k0)) = x_beta(-2u t^k + O(t^(k+1)))`.
  The leading coefficient `-2u` is a unit because `p` is odd.
- **Its class.** By hypothesis `ker phi^` is contained in `D_(pd)`, which is
  contained in `D_d`. Since `phi(g)` lies in `D_d(I_1)`, `g` lies in
  `D_d Gamma^`. Its class is a unit multiple of `y`, because the root space
  of `(L_p)_d` at `(beta, k)` is a line and `gr_d` is an isomorphism.

**The two facts that drive Hall-Petrescu.**

- `phi([g, x]) = 1`, because `x_beta` is abelian. So `[g, x]` lies in
  `ker phi^`, which is contained in `D_(pd)`.
- `x g = x x^-1 sigma^-1 x sigma = x^sigma`. So `(x g)^p = (x^p)^sigma = 1`.

**Hall-Petrescu.** Let `H = <x, g>`. Then

    x^p g^p = (x g)^p c_2^C(p,2) ... c_(p-1)^C(p,p-1) c_p,   with c_i in gamma_i(H).

- `gamma_2(H)` is the normal closure in `H` of `[g, x]`, so it is contained
  in `D_(pd)`.
- For `2 <= i <= p-1`, `p` divides `C(p,i)`. So `c_i^C(p,i)` lies in
  `D_(pd)^p`, which is contained in `D_(p^2 d)`.
- `c_p` lies in `gamma_3(H) = [gamma_2 H, H]`, which is contained in
  `[D_(pd), D_1]` and so in `D_(pd+1)`.
- Since `x^p = 1` and `(x g)^p = 1`, this gives `g^p` in `D_(pd+1)`.

So the p-power of the class of `g` is zero in `gr_(pd)`. As `y` is a unit
times that class, and `[p]` is p-homogeneous, `y^[p] = 0`. ∎

`torus_comm.py` checks the matrix facts of this section for `p = 5, 7, 11`
in degrees up to 20: the value `-2u` (it prints `3` at `p = 5`),
`[g, x] = 1`, `x g = x^s`, and the coverage.

## 3. Proof of (FD)

Suppose `d0 < infinity`. Then `Gamma^/D_(d0) = I_1/D_(d0)`, so
`gr_(<d0) Gamma^ = (L_p)_(<d0)` as restricted Lie algebras.

**(a) gr_(d0) is a quotient of U_(d0).** `gr Gamma^` is generated in degree
1 as a restricted Lie algebra. Every relation of `L_p` of degree `< d0`
holds in it. So `gr_(<=d0) Gamma^` is a quotient of `U_(<=d0)`, compatibly
with the map `U -> L_p`.
- The relations of `L_p` are multihomogeneous, and `[p]` multiplies the
  multidegree by `p`. So `U` is multigraded. The kernel of `U_(d0) -> (L_p)_(d0)`
  is a multigraded subspace.

**(b) The Lie part.** Let `G` be the Lie subalgebra of `U` generated in
degree 1. `L_p` is Lie-generated in degree 1, as the positive part of
affine `sl_3` with generators `e_0, e_1, e_2`. So `G_(d0)` maps onto
`(L_p)_(d0)`.
- `G_(d0)` is a quotient of `(FreeLie_3 / <R_(<d0)>)_(d0)`, where `R` is the
  relation ideal of `L_p`.
- In the minimal presentation, the kernel of `(FreeLie_3/<R_(<d0)>)_(d0) -> (L_p)_(d0)`
  is `H_2(L_p)_(d0)`, the relations first needed in degree `d0`.
- By Open 1 this is zero unless `d0 = 3` or `d0 = 3np`. In the case
  `d0 = 3np` it is the line `K_n`, of multidegree `(np, np, np)`.
- `d0 = 3` is excluded: the vertex relators `[[x,y],x] = 1` give the 6 Serre
  relations in `gr_3 Gamma^`.

**(c) The restricted part.** `U_(d0)` is `G_(d0)` plus the span of the
`z^[p]` with `z` in `U_(d0/p)` (and `z` itself may be a p-power). Modulo
`G_(d0)` the map `z -> z^[p]` is additive and p-semilinear. So it is enough
to take `z` in a basis of `U_(d0/p) = (L_p)_(d0/p)`. That basis consists of:
- **root vectors** `t^k E_beta`. Their p-powers have real multidegree `p mu`
  with `mu` not a multiple of `(1,1,1)`. They map to 0 in `L_p` and, by (RP)
  with `d = d0/p`, also map to 0 in `gr_(d0) Gamma^`.
- **Cartan vectors** `h_A t^(n)` and `h_B t^(n)`, which occur only when
  `d0/p = 3n`. Their p-powers minus the Lie lifts of `h t^(np)` are
  `C_nA` and `C_nB`, of multidegree `(np, np, np)`.

**(d) Conclusion.**
- `ker(U_(d0) -> L)` is spanned by `K_n` (if `d0 = 3np`), by `C_nA` and
  `C_nB` (if `3p` divides `d0`), and by the real p-power lines.
- The real lines die in `gr Gamma^`. So `ker(gr_(d0) Gamma^ -> L)` is the
  image of `W_n`.
- A deviation needs a nonzero kernel. If `d0` is not of the form `3np`,
  `W` is absent and the kernel is 0, which contradicts minimality. So
  `d0 = 3np`, and the kernel has dimension at most 3 in multidegree
  `(np, np, np)`. ∎

## 4. (Crit), (Z), (P), (M)

**(Crit).**
- Both `D_n` filtrations are separated. The one on `Gamma^` is a basis of
  open normal subgroups of a finitely generated pro-p group.
- So if `gr phi^` is injective in every degree, then `phi^` is injective,
  and it is surjective by construction.
- Conversely, a deviation at `3np` means a nontrivial kernel.
- By (FD), the level-`n` test is exactly the vanishing of the images of the
  three spanning elements. Those images vanish iff the level-`n` relation
  classes fill `W_n`, which is `V_n = W_n`.

**(Z).**
- **The transfer.** Suppose `Gamma^/P_(c+1) = I_1/P_(c+1)`. Then `ker phi^`
  is contained in `P_(c+1) Gamma^`, which is contained in `D_(c+1) Gamma^`.
  Since `phi(D_(c+1) Gamma^) = D_(c+1) I_1`, the quotients modulo `D_(c+1)`
  agree.
- **Levels at p = 5.** Class 59 covers `3np` for `n = 1, 2, 3`
  (15, 30, 45).
- **Levels at p = 7.** Class 62 covers `n = 1, 2` (21, 42).
- **Levels at p = 11.** Class 65 covers `n = 1` (33).

**(P).**
- `rho_n` is the evaluation of level `n` in `u(N)`, truncated at `3np`.
  It factors through `A / (gr I)_(<3np) A`, as the w12 claim records.
- A product `u T v` with `T` in gr I of degree `3p` has `rho_n(u T v) = rho(u) rho_n(T) rho(v)`.
- Here `rho_n(T) = 0`, because `T` is a level-1 relation class, and level 1
  holds by the lift claim.
- So such products give 0 in `W_2`, and the step "products of level-1 gr I
  elements with `(p,p,p)` words" cannot span `W_2`.

**(M).**
- An S-pair jump `J` of total degree `3np` is a sum of multihomogeneous
  components `J_mu`.
- For `mu` not equal to `(np, np, np)`, the image of `J_mu` in
  `U_(3np) / (lower relations)` lies in the kernel part of multidegree `mu`,
  and by (FD) that part is 0 in `gr Gamma^`.
- So only the `(np, np, np)` component of a jump is visible, which is how
  the w12 claim evaluates it.
