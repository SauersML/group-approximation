---
rg: 2
id: jacobson-heisenberg-root-group-uniformly-kills-the-head-proof
kind: route
title: Finite image of a root group in each central isotypic block makes the Heisenberg pairing of finite rank, direct finiteness of J on the finite quotient puts Q in the radical, and De Chiffre--Ozawa--Thom makes it uniform
target: jacobson-heisenberg-root-group-uniformly-kills-the-head
requires:
  - dot-amenable-uniform-hs-stability
---

Notation as on the target.

## Step 1. H(J) is locally finite

The matrix of `x_12(a) x_23(b) x_13(c)` is `[[1,a,ab+c],[0,1,b],[0,0,1]]`, so `(a,b,c)` are coordinates and (HJ1)
presents `H(J)`; the commutator subgroup lies in the centre `x_13(J)`, so `H(J)` is nilpotent of class at most two.
In characteristic two, `(x_12(a)x_23(b)x_13(c))^2 = x_13(ab)` and hence every element has order dividing `4`. A
finitely generated nilpotent torsion group is finite. So `H(J)` is locally finite, and therefore amenable.

## Step 2. Exact finite-dimensional representations kill x_13(I)

Let `rho : H(J) -> U(W)` be unitary with `dim W < infinity`.

*Isotypic blocks.* `rho(x_13(J))` is a commuting family of unitaries with `rho(x_13(c))^2 = 1`. Diagonalize it
simultaneously: `W = (+)_chi W_chi`, a finite sum over additive characters `chi : J -> {+1,-1}` with
`rho(x_13(c))|W_chi = chi(c)`. Each `W_chi` is `H(J)`-invariant because `x_13(J)` is central. Fix `chi` with
`W_chi != 0` and write `rho_chi = rho|W_chi`.

*Finite image.* `a -> rho_chi(x_12(a))` is a homomorphism from `(J,+)` into `U(W_chi)` whose image consists of commuting
involutions. They diagonalize simultaneously with eigenvalues `+-1`, so the image has at most `2^(dim W_chi)` elements.
Its kernel `K` therefore has finite index in `(J,+)`.

*Radical.* By (HJ1), on `W_chi`

```text
rho_chi(x_12(a)) rho_chi(x_23(b)) rho_chi(x_12(a))^(-1) rho_chi(x_23(b))^(-1) = chi(ab).
```

For `a in K` the left side is `1`, so `chi(ab) = 1` for all `b`. Put

```text
R = { a in J : chi(ab) = 1 for all b in J }.
```

Then `K <= R`, so `R` has finite index. `R` is an additive subgroup, and it is a right ideal: if `a in R` and
`c in J`, then `chi((ac)b) = chi(a(cb)) = 1`.

*Direct finiteness on the quotient.* `M = J/R` is a finite-dimensional `F_2`-space with the right `J`-action
`r_x(m) = mx`, and `r_(xy) = r_y r_x`. From `TS = 1` we get `r_S r_T = id_M`. So `r_T` is injective and `r_S` is
surjective, and both are bijective because `dim M < infinity`. Hence `r_T r_S = id_M`, that is `r_(ST) = id_M` and
`r_Q = 0`. Taking `m = u + R` gives `uQ in R` for every `u in J`.

*Conclusion.* For `u, v in J`, `uQ in R` gives `chi(uQv) = 1`. `I` is the additive span of such elements and `chi` is
additive, so `chi(I) = 1`. Therefore `rho_chi(x_13(c)) = 1` for `c in I`, on every block, and so
`rho(x_13(c)) = 1`. Since `Q = 1 Q 1 in I`, `rho(z) = 1`. This proves item 2.

**Remark: characteristic two only enters through `{+-1}`.** The same argument works over any field of characteristic
other than `2`, applied to finite-dimensional representations. In characteristic `2` it fails at *Finite image*,
because commuting unipotent involutions can form an infinite group. That is consistent with the rank-model question
`binary-jacobson-el3-rank-radical-is-the-finitary-kernel` staying open.

## Step 3. The uniform bound

Let `phi : H(J) -> U(n)` be a mean `epsilon`-representation for the normalized 2-norm; a supremum defect below
`epsilon` implies this. `H(J)` is countable, discrete and amenable (Step 1). Apply `dot-amenable-uniform-hs-stability`
(DOT2). This gives a finite-rank projection `P`, a partial isometry `U in P M_infty 1_M` and a genuine
finite-dimensional unitary representation `rho` of `H(J)` on `P l^2`, with

```text
||phi(g) - U^* rho(g) U||_2 < 71 epsilon,     ||1_M - U^*U||_2 < 40 epsilon.
```

For `c in I`, Step 2 gives `rho(x_13(c)) = P`, and `PU = U`, so `U^* rho(x_13(c)) U = U^*U`. Hence

```text
||phi(x_13(c)) - 1||_2 <= ||phi(x_13(c)) - U^*U||_2 + ||U^*U - 1_M||_2 < 71 epsilon + 40 epsilon = 111 epsilon.
```

The trace `tau` on `M_infty` restricts on `1_M M_infty 1_M = M_n` to the normalized trace, so this is (HJ2). If
`delta(phi) = 0`, apply it for every `epsilon > 0`. This proves item 3.

## Step 4. Transport and sharpness

*Item 4.* Apply item 3 to `phi = pi o theta`. Its supremum defect is `delta_theta(pi)`. For the Leavitt case,
`t_2 s_2 = 1` in `L_(F_2)(1,2)`, so `S -> s_2, T -> t_2` is a ring map `J -> L_(F_2)(1,2)` and sends `Q` to
`1 - s_2t_2 = s_1t_1`. The Steinberg relations of `St_20` include (HJ1) for the root triple `(1,2,3)`: the pairs
`(12,13)` and `(23,13)` commute. So the ring map induces `theta : H(J) -> St_20(L_(F_2)(1,2))`, using the normal form
from Step 1.

*Item 5.* By Step 1, `G_F = <F,z>` is finite. Its left regular representation `lambda` has
`tr lambda(z) = 0` since `z != 1`. So `||lambda(z) - 1||_2^2 = 2 - 2 Re tr lambda(z) = 2`. The extension by `1`
is multiplicative on `G_F x G_F`.

HS-stability of a countable group in the finite-set sense asks the following: for every finite `F_0` and every
`eta > 0` there are a finite `F` and a `d > 0` such that every map with defect `< d` on `F x F` is `eta`-close on
`F_0` to a genuine finite-dimensional representation. Take `F_0 = {z}` and `eta < sqrt 2`. The regular-window map
of any `F` has defect `0` on `F x F`, but every genuine representation `rho'` has `rho'(z) = 1` by item 2, at
distance `sqrt 2`. So `H(J)` is not HS-stable.

## Step 5. Consequence (HJ3)

If `pi_k` are approximations of `EL_20(J)` with `||pi_k(z) - 1||_2 -> r > 0`, item 4 applied to
`theta_g = Ad(g) o (root triple)` gives `delta_(theta_g)(pi_k) >= ||pi_k(g z g^-1) - 1||_2 / 111`. Moreover
`||pi_k(g z g^-1) - pi_k(g) pi_k(z) pi_k(g)^* ||_2 -> 0` by local defect, so the right side tends to `r/111`.

**Why this does not contradict hyperlinearity by itself.** The ultraproduct of `pi_k` is an exact representation of
`H(J)` in the corner of a II_1 factor `R^omega`. That corner is not finite-rank, and the II_1 case of DOT2 produces no
finite-rank `P`. The whole content is the gap between `lim_k sup_(H(J))` and `sup_(H(J)) lim_k`.
