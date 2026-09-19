---
rg: 2
id: jacobson-mirror-kernel-no-conjugation-mean-proof
kind: route
title: Push the kernel mean to the Kazhdan mirror half, let the finite-orbit theorem put it on the FC-centre, and translate it off itself by one kernel element
target: jacobson-mirror-kernel-has-no-conjugation-invariant-mean
requires:
  - kazhdan-groups-mean-free-amenable-iff-residually-finite
  - elementary-groups-over-fg-rings-have-property-t
  - jacobson-toeplitz-extension-is-a-mirror-quotient-of-a-lef-group
  - coherent-kernel-folner-windows-force-conjugation-invariant-mean
  - affine-semidirect-sl3-source-has-property-t
---

Notation as in the target. Imported facts:
- **(F1)** Item 1 of `kazhdan-groups-mean-free-amenable-iff-residually-finite`. If a countable group `W` with a
  Kazhdan pair acts on a set `Omega`, every `W`-invariant mean on `Omega` gives mass `1` to the union `Omega_fin`
  of the finite orbits. A group with property (T) is finitely generated, so countable, and has a Kazhdan pair.
- **(F2)** `elementary-groups-over-fg-rings-have-property-t`. `EL_n(R)` has (T) for `R` a finitely generated ring
  with `1` and `n >= 3`.
- **(F3)** (MQ1)–(MQ3) of `jacobson-toeplitz-extension-is-a-mirror-quotient-of-a-lef-group`.
- **(F4)** Items 1 and 2 of `coherent-kernel-folner-windows-force-conjugation-invariant-mean`.

Everything else is elementary and proved here.

## Step 0. The FC-centre is a subgroup

If `x` and `y` have finite conjugacy classes, their centralizers have finite index. So `C(x) ∩ C(y)` has finite
index, and it centralizes `x y^-1`. So `x y^-1` has a finite class. Also `1 in FC(W)`. So `FC(W)` is a subgroup, and
for `w_0 notin FC(W)` the coset `w_0 FC(W)` is disjoint from `FC(W)`.

## Step 1. Theorem A

Let `m` be a mean on `G` with `m(gAg^-1) = m(A)` for all `g`, and `m(k_0 A) = m(A)`. Put `m'(D) = m(phi^-1 D)` for
`D ⊆ W`. This is a mean on `W`.
- **Conjugation.** `phi^-1(phi(g) D phi(g)^-1) = g phi^-1(D) g^-1`, so `m'` is invariant under conjugation by
  `phi(G) = W`.
- **Translation.** `phi^-1(w_0 D) = k_0 phi^-1(D)` with `w_0 = phi(k_0)`, so `m'(w_0 D) = m'(D)`.

Apply (F1) to `W` acting on `Omega = W` by conjugation. Then `Omega_fin = FC(W)`, so `m'(FC(W)) = 1`. By
translation, `m'(w_0 FC(W)) = 1`. By Step 0 the two sets are disjoint, so `m'(W) >= 2`. This is a contradiction.

## Step 2. Theorem B

**Coefficients.** `L^2(M) = l^2(G) ⊗ L^2(B)`. So each `x in L^2(M)` is `x = sum_h delta_h ⊗ x_h` with
`sum_h ||x_h||_2^2 = ||x||_2^2`.
- On elementary tensors, `U_g (delta_h ⊗ xi) U_g^* = delta_(g h g^-1) ⊗ v_g xi v_g^*` and
  `U_k (delta_h ⊗ xi) = delta_(kh) ⊗ v_k xi`.
- Left and right multiplication by unitaries of `M` are isometries of `L^2(M)`. So by continuity,
  `(U_g x U_g^*)_(h') = v_g x_(g^-1 h' g) v_g^*` and `(U_k x)_(h') = v_k x_(k^-1 h')`.
- `||v xi v^*||_2 = ||xi||_2` for `v in U(B)`.

**Densities.** For `x != 0` put `f_x(h) = ||x_h||_2^2 / ||x||_2^2`, a probability measure on `G`. By the
formulas, `f_(U_g x U_g^*)(g A g^-1) = f_x(A)` and `f_(U_k x)(k A) = f_x(A)` for every `A ⊆ G`.

**Estimate.** If `||y||_2 = ||x||_2`, then

```text
sum_h | ||y_h||^2 - ||x_h||^2 | <= sum_h ||y_h - x_h|| (||y_h|| + ||x_h||) <= ||y - x||_2 (||y||_2 + ||x||_2)
```

by Cauchy–Schwarz. So `||f_y - f_x||_1 <= 2 ||y - x||_2 / ||x||_2`. Both `U_g x U_g^*` and `U_(k_0) x` have the norm
of `x`.

**Contradiction.** Suppose no pair `(F, epsilon)` works. Enumerate `G = {g_1, g_2, ...}` and take
`F_i = {g_1, ..., g_i}` and `epsilon_i = 1/i`. There are then `(B_i, v_i)` and `x_i != 0` violating the conclusion.
The densities `f_i = f_(x_i)` live on `G` alone, whatever `B_i` is. For `g in F_i` and `A ⊆ G`,

```text
|f_i(g A g^-1) - f_i(A)| = |f_i(g A g^-1) - f_(U_g x_i U_g^*)(g A g^-1)| <= 2/i,
```

and likewise `|f_i(k_0 A) - f_i(A)| <= 2/i`. Let `m` be a weak-star cluster point of the `f_i` in `(l^inf G)^*`. It
is a mean, invariant under conjugation by every `g` (since `g in F_i` eventually) and under left translation by
`k_0`. This contradicts Theorem A. A nonzero projection `p in M` is a nonzero vector of `L^2(M)`.

## Step 3. Compressions (item 4 of Theorem C)

For a projection `p` and a unitary `u` in a tracial `(M, tau)`:
- **(i)** `||u p u^* - p||_2^2 = 2 tau(p) - 2 tau(p u p u^*) = 2 ||(1-p) u p||_2^2`, since
  `tau(p u p u^*) = ||p u p||_2^2` and `tau(p) = ||u p||_2^2 = ||p u p||_2^2 + ||(1-p) u p||_2^2`.
- **(ii)** `||u p - p||_2^2 = ||p u p - p||_2^2 + ||(1-p) u p||_2^2`.

Write `||y||_(2,p) = ||y||_2 / tau(p)^(1/2)`. Put `c(g) = p U_g p`. Then `p - c(g) c(g^-1) = y^* y` with
`y = (1-p) U_g^* p`. Also `tau(y^* y) = tau(p y^* y) <= ||p||_2 ||y^* y||_2`, so
`||y||_(2,p)^2 <= ||y^* y||_(2,p)`.

Suppose the compressions are approximately multiplicative on every finite set in the renormalized norm. Then
`||(1-p_i) U_g^* p_i||_(2,p_i) -> 0` for every `g`. Replacing `g` by `g^-1` and using (i),
`||U_g p_i U_g^* - p_i||_(2,p_i) -> 0` for every `g`.

Suppose also that `||c_i(k_0) - p_i||_(2,p_i) -> 0`. With (ii) and the previous line for `g = k_0`, this gives
`||U_(k_0) p_i - p_i||_(2,p_i) -> 0`. For large `i`, `x = p_i` violates Theorem B with its uniform `(F, epsilon)`.

## Step 4. Verifying the Jacobson hypotheses (Theorem C)

- **Property (T).** By (MQ1), `E_- = GL_n(J) = EL_n(J)` as an abstract group; the mirror action only relabels the
  basis. `J` is generated as a ring by `S, T`, and `n >= 3`. By (F2), `E_-` has (T), and likewise `E_+`.
- **Surjectivity.** Let `h in E_-`. By (MQ1), `pi_-(h) in SL_n(A) = pi_+(E_+)`. So some `g` has
  `pi_+(g) = pi_-(h)`, and then `(g,h) in P`. So `pr_-` is onto.
- **The kernel lies in `P`.** `1 x L_- = ker(pr_+) ⊆ P` (MQ3). So `L_- ⊆ E_-`, and `pr_-(1,t) = t`.
- **Infinite classes.** Let `1 != t in L_-`, and let `U_t = im(t - 1)`, a subspace of dimension `d >= 1`.
  - For `s in L_-`, `im(s t s^-1 - 1) = s U_t`.
  - Any two `d`-dimensional subspaces of `V_-^n` lie in a common finite coordinate subspace `U_N`, and `GL(U_N)`
    (extended by the identity) lies in `L_-` and is transitive on its `d`-dimensional subspaces.
  - `V_-^n` has infinitely many `d`-dimensional subspaces. So the `L_-`-class of `t`, and hence its `E_-`-class,
    is infinite. So `t notin FC(E_-)`.
  The same argument in `V_+^n` gives `1 != t in L ⊆ E_+` with infinite class.

**Item 1.** A mean `mu` on `L_-` that is invariant under left `L_-`-translation and `P`-conjugation pushes forward
along the inclusion `1 x L_- -> P` to a mean on `P`. Normality of `1 x L_-` makes that mean `P`-conjugation
invariant, and it is `(1,t)`-translation invariant. Theorem A forbids it. The fibre-square form is item 2 of (F4),
applied to `W := P`, `N := 1 x L_-` and `Q = P/N = EL_n(J)`.

**Item 2.** Apply Theorem A to `G = W = E_+ = EL_n(J)`, `phi = id` and `k_0 = t in L`, and push forward as in
item 1.

**Item 3.** This is the contrapositive of item 1 of (F4), with items 1 and 2.

**Item 4.** This is Step 3, with `G = P` and `k_0 = (1,t)`.

**Calibration.** `Z^3 x| SL_3(Z)` has (T) (`affine-semidirect-sl3-source-has-property-t`), and the class of
`(e_1, 1)` contains `(v, 1)` for every primitive `v`, so it is infinite. Theorem A applies with `G = W` and
`phi = id`, so (CIM) fails for `(G, Z^3)`. The quotient `SL_3(Z)` is residually finite (Malcev). So the target kills
a method and not a conclusion. It is not a nonsoficity certificate.

**COMPLETE.**
