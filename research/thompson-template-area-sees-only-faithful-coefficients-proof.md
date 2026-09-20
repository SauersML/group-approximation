---
rg: 2
id: thompson-template-area-sees-only-faithful-coefficients-proof
kind: route
title: Split the edge commutator as a conjugated fixed torus times the h-commutator of the conjugacy loop, then push to the relation module
target: thompson-template-area-sees-only-faithful-coefficients
requires: []
---

**Step 1 (free identity).**  Write `s = s_e`, `sigma = sigma_s`,
`lambda = lambda_e`.  Then `lambda sigma` is freely equal to `k c k^(-1)`,
and in the free group

```text
lambda [sigma,h] lambda^(-1) . [lambda,h]
  = lambda sigma h sigma^(-1) h^(-1) lambda^(-1) . lambda h lambda^(-1) h^(-1)
  = (lambda sigma) h (lambda sigma)^(-1) h^(-1)  =  w_e .
```

Since `s` commutes with `h` in `Gamma`, `[sigma,h] in N`, and so
`[lambda,h] in N`.  Area is conjugation-invariant and subadditive, and
`Area(u^(-1)) = Area(u)`.  So `Area(w_e) <= C_0 + Area([lambda,h])`.
Also `[lambda,h] = lambda [sigma,h]^(-1) lambda^(-1) w_e`, which gives
`Area([lambda,h]) <= C_0 + Area(w_e)`.  This proves the first display of
item 1.

**Step 2 (relation-module class).**  For `n, n' in N` and `g in F(X)`,

```text
cl(n n') = cl(n) + cl(n'),
cl(g n g^(-1)) = gbar . cl(n).
```

The image `lambdabar` of `lambda` in `Gamma` is 1, so
`cl(lambda [sigma,h] lambda^(-1)) = cl([sigma,h])`.  Writing
`[lambda,h] = lambda . (h lambda^(-1) h^(-1))` gives

```text
cl([lambda,h]) = cl(lambda) - h . cl(lambda).
```

Adding the two gives the second display of item 1.

**Step 3 (ultrapower form).**  Suppose `Area(u_n) <= A` for `omega`-almost
every `n`.  Each `u_n` is freely a product of at most `A` conjugates
`g_(n,i) r_(n,i)^(+-1) g_(n,i)^(-1)`.  There are only finitely many patterns
`(r_(n,i), sign)_(i<=l)` of length `l <= A`, so one pattern holds
`omega`-almost surely.  The sequences `(g_(n,i))_n` are then
elements of `F(X)^omega`, and `[u_n]_omega` lies in the normal closure of
the diagonal relators.

Conversely, a product of `A` conjugates of diagonal relators in
`F(X)^omega` is represented coordinatewise by products of `A` conjugates,
`omega`-almost surely.

Hence `[u_n]_omega = 1` in `P_omega` exactly when `Area(u_n)` is
`omega`-bounded.  Apply this to `[lambda_(e_n), h]`, and use Step 1 and the
fact that `sup_e = infinity` exactly when some sequence of arcs `e_n` has
area tending to infinity.  This gives the ultrapower clause of item 1.  The
class `Lambda` maps to 1 in `Gamma^omega`, because each `lambda_e` lies in
`N`.

**Step 4 (LC and blindness).**  Take a van Kampen diagram of area `A` for `w`.
Then `w` is freely `prod_(i<=A) g_i r_i^(+-1) g_i^(-1)`, so

```text
cl(w) = sum_i +- gbar_i cl(r_i).
```

The seminorm is `Gamma`-invariant, which gives (LC).  If `h` acts trivially
on `M`, then `phi((1-h) cl(lambda_e)) = (1-h) phi(cl lambda_e) = 0`.  By
Step 2, `phi(cl w_e) = phi(cl [sigma_s, h])`, and this takes at most `|S|`
values.  That proves item 2.

**Step 5 (coefficients in F and T-bar).**  Let `M` be a module and let
`K_M` be the kernel of the action, a normal subgroup.

- **For `F`.**  Every nontrivial normal subgroup of `F` contains `F'`
  (Cannon–Floyd–Parry, Theorem 4.3).  So if `K_M != 1` then `h in F' <= K_M`.
- **For `T-bar`.**  Suppose `K_M` is not contained in `<z>`.  Its image in
  the simple group `T` is nontrivial and normal, so it is all of `T`, and
  `T-bar = K_M <z>`.  Since `z` is central,
  `[T-bar, T-bar] = [K_M, K_M] <= K_M`.
  - The lifted copy of `F` fixes `Z`, so it meets `<z>` trivially and is
    isomorphic to `F`.
  - `F'` is simple and nonabelian, so it is perfect.
  - Hence the lifted `h in F' = [F',F'] <= [T-bar,T-bar] <= K_M`.

**Step 6 (finite-dimensional coefficients).**  A finite-dimensional linear
image of a finitely generated group is residually finite (Mal'cev).

- For `F`, a kernel that contains `F'` gives an abelian image.  A trivial
  kernel would make `F` itself residually finite, but `F'` is infinite and
  simple, so it is not.
- For `T-bar`, a non-central kernel contains `[T-bar,T-bar]` and the image
  is abelian.  A kernel `<z^n>` would leave the embedded `F'` inside a
  residually finite group, which is impossible.
- In the abelian cases `h`, a commutator, acts trivially.  The same holds
  for any module pulled back from such an image, for example a finite-rank
  induced local system.

So all of these certificates are constant on the template, by Step 4.  This
covers every example listed under (LC) in the claim except homological area
and other faithful modules.

**Step 7 (the Sh_3 template).**  On every arc, `k c k^(-1) = c_{sI}`, so
`S = {c_{sI}}`.  The word `h = c_{sK}` is an affine copy of `x_0` inside the
interior interval `(1/4, 1/2)`.  It is compactly supported in `(0,1)`, hence
lies in `F'`.  Its lift lies in the lifted `F'`.  Steps 4–6 apply.
