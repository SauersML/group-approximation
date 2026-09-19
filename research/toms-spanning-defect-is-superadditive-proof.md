---
rg: 2
id: toms-spanning-defect-is-superadditive-proof
kind: route
title: Products of usc level functions have product level components, so the spanning defect adds; Fekete gives a rate, one counterexample amplifies to linear defect, and the component budget turns the rate into depth
target: toms-spanning-defect-is-superadditive
requires: [toms-level-two-spanning-reduces-to-relative-hex, toms-slice-constant-targets-reduce-to-level-spanning, toms-two-level-spanning-holds-in-every-dimension]
---

Notation is that of the claim. For a usc `delta` write `d(delta) = min_Omega (f(Omega) - delta(Omega))`,
so `D(M) = max_delta d(delta)`. The minimum exists because `f - delta` takes integer values in
`[-max delta, M]`, and `max delta` is finite (a usc integer function on a compactum is bounded).

## Part 1: range

- *Lower bound.* `delta = 0` has the single level component `I^M`, which meets every face, so
  `d(0) = 0` and `D(M) >= 0`.
- *Upper bound.* If `delta = 0` then `d(delta) = 0`. Otherwise some level component has
  `delta(Omega) >= 1`, and `f(Omega) <= M`, so `d(delta) <= M - 1`.
- *`M = 1, 2`.* By Theorem 1 of `toms-two-level-spanning-holds-in-every-dimension`, every `delta`
  with `max delta <= 1` has a component with `f <= delta`. If `max delta >= 2` and `M <= 2`,
  a level component with `delta >= 2 >= M >= f` exists. Either way `d(delta) <= 0`. ∎

## Part 2: superadditivity

Let `delta_i` be usc on `I^(M_i)` and `delta(x, y) = delta_1(x) + delta_2(y)`. By Part 5 of
`toms-level-two-spanning-reduces-to-relative-hex-proof`:
- `delta` is usc;
- its level components are exactly the products `Omega_1 x Omega_2` of level components;
- `Omega_1 x Omega_2` meets the face `F x I^(M_2)` iff `Omega_1` meets `F`, and similarly in the
  second factor, so `f(Omega_1 x Omega_2) = f(Omega_1) + f(Omega_2)`;
- `delta(Omega_1 x Omega_2) = delta_1(Omega_1) + delta_2(Omega_2)`.

Hence `f - delta` adds over the product, and the minimum over all pairs is
`d(delta) = d(delta_1) + d(delta_2)`. Taking maximisers gives
`D(M_1 + M_2) >= D(M_1) + D(M_2)`. With `D(1) = 0` this gives `D(M + 1) >= D(M)`. ∎

## Part 3: rate

`D` is superadditive and `0 <= D(M) <= M`. By Fekete's lemma, `D(M)/M` converges to
`lambda = sup_M D(M)/M in [0, 1]`. In particular `D(M) <= lambda M` for every `M`. ∎

## Part 4: amplification

If `F(N_0)` fails, some `delta` on `I^(N_0)` has `d(delta) >= 1`, so `D(N_0) >= 1`. Part 2 gives
`D(k N_0) >= k D(N_0) >= k`. For `M = k N_0 + r` with `0 <= r < N_0`,
`D(M) >= D(k N_0) + D(r) >= k = floor(M/N_0)`, where `D(0) = 0` by convention (no factor).
Then `lambda >= 1/N_0 > 0`.

Conversely `lambda = 0` forces `D(M) <= 0` for every `M` by Part 3, which is `F(M)`. And
`D(M) = o(M)` means `lambda = 0`. So the three statements are equivalent. ∎

## Part 5: depth from the rate

Take a slice-constant target over `N` ideal two-wall windows, and its `delta` as in
`toms-slice-constant-targets-reduce-to-level-spanning`. By definition of `D(N)` there is a
level component `Omega` with `f(Omega) <= t + D(N)`, where `t = delta(Omega)`.
- *Failing to span versus failing face-wise.* The faces `x_nu = 0` and `x_nu = 1` lie in the
  chambers `A` and `C`. So if `Omega` does not span `nu` (misses `A` or `C`), it misses a face of
  `nu`. The number `f'` of coordinates `Omega` does not span therefore satisfies `f' <= f`.
- *The budget.* Part 2 of that proof gives `E(cl Omega) >= 2(N - f') - f'`, and Part 1 there
  gives `t + E(cl Omega) <= N`. So `N + t <= 3 f' <= 3t + 3 D(N)`, that is
  `t >= (N - 3 D(N))/2`.

The depth is at least `max delta >= t >= (N - 3D(N))/2 >= (1 - 3 lambda) N/2`. For `lambda = 0`
this is the `N/2` of the parent route. ∎

## Part 6: the exact local model

Let `X_n` be the product cell complex of `I^N` with `n` open intervals per coordinate, and let
`delta` be constant on its open cells. Then `{delta >= t}` is closed iff `delta(sigma) >=
delta(tau)` whenever `sigma` is a face of `tau`, and it suffices to check codimension-one
faces. Two cells lie in the same level component iff they are joined by a chain of
codimension-one face relations between cells of that level: a union of open cells of one level
is connected exactly along face relations, and if `sigma < rho < tau` with
`delta(sigma) = delta(tau)`, usc forces `delta(rho)` to the same value.

The formula of `face_form_sat.py` has, per cell, the level bits and six labels `l(nu, e)`.
Labels agree across equal-level codimension-one relations. The label `(nu, -)` ("my component
misses `x_nu = 1`") is forbidden on cells of the face `x_nu = 1`, and `(nu, +)` on cells of
`x_nu = 0`. At least `delta + 1` coordinates carry a label.
- A model gives labels constant on each level component, and each label certifies a missed
  face, so every component fails at least `delta + 1` coordinates. It is a face counterexample.
- Conversely a cell-constant face counterexample gives a model by labelling each component
  with its missed faces.

So SAT is a genuine counterexample to `F(N)`, and UNSAT rules out every cell-constant
counterexample on `X_n`. ∎
