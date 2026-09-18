---
rg: 2
id: ugc-sqrt-scale-equivalence-proof
kind: route
title: Constant-round Dinur--Steurer repetition turns a sqrt-scale unique games gap into the root gap, and dilution rescales it
target: sqrt-scale-unique-games-hardness-is-equivalent-to-ugc
requires: [dinur-steurer-projection-game-repetition-bound]
---

Every instance is a bipartite unique game given as an edge multiset `E`, with
the uniform distribution on `E`. All reductions below are Karp reductions of
promise problems. They map YES instances to YES instances and NO instances to
NO instances.

**Step 0: tensoring.** Fix a constant `t`. The map `G -> G^(x t)` has
alphabet `[k]^t` and edge multiset `E^t`, so it runs in time `poly(|E|^t)`.

* Completeness. If `f, g` achieve `val(G) >= 1 - eta`, then the product
  assignments `f^t, g^t` satisfy a tuple of edges iff they satisfy every
  coordinate. The coordinates are independent, so
  `val(G^(x t)) >= (1-eta)^t >= 1 - t eta` (Bernoulli).
* Soundness. If `val(G) <= 1 - g` with `g` in `[0,1]`, then
  `val(G^(x t)) <= exp(-g^2 t/16)`. This is the consequence recorded in
  `dinur-steurer-projection-game-repetition-bound`.

**Step 1: amplification lemma.** Assume `Gap-UG_k[1-eta, 1-g]` is NP-hard with
`g` in `(0,1]`, and let `eps', delta'` be in `(0,1/2]`. Assume
`g^2 >= 32 ln(1/delta') eta/eps'` and `eta <= eps'`. Put `t = floor(eps'/eta)`.
Then `t >= 1`, and `t >= eps'/(2 eta)` because `floor(x) >= x/2` for `x >= 1`.

* Step 0 gives completeness `>= 1 - t eta >= 1 - eps'`.
* Step 0 gives soundness `<= exp(-g^2 t/16)`. Since
  `g^2 t/16 >= (32 ln(1/delta') eta/eps') (eps'/(2 eta))/16 = ln(1/delta')`,
  soundness is `<= delta'`.

So `Gap-UG_(k^t)[1-eps', delta']` is NP-hard.

**Step 2: (SQ) implies (UGC).** Let `eps` be in `(0,1/2)`. Put
`C = sqrt(32 ln(1/eps)/eps)`. Then `C >= 1`, because `32 ln 2 * 2 > 1`.
By (SQ) there are `eta <= 1/C^2` and `k` such that
`Gap-UG_k[1-eta, 1-C sqrt(eta)]` is NP-hard.

Put `g = C sqrt(eta)`, so `g <= 1`. Then `g^2 = 32 ln(1/eps) eta/eps`. Also
`eta <= 1/C^2 = eps/(32 ln(1/eps)) <= eps`. Apply Step 1 with
`eps' = delta' = eps`. It gives that `Gap-UG_(k^t)[1-eps, eps]` is NP-hard.

**Step 3: (UGC) implies (SQ).** Let `C >= 1`, and put `eta = 1/(4C^2)`. This is
at most `1/4`, and at most `1/C^2`. By (UGC) there is `k` such that
`Gap-UG_k[1-eta, eta]` is NP-hard. Its NO set `val <= eta` lies inside
`val <= 1/2 = 1 - C sqrt(eta)`, and its YES set is unchanged. So the identity
map reduces `Gap-UG_k[1-eta, eta]` to `Gap-UG_k[1-eta, 1-C sqrt(eta)]`, and the
latter is NP-hard.

**Step 4: dilution.** Let `rho = p/q` with `1 <= p <= q` integers, and let `G`
have `N` edges. Build `G'` as follows:

* copy every edge of `G` `p` times;
* add a fresh left vertex `u*` and a fresh right vertex `v*`;
* add `(q-p) N` parallel copies of the identity constraint on `u* v*`.

The fresh edges are satisfied by any assignment with `f(u*) = g(v*)`,
independently of the rest. So

```text
val(G') = (p N val(G) + (q-p) N)/(q N) = rho val(G) + 1 - rho .
```

Hence `val(G) >= 1 - a` implies `val(G') >= 1 - rho a`, and `val(G) <= 1 - b`
implies `val(G') <= 1 - rho b`. The alphabet is unchanged and the size is
`qN`. So NP-hardness of `Gap-UG_k[1-a, 1-b]` transfers to
`Gap-UG_k[1-rho a, 1-rho b]`.

**Step 5: squaring law.** Assume `Gap-UG_k[1-eta_0, 1-R sqrt(eta_0)]` is
NP-hard, with `R >= 6` and `eta_0 <= 1/R^2`. Put `g = R sqrt(eta_0)`, which is
at most `1`, and `t = ceil(16/(R^2 eta_0))`.

* By Step 0, completeness is `>= 1 - t eta_0`. Since
  `t eta_0 < 16/R^2 + eta_0 <= 17/R^2`, completeness is `>= 1 - 17/R^2`.
* By Step 0, soundness is `<= exp(-R^2 eta_0 t/16) <= e^-1`.

So `Gap-UG_(k^t)[1-17/R^2, 1/e]` is NP-hard. Here `17/R^2 <= 17/36 < 1 - 1/e`,
so this is a genuine gap.

Now apply Step 4 with `a = 17/R^2` and `b = 1 - 1/e`. It gives that
`Gap-UG_(k^t)[1 - 17 rho/R^2, 1 - (1-1/e) rho]` is NP-hard for every rational
`rho` in `(0,1]`. The deficit ratio is `b/a = (1-1/e) R^2/17 = 0.0371... R^2`,
which is at least `R^2/27`.

Steps 2 and 3 prove the equivalence. Step 1 is the explicit amplification.
Step 5 is the squaring law. `square`

**Numerics.** `experiments/ugc-sqrt-scale-2026-09-17/check_sqrt_scale.py`
checks the parameter arithmetic of Step 1 on 180 cases and of Step 5 on 25
cases. It also checks the inequality behind Step 0's soundness. It reports no
violations.
