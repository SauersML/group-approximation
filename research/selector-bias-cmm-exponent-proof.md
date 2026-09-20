---
rg: 2
id: selector-bias-cmm-exponent-proof
kind: route
title: Run CMM low-value rounding on the selector's YES lift, pull the labelling back through the sandwich, and accept iff its 2-to-1 value beats delta
target: selector-bias-is-capped-by-the-cmm-alphabet-soundness-exponent
requires: [cmm-unique-games-low-value-rounding, cmm-unique-games-sqrt-log-k-rounding, orientation-lifts-sandwich-2to1-game-values]
---

Notation is that of the target.

**Step 0 (the lift is a CMM instance).** `U_o` has left alphabet `[K]`. By the
sandwich setting, its right alphabet is `[k] x {0,1}`, identified with `[2k] = [K]`.
Edge `e = (p, q)` carries the map `a -> (p_e(a), o_e(a))`. This map is a
bijection: `p_e` is exactly 2-to-1, and `o_e` is injective on each fibre. So
`U_o` is a unique game in the sense of CMM Definition 1.1. Its constraint graph
is the bipartite multigraph of `G`, with each edge taken with its
multiplicity, and each edge carries a permutation of `[K]`. It is computed from
`G` and `o` in polynomial time, one table per edge.

**Step 1 (pull-back).** Let `(f, h)` be a labelling of `U_o`, with
`f(p) in [K]` and `h(q) = (tau_q, b_q) in [k] x {0,1}`. Put `F := (f, tau)`, a
labelling of `G`. If `(f, h)` satisfies `e = (p, q)` then
`(p_e(f(p)), o_e(f(p))) = (tau_q, b_q)`, so `p_e(f(p)) = tau_q`, and `F`
satisfies `e` in `G`. Hence `val_G(F) >= val_(U_o)(f, h)`. This is the upper
half of item 1 of `orientation-lifts-sandwich-2to1-game-values`, applied to a
single labelling. The artifact checks it exhaustively on toy games.

**Algorithm T.** On input `x`:

1. compute `G(x)` and `delta(x)`;
2. run `S(x)` to get `o`, and build `U_o`;
3. run the algorithm of `cmm-unique-games-low-value-rounding` on `U_o`, getting
   `(f, h)`;
4. form `F` as in Step 1 and compute `val_G(F)` exactly, as a rational with
   polynomially many bits;
5. accept iff `val_G(F) > delta(x)`.

Every step takes polynomial time.

**NO inputs.** `val_G(F) <= val(G(x)) <= delta(x)`, so T never accepts.

**YES inputs.** With probability at least `theta` over `S`, `val(U_o) >= 1 - eps`.
Fix such an `o`. The optimum of `U_o` is `1 - eps*` with `eps* <= eps`. By the
CMM claim and monotonicity of `g` in `eps`, the satisfied fraction `X` of
`(f, h)` has `E[X] >= g(eps*, K) >= g(eps, K) >= delta + 1/p`. Since
`0 <= X <= 1`,
`E[X] <= delta Pr[X <= delta] + Pr[X > delta] <= delta + Pr[X > delta]`. So
`Pr[X > delta] >= 1/p`. By Step 1, `val_G(F) >= X`. So T accepts with
probability at least `theta/p >= 1/poly`. Repeating T polynomially many times
gives `Lang in RP`, with one-sided error. This proves **Theorem K**.

**Corollary K1.** Put `e := e(eps) < s`, and pick `gamma > 0` with
`e + 2 gamma < s`. For all large `j`, `delta_j <= K_j^(-(e + gamma))`. Take
`K := K_j >= e^(1/eps)` when `eps > 0`. Then

```text
g(eps, K)  =  c_0 (1-eps)^2 (eps ln K)^(-1/2) (ln K)^(e/2) K^(-e)  >=  c_0 (1-eps)^2 eps^(-1/2) (ln K)^(-1/2) K^(-e).
```

At `eps = 0`, `g = c_0`. In both cases
`g - delta_j >= K^(-e) (c_0' (ln K)^(-1/2) - K^(-gamma))`, with
`c_0' = c_0 (1-eps)^2 max(1, eps^(-1/2))`. This is at least
`(c_0'/2) K^(-e) (ln K)^(-1/2)` once `K` is large. `K <= poly(|x|)`, because
`G_j(x)` is written out in polynomial time. So the gap is at least
`1/poly(|x|)`, and Theorem K applies to `(G_j, S_j)`. The rewriting
`e(1-c) = (1-c)/(1+c)` is algebra, checked symbolically in the artifact. It is
equivalent to `c > (1-s)/(1+s)`. The alphabet price is the contrapositive.

**Corollary K2.** The fixed rule is a deterministic polynomial-time orientation.
By the lower half of item 1 of the sandwich, `val(U_o) >= val(G)/2`. On YES
inputs that is `>= (1-eta)/2 = 1 - (1+eta)/2`. Apply K1 with
`eps = (1+eta)/2 < 1`. The identity `e((1+eta)/2) = (1+eta)/(3-eta)` holds, and
at `d = 2` it equals the exponent `(d-1+eta)/(d+1-eta)` quoted from CMM
Section 5 in the citation. Both are checked in the artifact.

**Corollary K3.** Let `c > 1/2` be a constant. Then `e(1-c) = (1-c)/(1+c) < 1/3 <= s`,
and K1 applies.

**Corollary K4.** Run T with step 3 replaced by the algorithm of
`cmm-unique-games-sqrt-log-k-rounding`. By that claim,
`E[1 - X] <= a := A sqrt(eta' ln K)`. By Markov,
`Pr[1 - X >= 1 - delta] <= a/(1 - delta) <= 1 - 1/p`. So `Pr[X > delta] >= 1/p`,
and the rest of the proof of Theorem K is unchanged. The second inequality is
K1 with `eps = eta'`: `e(eta') >= s` is `eta' >= 2s/(1+s)`.
