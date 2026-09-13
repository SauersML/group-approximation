---
rg: 2
id: houghton-h2-not-fp2-over-q-proof
kind: route
title: A shift-invariant coinvariant class in the product of group algebras obstructs FP_2 over Q
target: houghton-h2-is-not-fp2-over-q
requires:
  - fp2-over-q-descends-along-locally-finite-kernels
---

Let `G = H = K x| <t>` with `K = FSym(Z)` and `t(x) = x + 1`, so
`t^k (a b) t^(-k) = (a+k, b+k)`. Modules are left modules; `Q` is the trivial
right module; `Tor` is over `Q[G]`. Write `e_F` and `M_K = M / I_K M` as in
`fp2-over-q-descends-along-locally-finite-kernels`, whose Step 1 describes
`I_K M` and whose Step 2 makes `M -> M_K` exact, since `K` is locally finite.

**Step A: `FP_2` makes `Tor_1(Q, -)` commute with products.** Suppose `G` is
of type `FP_2` over `Q`. Take a free resolution `P_.` of the right module `Q`
with `P_0, P_1, P_2` finitely generated (the anti-involution `g -> g^(-1)`
switches sides). For finitely generated free `P`,
`P (x) prod_i N_i = prod_i (P (x) N_i)`, and products are exact. So for every
index set `I`,
`Tor_1(Q, prod_I Q[G]) = prod_I Tor_1(Q, Q[G]) = 0`,
because `Q[G]` is free.

**Step B: `Tor_1` through the cyclic quotient.** Let `R = Q (x)_(Q[K]) Q[G]`.
This is `Q[G]/I_K Q[G] = Q[G/K]`, a right `Q[G]`-module. For every `M`,
`R (x)_(Q[G]) M = M_K`, and this functor is exact, so `R` is flat. The
sequence `0 -> R -> R -> Q -> 0`, whose first map is right multiplication by
`t - 1` and whose second is the augmentation, is exact, since `Q[G/K]` is a
Laurent polynomial ring in `t`. In the long exact sequence,
`Tor_1(R, M) = 0` by flatness, so

`Tor_1(Q, M) = ker( t - 1 : M_K -> M_K )`.

The operator `t` acts on `M_K` because `I_K M` is `t`-stable.

**Step C: an invariant class.** Let `M = prod_(n >= 1) Q[G]`, and `s = (0 1)`.
For `n >= 1` put
- `s_n = t^(-(n+1)) s t^(n+1) = (-n-1, -n)`, disjoint from `s`, so `s` and
  `s_n` commute;
- `a_n = (1 - s)(1 - s_n) = (1 - s_n)(1 - s)` in `Q[K]`;
- `y_n = (sum_(i=0)^n t^i) a_n`, and `y = (y_n)_n in M`.

*(C1) `(t-1)y` lies in `I_K M`.* We have `(t - 1) y_n = t^(n+1) a_n - a_n`.
Let `F = {1, s}`. Then:
- `e_F a_n = e_F (1 - s)(1 - s_n) = 0`;
- `e_F t^(n+1) a_n = t^(n+1) e_(<s_n>) a_n = t^(n+1) e_(<s_n>) (1 - s_n)(1 - s) = 0`.

So `e_F (t - 1) y = 0` coordinatewise with one `F`, and `(t - 1) y in I_K M`
by Step 1 of the lemma.

*(C2) `y` does not lie in `I_K M`.* Suppose `e_(F') y = 0` for some finite
`F' <= K`. Then `F' <= Sym(S)` for a finite `S` in `Z`; let
`r = max(|x| : x in S)`, or `r = 0` if `S` is empty. Choose `n >= 2r + 4` and
`j = r + 2`.
- Decomposition. Since `Q[G] = (+)_(i in Z) t^i Q[K]`,
  `e_(F') y_n = sum_(i=0)^n t^i e_(A_i) a_n` with `A_i = t^(-i) F' t^i`, and it
  vanishes only if each `e_(A_i) a_n` vanishes.
- Support of `A_j`. For `pi in Sym(S)`, `t^(-j) pi t^j` moves only points of
  `S - j`, which lies in `[-2r-2, -2]`.
- Disjointness. `A_j` is supported in `[-2r-2, -2]`, `s` on `{0,1}`, and `s_n`
  on `{-n-1, -n}` with `-n <= -2r-4`. These three supports are pairwise
  disjoint, so `A_j`, `<s>` and `<s_n>` generate their direct product `D`.
- Nonvanishing. Under `Q[D] = Q[A_j] (x)_Q Q[<s>] (x)_Q Q[<s_n>]`, the element
  `e_(A_j) a_n` corresponds to `e_(A_j) (x) (1 - s) (x) (1 - s_n)`, a tensor
  of nonzero vectors, which is nonzero. `Q[D]` embeds in `Q[K]`, so
  `e_(A_j) a_n != 0`.

This contradicts `e_(F') y = 0`, so `y` is not in `I_K M`.

**Conclusion.** The class of `y` in `M_K` is nonzero and fixed by `t`. By
Step B, `Tor_1(Q, prod_N Q[G]) != 0`. By Step A, `G` is not of type `FP_2` over
`Q`. `∎`
