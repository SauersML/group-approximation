---
rg: 2
id: fpbs-quotient-l2-threshold-sandwich
kind: claim
title: The quotient l2 threshold of a normal subgroup lies between p_c and both p_(2->2) and the relative threshold, and it does not change under amenable extensions
distinct_from:
  fpbs-fibre-summed-connectivity-operator: that is the norm comparison ||T_p|| <= ||S_p|| for one quotient at one p; this defines the threshold p^Q_(2->2)(N;G) of S_p, proves it is monotone in N and constant along amenable extensions, that it is an open condition with an l2 Aizenman-Barsky bound, and that it sits below p_c(N;G).
  fpbs-bk-majorant-kesten-gap-is-quotient-critical-l2: that shows ||S_(p_c)|| < infinity gives the relative gap through the Russo-BK majorant at p_c; this runs the same comparison from any base point p_0, which makes {p : ||S_p|| < infinity} an open interval and gives p_c < p^Q_(2->2) iff ||S_(p_c)|| < infinity.
  fpbs-sphere-fibre-operator-iff-critical-fibre-l2: that makes boundedness of S_(p_c) equivalent to one-radius conditions; this is about the whole parameter range, the ordering of four thresholds, and the dependence on N.
  fpbs-hutchcroft-l2-gap-criterion: that is Hutchcroft's p_(2->2) for the whole graph; this is its quotient relative version, which equals p_(2->2) exactly when N is amenable up to finite data, and equals p_c when Gamma/N is amenable.
  fpbs-percolation-kesten-normal-gap: that asks for p_c < p_c(N;G); this shows p_c < p^Q_(2->2)(N;G) is a sufficient condition that is monotone in N and blind to amenable extensions, and it names the open inequality separating the two (fpbs-relative-threshold-is-quotient-l2-threshold).
---

**ESTABLISHED.** Proof in `fpbs-quotient-l2-threshold-sandwich-proof`.

**Setting.**

- `Gamma` is finitely generated and `S` is a finite symmetric generating set
  with `d = |S|`. Put `G = Cay(Gamma,S)`, with `tau_p` and `T_p` as usual.
- For a normal subgroup `N` put `Q = Gamma/N` and `pi: Gamma -> Q`.
- The fibre-summed kernel is `sigma^N_p(q) = sum_(x in q) tau_p(o,x)`.
- For nonnegative `f` on a group `R`, write
  `||f||_R = sup{ <g, f*h> : g,h >= 0 finitely supported, ||g||_2 = ||h||_2 = 1 }`,
  a value in `[0,infinity]`. It is the operator norm of convolution by `f`
  when that is bounded. So `||sigma^N_p||_Q = ||S_p||_(l2(Q))`.
- Define the **quotient l2 threshold**
  `p^Q_(2->2)(N;G) = sup{ p in [0,1] : ||sigma^N_p||_Q < infinity }`.

**Theorem.**

1. **(Diagonal formula.)** `||sigma^N_p||_Q = limsup_m ( chi^(N,m)_p )^(1/m)`,
   where the `m`-chain relative susceptibility is
   `chi^(N,m)_p = sum_(y in N) (T_p^m)(o,y) = sigma_p^(*m)(e)`.
   The case `m = 1` is `chi^N_p = E_p|K_o ∩ N|`.
2. **(Monotone in the subgroup, blind to amenable extensions.)** If `N <= M`
   are normal subgroups, then `||sigma^N_p||_(Gamma/N) <= ||sigma^M_p||_(Gamma/M)`
   for every `p`, so `p^(Gamma/M)_(2->2)(M;G) <= p^(Gamma/N)_(2->2)(N;G)`.
   If `M/N` is amenable, both norms and both thresholds are equal.
3. **(Extremes.)** For `N = {e}` the threshold is `p_(2->2)(G)`. For `N = Gamma`
   it is `p_c(G)`. Hence for every normal `N`:
   * `p_c(G) <= p^Q_(2->2)(N;G) <= p_(2->2)(G)`;
   * if `N` is amenable, `p^Q_(2->2)(N;G) = p_(2->2)(G)`;
   * if `Q` is amenable, `p^Q_(2->2)(N;G) = p_c(G)`.
4. **(Below the relative threshold.)** If `N` is infinite, then
   `chi^N_p <= ||sigma^N_p||_Q`, and so `p^Q_(2->2)(N;G) <= p_c(N;G)`.
   With 3, for every infinite normal `N`:

   ```text
   p_c(G)  <=  p^Q_(2->2)(N;G)  <=  min{ p_(2->2)(G), p_c(N;G) }.
   ```

5. **(Openness and l2 Aizenman-Barsky bound.)** Suppose
   `||sigma^N_(p_0)||_Q = M < infinity`, `delta > 0`, `p_0 + delta <= 1` and
   `d delta M < 1`. Then
   `||sigma^N_(p_0+delta)||_Q <= M/(1 - d delta M)`. Consequently:
   * if `p^Q_(2->2)(N;G) < 1`, then for every `p < p^Q_(2->2)(N;G)`,
     `||sigma^N_p||_Q >= 1/(d (p^Q_(2->2)(N;G) - p))`;
   * if `Gamma` is infinite, `||sigma^N_p||_Q = infinity` at
     `p = p^Q_(2->2)(N;G)`.
6. **(Critical form.)** `p_c(G) < p^Q_(2->2)(N;G)` iff
   `||sigma^N_(p_c)||_Q < infinity`. When this holds and `N` is infinite, it
   gives `p_c(G) < p_c(N;G)` and `p_c(G) < p_(2->2)(G)`, hence
   `p_c(G) < p_u(G)`.

**What it changes for the Kesten premise.**

- By 4 and 6, the relative gap `p_c < p_c(N;G)` has a sufficient condition,
  `p_c < p^Q_(2->2)(N;G)`, that is monotone under shrinking `N` (by 2) and is
  unchanged by passing to `M ⊇ N` with `M/N` amenable.
- By 3, this sufficient condition is exactly Hutchcroft's condition
  `p_c < p_(2->2)` when `N` is amenable. It is false whenever `Q` is amenable,
  which is consistent with the Kesten premise.
- By 5, the threshold `p^Q_(2->2)` is where `||sigma^N_p||_Q` blows up, at
  least as fast as `1/(d(p^Q_(2->2) - p))`.
- The only room for the premise beyond critical fibre l2 is a strict
  inequality `p^Q_(2->2)(N;G) < p_c(N;G)`. The open claim
  `fpbs-relative-threshold-is-quotient-l2-threshold` asserts there is none.
