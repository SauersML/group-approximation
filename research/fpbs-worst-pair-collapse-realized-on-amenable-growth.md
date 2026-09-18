---
rg: 2
id: fpbs-worst-pair-collapse-realized-on-amenable-growth
kind: claim
title: On every amenable Cayley graph of exponential growth the worst-pair rate jumps by at least log gr at p_c, so the kernels K, CS, K' and EG fail there and every proof of them must consume nonamenability
distinct_from:
  fpbs-worst-pair-critical-rate-and-chemical-slope-tradeoff: that proves the trade-off inequality and records the forced slope as a consequence of a hypothetical collapse on a nonamenable graph; this shows the same proofs run on amenable Cayley graphs of exponential growth, where the collapse alternative is a theorem, so the forced slope, the jump and the spikes are realized and cannot yield a contradiction
  fpbs-worst-pair-connectivity-rate-kernel: that proves (K) implies p_c < p_u on nonamenable graphs; this proves (K) itself is false on every amenable Cayley graph with gr > 1 and p_c < 1
  fpbs-pivotal-budget-universal: its amenable calibration attempt is heuristic (unproved near-critical pivotal bounds on Z^d) and kills no class; this calibration is rigorous from established nodes and is about the worst-pair, chemical-slope and sphere-rate kernels, not the pivotal budget
  fpbs-lattice-amenable-subgroup-critical-finiteness-no-gap: that calibrates the relative-susceptibility lane on Z^d, of polynomial growth; this calibrates the worst-pair lane, which needs gr > 1 and so is vacuous on Z^d
---

**ESTABLISHED.** Proof in `fpbs-worst-pair-collapse-realized-on-amenable-growth-proof`.

**Setting.** `H = Cay(Lambda,S)` is a Cayley graph of a finitely generated
**amenable** group with `gr = lim |B_n|^(1/n) > 1` and `p_c(H) < 1`.
Notation `tau`, `kappa_p(n)`, `gamma`, `A_n`, `s_t`, `l(t)` and
`g(p) = limsup_r (1/r) log E_p|K_o ∩ S_r|` is exactly that of
`fpbs-worst-pair-connectivity-rate-kernel` and
`fpbs-worst-pair-critical-rate-and-chemical-slope-tradeoff`, read on `H`.

**Explicit instance.** `Lambda = Z_2 wr Z^2 = (⊕_(Z^2) Z_2) ⋊ Z^2` with
`S = {a, e_1^(±1), e_2^(±1)}`, where `a` switches the lamp at the head. It is
metabelian, hence amenable; `|B_(2n)| >= 2^n`, so `gr >= sqrt 2`; its Cayley
graph contains the square lattice on the coset `Z^2`, so `p_c(H) <= p_c(Z^2) < 1`.

**Theorem.** On every such `H`:

1. *(Uniqueness above `p_c`.)* For every `t in (p_c,1]`, `omega_t` has exactly
   one infinite cluster a.s., `tau_t(u,v) >= theta(t)^2 > 0` for all `u,v`, and
   `gamma(t) = 0`.
2. *(The jump.)* `gamma(p) >= log gr` for every `p <= p_c`, and `gamma = 0` on
   `(p_c,1]`. So `gamma` drops by at least `log gr` at `p_c`. Kernel (K) is
   false on `H`.
3. *(Forced slope, unconditionally.)* For every `t in (p_c,1]`,
   `l(t) >= log(gr)/log(t/p_c)`, and `l(p_c+epsilon) >= p_c log(gr)/epsilon`.
   Every linear stretch constant at `t` is at least `log(gr)/log(t/p_c)`.
   Kernel (CS) is false on `H` at every `t`.
4. *(Sphere rate.)* `g(p) <= 0` for `p < p_c` and `g(t) = log gr` for every
   `t in (p_c,1]`. So `lim_(t↓p_c) g(t) = log gr`. Kernels (K') and (EG) are
   false on `H`, and (EG) fails through (EG1) whenever `g(p_c) < log gr`.
5. *(Deterministic-endpoint pivotal spikes, unconditionally.)* Fix
   `alpha in (0, (log gr)/2)` and put `s_n = p_c + e^(-alpha n)`. For all
   large `n`, each `v_n in A_n` has some `R_n >= n` and `q_n in (p_c,s_n)` with

   ```text
   E_(q_n)[ N^(R_n)(o,v_n) | o <-> v_n inside B_(R_n) ]
       >=  ( (log gr - 2 alpha) n + log(K^2/2) ) / log(s_n/p_c) ,
   ```

   where `N^R(o,v)` counts edges pivotal for `{o <-> v inside B_R}` and `K` is
   the constant of `fpbs-transitive-sharpness-linear-lower-bound`. This is the
   spike that Attempt 2 of
   `fpbs-worst-pair-connectivity-rate-positive-above-pc-universal` derived
   *under collapse*; on `H` it holds outright.
6. *(Calibration obstruction.)* Let an argument deduce (K), (CS), (K') or (EG)
   for a Cayley graph `G` using only facts that hold on every Cayley graph with
   `gr > 1` and `p_c < 1`. Then the argument is invalid, since run on `H` it
   contradicts items 2–4. This covers every input of the proofs of
   `fpbs-worst-pair-connectivity-rate-kernel` (items 1–3, 6),
   `fpbs-worst-pair-critical-rate-and-chemical-slope-tradeoff` (items 1, 2, 5),
   `fpbs-intrinsic-rates-log-lipschitz-in-parameter` (item 1: thinning),
   `fpbs-transitive-sharpness-linear-lower-bound`, Russo's formula,
   Harris–FKG, BK and Fekete.
7. *(Any kernel above (K).)* If a statement `Q(G)` implies (K) for `G` by an
   argument of the kind in item 6, then `Q(H)` is false. Examples:
   - (CS), via item 3 of the trade-off claim;
   - (K'), via item 3 of the kernel claim;
   - any summability `sum_x tau_t(o,x)^q < infinity` at some `t > p_c` and
     finite `q`, which already fails on `H` because `tau_t >= theta(t)^2`.

   Every new hole placed between such a `Q` and (K) inherits the obstruction.

**Invariant and the step where the class dies.** The invariant is amenability.
It enters through uniqueness (`fpbs-hp-relative-burton-keane` with the
subgroup equal to the whole group). Every argument of item 6 dies at the step
that bounds, for some `t > p_c`:

- `gamma(t)` from below, or
- `l(t)` from above, or
- `g(t)` strictly below `log gr`.

On `H` each of these bounds is false at every `t > p_c`. So that step must use
a hypothesis that fails on `H`, such as `rho < 1`, a positive Cheeger constant,
or a consequence proved only under nonamenability.

The worst-pair budget `log gr` does not see amenability: `gr > 1` on `H`.
Contrast the walk-averaged budget `log(1/rho)` of
`fpbs-collapse-exponential-pivotal-spikes`, which is `0` on every amenable
graph by Kesten. Every collapse consequence recorded on the worst-pair lane is
a theorem on `H`:

- the jump of `gamma` of size at least `log gr`;
- the forced slope `p_c log(gr)/epsilon`;
- the deterministic-endpoint spikes at exponent `log gr`.

So none of them can be contradicted using amenability-blind inputs.

**Reading for (CS).** Its mean-field heuristic, conditional slope of order
`epsilon^(-1/2)`, is violated on `H` by at least a factor
`c epsilon^(-1/2)`. So "a collapse must break the mean-field slope" is not
evidence against collapse unless the heuristic's mechanism is itself derived
from nonamenability.
