---
rg: 2
id: fpbs-worst-pair-collapse-realized-on-amenable-growth-proof
kind: route
title: Relative Burton-Keane with the whole amenable group gives uniqueness above p_c, and the amenability-blind worst-pair proofs then force the jump, the slope and the spikes
target: fpbs-worst-pair-collapse-realized-on-amenable-growth
requires:
  - fpbs-hp-relative-burton-keane
  - fpbs-worst-pair-connectivity-rate-kernel
  - fpbs-worst-pair-critical-rate-and-chemical-slope-tradeoff
  - fpbs-intrinsic-rates-log-lipschitz-in-parameter
  - fpbs-intrinsic-l2-rate-closed-zero-set
  - fpbs-transitive-sharpness-linear-lower-bound
---

Complete written proof. Notation as in the claim. No computation is used.

**Transfer principle (checked line by line).** The proofs cited below are
written for a nonamenable `Gamma`. They use only the following, all of which
hold on every Cayley graph `H` with `gr > 1` and `p_c(H) < 1`:

- vertex-transitivity;
- Harris–FKG, BK and Fekete;
- lower semicontinuity of `tau_p(o,v) = sup_R P_p(o <-> v inside B_R)`;
- the thinning coupling;
- `|B_(n+m)| <= |B_n||B_m|`;
- Duminil-Copin–Tassion sharpness, which is stated for all infinite locally
  finite vertex-transitive graphs.

The word "nonamenable" appears in them only in the Setting and in
`gr > 1`. Specifically:

- **(T1)** Proof of `fpbs-worst-pair-connectivity-rate-kernel`, item 1:
  supermultiplicativity of `kappa_p`, the limit `gamma = inf_n a_n/n`,
  monotonicity and left-continuity. Item 2's argument: uniqueness at `t`
  gives `tau_t(u,v) >= theta(t)^2`. Item 3: `limsup_r (1/r) log|S_r| >= log gr`
  and `g >= log gr - gamma`.
- **(T2)** Proof of `fpbs-worst-pair-critical-rate-and-chemical-slope-tradeoff`,
  items 1, 2 and 5. Its inputs are:
  - (I1), which is (T1);
  - (I2), thinning: item 1 of `fpbs-intrinsic-rates-log-lipschitz-in-parameter`,
    a coupling valid on every graph;
  - (I3), `chi(p) < infinity` for `p < p_c`: Lemma 3.1 of
    `fpbs-intrinsic-l2-rate-closed-zero-set-proof`, which uses only the
    Duminil-Copin–Tassion characterisation of `p_c` by `varphi_p(S) < 1`;
  - (I4), ball submultiplicativity.
- **(T3)** `fpbs-transitive-sharpness-linear-lower-bound` is stated for
  transitive graphs: `theta(p_c+epsilon) >= K epsilon` for
  `0 < epsilon <= eta`.

## Explicit instance

Let `Lambda = Z_2 wr Z^2`, with elements `(phi, z)`, where
`phi : Z^2 -> Z_2` has finite support. Let `S = {a, e_1^(±1), e_2^(±1)}`.
Right multiplication by `a` toggles `phi(z)`; right multiplication by `e_i`
moves `z` to `z + e_i`.

- *Amenable.* `Lambda` is an extension of the abelian group `⊕ Z_2` by `Z^2`.
  Amenability is closed under extensions, and abelian groups are amenable.
- *Growth.* For `epsilon in {0,1}^n`, the word
  `a^(epsilon_1) e_1 a^(epsilon_2) e_1 ... a^(epsilon_n) e_1` has length at most
  `2n` and equals `(phi_epsilon, n e_1)`, with `phi_epsilon(j e_1) = epsilon_(j+1)`
  for `0 <= j < n` and `phi_epsilon = 0` elsewhere. Distinct `epsilon` give
  distinct elements, so `|B_(2n)| >= 2^n` and `gr >= sqrt 2 > 1`.
- *`p_c < 1`.* The edges labelled `e_1, e_2` among the vertices `(0, z)` form a
  copy of the square lattice. So `p_c(H) <= p_c(Z^2) < 1`, by the Peierls
  contour bound. Also `p_c(H) > 0`, since `H` has bounded degree.

## Item 1

Fix `t in (p_c,1]`.

- *Existence.* `theta` is nondecreasing and `p_c = inf{p : theta(p) > 0}`, so
  `theta(t) > 0`. The event that an infinite cluster exists is invariant under
  changing finitely many edges, so by Kolmogorov's 0-1 law it has probability
  0 or 1. It has probability at least `theta(t) > 0`, so it has probability 1.
- *Uniqueness.* Apply `fpbs-hp-relative-burton-keane` with the subgroup equal to
  `Lambda` itself. `Lambda` is amenable, and a cluster is `Lambda`-infinite
  exactly when it is infinite. So there is at most one infinite cluster a.s.,
  and by the previous point exactly one.
- *Connection bound.* If `u` and `v` both lie in infinite clusters, they lie in
  the unique one, so `u <-> v`. The events `{u <-> infinity}` and
  `{v <-> infinity}` are increasing, so by Harris–FKG and transitivity
  `tau_t(u,v) >= theta(t)^2`.
- *Rate.* So `kappa_t(n) >= theta(t)^2` for every `n`, and
  `gamma(t) = lim -(1/n) log kappa_t(n) = 0`.

## Item 2

By (T2), item 1 of the trade-off claim holds on `H`:
`kappa_p(n) <= gr^(-n)` for every `n >= 1` and every `p <= p_c`. So
`gamma(p) >= log gr` for `p <= p_c`. With item 1, `gamma = 0` on `(p_c,1]`.
Kernel (K) asks for `gamma(t) > 0` at some `t > p_c`, which is false on `H`.

## Item 3

By (T2), item 2 of the trade-off claim holds on `H`: for `t in (p_c,1]`,
`gamma(t) + l(t) log(t/p_c) >= log gr`. With `gamma(t) = 0` and
`0 < p_c < t <= 1`, this gives `l(t) >= log(gr)/log(t/p_c)`, including the case
`l(t) = +infinity`. For `t = p_c + epsilon`, `log(1 + epsilon/p_c) <= epsilon/p_c`
gives `l(p_c+epsilon) >= p_c log(gr)/epsilon`.

The stretch statement is item 5 of the trade-off claim, which holds on `H` by
(T2). (CS) asks for `l(t) log(t/p_c) < log gr` at some `t > p_c`, which is
false on `H` at every `t`.

## Item 4

- *Below `p_c`.* For `p < p_c`, `E_p|K_o ∩ S_r| <= E_p|K_o| = chi(p)`, which is
  finite by (I3). So `g(p) <= 0`.
- *Upper bound.* For every `p`, `E_p|K_o ∩ S_r| <= |S_r| <= |B_r|`, and
  `(1/r) log|B_r| -> log gr`. So `g(p) <= log gr`.
- *Lower bound above `p_c`.* For `t in (p_c,1]`, item 1 gives
  `E_t|K_o ∩ S_r| = sum_(x in S_r) tau_t(o,x) >= theta(t)^2 |S_r|`. By (T1),
  `limsup_r (1/r) log|S_r| >= log gr`. So `g(t) >= log gr`.
- *Conclusion.* `g(t) = log gr` on `(p_c,1]`, so `lim_(t↓p_c) g(t) = log gr > 0`.
  - (K') asks for `g(t) < log gr` at some `t > p_c`: false.
  - (EG) asks for `g(t) -> 0` as `t ↓ p_c`: false.
  - If `g(p_c) < log gr`, then `g` is not right-continuous at `p_c`, so (EG1)
    fails. Otherwise `g(p_c) = log gr > 0`, so (EG0) fails.

## Item 5

Fix `alpha in (0,(log gr)/2)`. Take `n` large enough that
`e^(-alpha n) <= min(eta, 1 - p_c)`, with `eta` from (T3). Put
`s_n = p_c + e^(-alpha n)` and take `v_n in A_n`.

- *Upper end.* By item 1 and (T3),
  `tau_(s_n)(o,v_n) >= theta(s_n)^2 >= K^2 e^(-2 alpha n)`.
- *Truncation.* `P_(s_n)(o <-> v_n inside B_R)` increases to `tau_(s_n)(o,v_n)`
  as `R -> infinity`. So some `R_n >= n` has
  `f_n(s_n) >= K^2 e^(-2 alpha n)/2`, where
  `f_n(q) = P_q(E_n)` and `E_n = {o <-> v_n inside B_(R_n)}`.
- *Lower end.* By item 2, `f_n(p_c) <= tau_(p_c)(o,v_n) = kappa_(p_c)(n) <= gr^(-n)`.
  Also `f_n(q) >= q^n > 0` for `q > 0`, using a geodesic from `o` to `v_n`,
  which lies in `B_n ⊆ B_(R_n)`.
- *Russo.* `f_n` is a polynomial in `q`, since `E_n` depends on the finitely
  many edges of `B_(R_n)`. `E_n` is increasing.
  - Russo's formula gives `f_n'(q) = sum_e P_q(e pivotal for E_n)`.
  - Pivotality of `e` does not depend on the state of `e`, and an open pivotal
    edge forces `E_n`. So `P_q(e pivotal) = q^(-1) P_q(e pivotal, e open)`.
  - On `E_n`, every pivotal edge is open, so
    `sum_e P_q(e pivotal, e open) = E_q[N^(R_n)(o,v_n); E_n]`.
  - Hence `d log f_n / d log q = h_n(q) := E_q[N^(R_n)(o,v_n) | E_n]`, a
    continuous function on `(0,1]`.
- *Mean value.* Apply the mean-value theorem to `u -> log f_n(e^u)` on
  `[log p_c, log s_n]`. Some `q_n in (p_c,s_n)` has

  ```text
  h_n(q_n)  =  ( log f_n(s_n) - log f_n(p_c) ) / log(s_n/p_c)
            >=  ( (log gr - 2 alpha) n + log(K^2/2) ) / log(s_n/p_c) .
  ```

  Since `log(s_n/p_c) <= e^(-alpha n)/p_c`, the right side is at least
  `p_c ((log gr - 2 alpha) n + log(K^2/2)) e^(alpha n)`.

## Item 6

Suppose an argument derives (K), (CS), (K') or (EG) for an arbitrary Cayley
graph `G` from facts that hold for every Cayley graph with `gr > 1` and
`p_c < 1`. Applied to `H`, it gives one of:

- `gamma_H(t) > 0` for some `t > p_c(H)`, contradicting item 2;
- `l_H(t) log(t/p_c) < log gr` for some `t`, contradicting item 3;
- `g_H(t) < log gr` for some `t > p_c`, contradicting item 4;
- `g_H(t) -> 0`, contradicting item 4.

So the argument is invalid.

At and below `p_c`, every quantity on the route behaves on `H` exactly as on a
nonamenable graph:

- `gamma >= log gr` on `[0,p_c]`;
- `g <= 0` on `[0,p_c)`;
- thinning, the trade-off inequality and the stretch bound hold.

So the hypothesis that fails on `H` must be consumed at a step that concludes a
lower bound on `gamma(t)`, an upper bound on `l(t)`, or `g(t) < log gr`, for
some `t > p_c`. The inputs (T1)–(T3), Russo, Harris–FKG, BK and Fekete are all
facts of the amenability-blind kind.

## Item 7

If `Q(H)` held, the amenability-blind argument `Q => (K)`, run on `H`, would
give (K) on `H`, contradicting item 2.

- (CS) implies (K) by item 3 of the trade-off claim, whose proof uses (T2).
- (K') implies (K) by item 3 of the kernel claim, whose proof uses (T1).
- For the summability example, directly: `tau_t(o,x) >= theta(t)^2 > 0` for
  every `x`, by item 1, and `H` is infinite. So
  `sum_x tau_t(o,x)^q = infinity` for every `t > p_c` and every finite `q`.

QED.
