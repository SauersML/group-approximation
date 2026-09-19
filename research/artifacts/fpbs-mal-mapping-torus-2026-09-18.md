# The ascending HNN overgroup of Gamma_mal cannot decide the single-stage floor

Lane: swarm-0917-w10-w10-fp-break (belief breaker for `fpbs-fixed-price-universal`),
September 18, 2026. Target: `fpbs-mal-bernoulli-single-stage-floor` (stays OPEN).
Script: `experiments/mal-mapping-torus-2026-09-17/twisted_double_coset.py`.

## 0. Setup

Let `L = F(a, b)` and `phi(a) = a`, `phi(b) = b a b^{-2}`. This is the stage
endomorphism of `Gamma_mal = <a, b_1, b_2, ... | b_k = b_{k+1} a b_{k+1}^{-2}>`,
where `b_k` maps to `b` in the `k`-th copy of `L`. Let `G` be the ascending HNN extension

    G = < a, b, t | t^{-1} a t = a,  t^{-1} b t = b a b^{-2} >,   t^{-1} x t = phi(x).

The normal closure of `L` in `G` is `N = ∪_k t^k L t^{-k}`. It is an increasing union of
copies of `L`, the inclusion of each copy into the next being `phi`, so `N ≅ Gamma_mal`
and `G = Gamma_mal ⋊ Z`, where the generator of `Z` acts by the stage shift.

Facts that need no new proof:

- **(F1) Two generators, one relator.** Eliminating `a = b^{-1} t^{-1} b t b^2` leaves
  `G = <b, t | [b^{-1} t^{-1} b t b^2, t]>`. The relator lies in `[F(b,t), F(b,t)]`, so
  `G^ab = Z^2`.
- **(F2) Infimal cost one.** `N` is infinite and normal, `G/N = Z` is infinite, and `N` has
  infimal cost 2 by `fpbs-mal-odometer-product-actions-have-cost-two`. Gaboriau's
  normal-subgroup theorem (as quoted in `fpbs-normal-subgroup-bounded-cost-fixed-price-one`)
  therefore gives `C(G) = 1`, i.e. infimal cost one.
- **(F3) Zero relative cost in every free action.** In every free p.m.p. `G`-action,
  `relC(R_G; R_L) = 0`, and hence `relC(R_G; R_N) = 0`.
  - The group `<a>` acts freely, hence aperiodically, so it has a complete section `A`
    for its orbits with `μ(A) < ε`.
  - For each `x`, pick `i` with `a^i x ∈ A`. Since `t a^i = a^i t`, we get
    `t x = a^{-i} (t (a^i x))`, so `R_L ∨ t|_A ∋ (x, t x)`.
  - This uses no ergodicity. It is motivation only; the lemma does not need it.

## 1. Lemma: `Z^2 = <a, t>` is malnormal in `G`

**Lemma 1.** For `g ∈ G \ <a, t>`, the intersection `g <a,t> g^{-1} ∩ <a,t>` is trivial.

*Proof.*

1. **Reduce to `L`.** Every element of an ascending HNN extension has the form
   `t^p u t^{-q}` with `u ∈ L` and `p, q ≥ 0`. Since `t ∈ Z^2`, the double coset
   `Z^2 g Z^2` equals `Z^2 u Z^2`. Since `a ∈ Z^2`, we may also strip powers of `a` from
   both ends of the reduced word `u`. So assume `u ∉ <a>` is reduced and begins and ends
   with a letter `b^{±1}`.
2. **An infinite intersection is a twisted double coset equation.** Suppose
   `u a^i t^j u^{-1} = a^k t^l` with `(i, j) ≠ (0, 0)`.
   - The homomorphism `G -> Z` given by the `t`-exponent forces `l = j`.
   - If `j = 0`, then `u a^i u^{-1} = a^k` in `L`, and `k = ±i ≠ 0`. Since `<a>` is a
     maximal cyclic subgroup of the free group `L`, it is malnormal, so `u ∈ <a>`. This is
     a contradiction.
   - If `j > 0`, rearrange to `a^{-k} u a^i = t^j u t^{-j}`. Applying `phi^j`, which is
     conjugation by `t^j`, gives `φ^j(u) = a^{-k'} u a^{-i'}`, i.e.
     `φ^j(u) ∈ <a> u <a>`.
   - The case `j < 0` is the same with `u` and `φ^{|j|}(u)` exchanged.
3. **`b`-length grows strictly.** Write `u = b^{e_1} a^{i_1} b^{e_2} ⋯ a^{i_{s-1}} b^{e_s}`
   with all `e_r` and `i_r` nonzero, where `s ≥ 1`. Then
   - `phi(b^e) = b a (b^{-1} a)^{e-1} b^{-2}` for `e > 0`;
   - `phi(b^{-e}) = b^2 a^{-1} (b a^{-1})^{e-1} b^{-1}` for `e > 0`.

   Each of these words is reduced, starts with `b`, ends with `b^{-1}`, and has `b`-length
   `|e| + 2`. Consecutive images are separated by `a^{i_r}` with `i_r ≠ 0`, so there is
   no cancellation. Hence `phi(u)` is reduced, starts with `b`, ends with `b^{-1}`, and
   `|phi(u)|_b = |u|_b + 2s > |u|_b`. By induction, `|phi^j(u)|_b > |u|_b` for all
   `j ≥ 1`.
4. **Conclude.** Every reduced element of `<a> u <a>` has the form `a^p u a^q`, whose
   `b`-length is `|u|_b`. This contradicts step 3. ∎

**Check.** The script enumerates all reduced `u` of length `≤ 10` that begin and end with
`b^{±1}`, and all `q ≤ 4`. It finds no solution of `phi^q(u) ∈ <a> u <a>`.

**Corollary 2.**
- `G` has trivial centre. A nontrivial central element `z` gives an infinite intersection
  `g Z^2 g^{-1} ∩ Z^2`:
  - if `z ∈ Z^2`, this holds for `g = b ∉ Z^2`, and the intersection contains `<z>`;
  - if `z ∉ Z^2`, this holds for `g = z`.
- The q-normal (Gaboriau chain) closure of any infinite subgroup `H ≤ Z^2` is `Z^2`
  itself. Every `γ` with `γ^{-1} H γ ∩ H` infinite lies in `Z^2`.

## 2. What dies, and where

The class of approaches examined consists of those that decide the price of `Gamma_mal`,
and hence the floor by `fpbs-mal-fixed-price-iff-bernoulli-finite-cost`, through the
overgroup `G`.

- **(K1) Chain and wq-normal criteria for `G` die at step one.** This covers
  `gaboriau-commensurated-chain-citation` (Critère VI.24 (3)) and the wq-normal
  statements `fpbs-wq-normal-price-one-subgroup-forces-price-one` and
  `fpbs-locally-free-wq-normal-fg-subgroup-fixed-price`, started from the obvious
  amenable subgroups `<a>`, `<t>` and `<a, t>`.
  - The commensurator of `<a>` is `Z^2`.
  - `Z^2` is malnormal by Lemma 1, so the chain stalls there. It never reaches `b`.
- **(K2) The twice-used-letter theorem never applies to `G`.**
  `fpbs-one-relator-twice-used-letter-fixed-price` would need a basis of `F(b, t)` in
  which some letter `s` occurs exactly twice in the relator.
  - Since `G^ab = Z^2`, the relator lies in the commutator subgroup in every basis. So
    the two occurrences are `s` and `s^{-1}`, and the relator is `s x^p s^{-1} x^q`
    with `p + q = 0`.
  - Then `x^p` is central and of infinite order, which contradicts Corollary 2.
- **(K3) No transfer to the floor in either direction.**
  - *Floor holds.* Then `C(β_{Gamma_mal}) = ∞`. The restriction of the Bernoulli shift of
    `G` to `N` is a Bernoulli shift of `N`, so it also has infinite cost. This gives no
    lower bound on `C(β_G)`, which lies in `[1, 2]`: a finite graphing of `R_G` need not
    restrict to anything of finite cost on `R_N`, and (F2) and (F3) are consistent with
    `C(β_G) = 1`. So the floor says nothing about `G`, and the price of `G` says nothing
    back.
  - *Floor fails.* Then only the Bernoulli-type actions of `N` are known to have cost 2.
    Getting fixed price one for `G` would need every free `N`-action to have bounded cost.
    That is the hypothesis of the OPEN `fpbs-normal-subgroup-bounded-cost-fixed-price-one`
    and `fpbs-bounded-cost-outer-cyclic-extension-price-one` with `K = 2`. The step that
    fails is exactly the one those claims leave open: Gaboriau's theorem gives infimal
    cost, not fixed price.

**Invariant.** In `G`, the invariant is Lemma 1 (malnormality of `Z^2`, from the strict
growth of `b`-length under `phi`). Across the extension, the invariant is the one-way
nature of normal-subgroup cost transfer.

**Status.** This is a dead approach, not a decision. `fpbs-mal-bernoulli-single-stage-floor`
stays OPEN. Lemma 1 is recorded here as a lemma and is not promoted to a node, because
nothing in the graph currently needs it.
