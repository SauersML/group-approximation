---
rg: 2
id: hs-invisible-corona-maps-are-full-trace-paddings
kind: claim
title: A Hilbert--Schmidt invisible corona map is a full-trace trivial summand plus a trace-null remainder
distinct_from:
  hs-invisibility-inflation-no-go: that pads a faithful corona map with identity blocks to make every element HS-invisible; this is the converse, that every HS-invisible corona map is such a padding, through an exactly invariant projection of full trace.
  corona-hs-radical-is-finite-residual: that computes the HS-invisible set of one specific group; this describes every HS-invisible corona map of any countable group.
  op-to-hs-shadow-residual-functoriality: that defines the shadow residual and proves its functoriality; this characterizes when the shadow residual is the whole group, as iterated padding.
artifacts:
  - research/artifacts/solve-mf-hyperlinear-quotient-2026-09-13.md
---

**Statement.** Let `G` be countable and let `rho : G -> U(Q_d)` be a
homomorphism into the matrix corona
`Q_d = prod_n M_(d_n) / directSum_n M_(d_n)`, with ultralimit traces
`tau_omega` along free ultrafilters `omega`. The following are equivalent.

- **(a)** `tau_omega(rho(g)) = 1` for every `g in G` and every `omega`.
  Equivalently, `||U_n(g) - 1||_(2,tr) -> 0` for unitary lifts `U_n(g)`.
- **(b)** There is a projection `p in Q_d` with `rho(g) p = p` for every `g`
  and `tau_omega(1 - p) = 0` for every `omega`.

Moreover, in (b):

1. `p` commutes with `rho(G)`, and `rho(g) = p + (1-p) rho(g) (1-p)`;
2. a projection lift `q_n` of `1 - p` has ranks `s_n` with `s_n/d_n -> 0`.
   On `J = {n : s_n >= 1}`, the remainder `rho' = (1-p) rho (1-p)` is a
   homomorphism into the unitary group of the corona
   `(1-p) Q_d (1-p) ~= prod_(n in J) M_(s_n) / directSum_(n in J) M_(s_n)`,
   and `ker rho' = ker rho`.

**Consequences for the shadow residual.** Write `R_(infinity->2)(G)` for the
subgroup killed in normalized HS norm by every operator-norm asymptotic
representation.

3. `R_(infinity->2)(G) = G` iff every corona homomorphism of `G` is a
   full-trace padding of a trace-null remainder. The remainder is again a
   corona homomorphism of `G`, so under `R_(infinity->2)(G) = G` it is again
   such a padding in its own normalized trace.
4. If `R_(infinity->2)(G) = G`, then `G` has no nontrivial finite-dimensional
   unitary representation. In every corona homomorphism, for every `g`,
   every `c > 0` and every `C`, the set

   ```text
   { n : ||U_n(g) - 1|| >= c  and  s_n <= C }
   ```

   is finite: remainders have unbounded rank wherever an element stays
   visible in operator norm.

**Scope.** Rank counting alone gives no contradiction with
`R_(infinity->2)(G) = G`. Iterating part 3 gives remainders with ranks
`s'_n = o(s_n)`, but nothing forces a minimal remainder, so a proof has to
bring in group input, as part 4 and `gapped-normal-generators-give-a-hyperlinear-quotient`
do. No novelty is claimed.
