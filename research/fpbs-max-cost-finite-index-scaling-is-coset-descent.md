---
rg: 2
id: fpbs-max-cost-finite-index-scaling-is-coset-descent
kind: claim
title: Finite-index scaling of maximal cost is cost descent through one Bernoulli-times-coset factor, both fixed price and the Betti target force it, and it forces chain-independent rank gradient
distinct_from:
  fpbs-burnside-explicit-action-pair: that computes the costs of b and b x Z/n only on B(2,n), using the common upper cost; this holds for every infinite finitely generated group and every finite-index subgroup, turns the pair into an equivalence with scaling of C^*, and has the Burnside pair as its calibration case.
  fpbs-compact-extensions-preserve-cost: that asks for cost equality along every relatively compact extension of every free base; this is one explicit q-point extension of the Bernoulli base, shown equivalent to a statement about group invariants C^* alone.
  fpbs-cycle-tails-force-rank-gradient-equals-l2-betti: that needs C(b)=1+beta_1 and pins rank gradients to beta_1; this needs only finite-index scaling of C^*, which is weaker than both fixed price and the Betti target, and pins every Farber rank gradient to C^*-1 and to the infimum over all finite-index subgroups.
  fpbs-finite-index-star-relative-cost: that is the zero relative cost of finite-index subrelations; this uses it for the lower bound C^*(Gamma) <= C^*(H).
artifacts:
  - research/artifacts/fpbs-max-cost-finite-index-scaling-2026-09-17.md
---

**ESTABLISHED** through `fpbs-max-cost-finite-index-scaling-is-coset-descent-proof`.

**Setting.** `Gamma` is an infinite finitely generated group and `H <= Gamma`
has index `q`. `b_Gamma` is a nontrivial Bernoulli shift, and `C^*` is the
maximal cost of free actions. `Y = b_Gamma x Gamma/H` is the diagonal action,
with uniform measure on the cosets.

1. **Scaling identity.** `C^*(H) - 1 = q (C(Y) - 1)`, and
   `C^*(Gamma) <= C^*(H) <= 1 + q (C^*(Gamma) - 1)`.
2. **Equivalence.** The following are equivalent:
   - (i) `C^*(H) - 1 = q (C^*(Gamma) - 1)`;
   - (ii) `C(Y) = C(b_Gamma)`;
   - (iii) `C(Y) >= C(b_Gamma)`.
3. **Necessity.** Write VS(Gamma) for "(i) holds for every finite-index `H`".
   - If `Gamma` has fixed price, VS(Gamma) holds.
   - If `C(b_G) = 1 + beta_1(G)` for `G = Gamma` and for all its
     finite-index subgroups, VS(Gamma) holds.
   - So VS for all infinite f.g. groups is a prerequisite of
     `fpbs-fixed-price-universal` (f.g. case) and of the universal cycle-tail
     target `fpbs-bernoulli-cycle-tail-compactness`.
   - VS can fail on its own. It mentions only `C^*` of `Gamma` and of its
     finite-index subgroups.
4. **Rank gradients.** Suppose VS(Gamma) holds and `Gamma` is residually
   finite. Then every Farber chain has
   `RG = C^*(Gamma) - 1 = rho(Gamma)`, where
   `rho(Gamma) = inf over finite-index H of (d(H) - 1)/[Gamma:H]`.
   - So rank gradient is chain-independent.
   - A group with two Farber chains of different rank gradient, or one chain
     with `RG > rho`, refutes VS. That refutes both routes to the full
     statement.
5. **Calibration.** For `B(2,n)` with large odd `n`, VS is equivalent to
   fixed price one. So VS for all f.g. groups contains the open hole
   `fpbs-burnside-upper-cost-one`.

Proofs are in the artifact:

| Part | Where |
| --- | --- |
| 1, 2 | Sections 1–4 |
| 3 | Section 5 |
| 4 | Corollary 6.1 |
| 5 | Section 7 |

Section 8 records, as an uncited pointer, why weak-containment monotonicity
cannot give (iii). Section 9 records the open measure-equivalence form.
