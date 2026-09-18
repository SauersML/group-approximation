---
rg: 2
id: fpbs-hole-at-s-is-s-price-plus-invariant-cayley-cost
kind: claim
title: Cayley subgraphing cost at a fixed generating set is antitone under weak containment, so the Morse-deficit hole at S is S-fixed price plus invariant Cayley cost 1+beta_1
distinct_from:
  fpbs-cost-is-limit-of-cayley-subgraphing-costs: that proves inf_S C_sub(S) = C(a) and splits the hole at S into Target plus (Q3)(S), both at the Bernoulli end; this proves weak-containment antitonicity of C_sub(S) at one fixed S, and splits the hole into a price statement between the two weak-containment extremes plus an invariant-percolation statement.
  fpbs-morse-deficit-vanishes-for-full-presentations: that is the open hole; this is an unconditional equivalence reformulating it, and it leaves the hole OPEN.
  fpbs-invariant-cayley-cost-literature-status: that imports the literature status of the invariant Cayley cost; this uses it to locate the Kazhdan case of the hole entirely in S-fixed price.
  cost-is-constant-on-weak-equivalence-classes: that is monotonicity of cost under weak containment, whose proof backs up with arbitrary group elements; here the backup edges are generator edges, so the fixed-S subgraphing cost is itself monotone.
artifacts:
  - research/artifacts/fpbs-fixed-s-price-split-2026-09-17.md
---

**ESTABLISHED (written deduction; see route `fpbs-hole-at-s-is-s-price-plus-invariant-cayley-cost-proof`).**

**Setting.**
- `Gamma` is infinite with finite symmetric generating set `S`.
- `C_sub^a(S)` is the Cayley subgraphing cost of a free action `a`, as in
  `fpbs-cost-is-limit-of-cayley-subgraphing-costs`.
- `c_inv(S)` is the invariant cost of `Cay(Gamma, S)`.
- `a_inf` is the Burton–Kechris maximum for weak containment, `b` is the Bernoulli shift, and
  `beta_1 = beta_1^(2)(Gamma)`.

**Theorem.**
- **(H1)** If `a ≼ a'` are free, then `C_sub^(a')(S) <= C_sub^a(S)`. Hence
  `C_sub^(a_inf)(S) <= C_sub^a(S) <= C_sub^b(S)` for every free `a`.
- **(H2)** `c_inv(S) = inf_a C_sub^a(S) = C_sub^(a_inf)(S)`.
- **(H3)** The following are equivalent:
  - `lim_L m_S(P_L) = 0` (the hole at `S`);
  - `C_sub^b(S) = 1 + beta_1`;
  - (P1) and (P2), where (P1) is `S`-fixed price (`C_sub^a(S)` is independent of the free action `a`), and (P2) is
    `c_inv(S) = 1 + beta_1`.

  Each of these implies `c_inv(S) = cost(Gamma) = C(b) = 1 + beta_1`. At `Cay(Gamma, S)` that is a positive answer to
  the Beringer–Pete–Timár question.
- **(H4)** If `Gamma` is Kazhdan or amenable, then (P2) holds at every `S`. So for Kazhdan `Gamma` the hole at `S` is
  exactly `S`-fixed price, `C_sub^b(S) = 1`.

**Reading.**
- The hole is a fixed-generating-set price problem. (P2) is purely invariant, and a failure of it would answer an open
  literature question and refute the hole at that `S` independently of cost–Betti.
- (P1) is the gap between the two weak-containment extremes of one upper-semicontinuous-type functional.
- Every free action does at least as well at `S` as Bernoulli, so a counterexample can only live at the factor-of-iid
  end.
- The artifact, Section 5, records the dead ends:
  - percolation-cluster certificates, not necessary: `F_2` at `{a, b, ab}`;
  - hyperfinite coarsening, killed by the spectral gap;
  - stepwise Hutchcroft–Pete transfer, already dead.
