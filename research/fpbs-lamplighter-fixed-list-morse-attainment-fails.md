---
rg: 2
id: fpbs-lamplighter-fixed-list-morse-attainment-fails
kind: claim
title: For the lamplighter group every finite relator list has Morse deficit at least 2^-(K+1), although the Bernoulli cost equals subgraphing cost equals one
artifacts:
  - research/artifacts/fpbs/docs/morse-l2-inequality-and-lamplighter-gap.md
  - experiments/fpbs-morse-l2-gap-2026-09-17/lamplighter_coset_cancellation.py
distinct_from:
  fpbs-morse-deficit-vanishes-for-full-presentations: that is the open limit assertion over growing lists, which this example satisfies; this shows that no single finite list attains it, so fixed-list attainment (Q1) and depth compactness (Q2) are strictly stronger than the premise
  fpbs-morse-mass-bounded-by-relator-boundary-rank: that proves the l2 mass bound for any group; this computes a positive relation gap for every finite list of one non-finitely-presented group
  fpbs-bernoulli-morse-collapse-criterion: that lists (Q1)–(Q3) and proves Target, (Q2) and (Q3) together imply (Q1); this separates them, with Target and (Q3) true and (Q1), (Q2) false
---

**PROPOSED ESTABLISHED.** A written deduction; see the route
`fpbs-lamplighter-fixed-list-morse-attainment-fails-proof`.

**Statement (Theorem D).** Let `Gamma = Z/2 wr Z = <a, t>`, `S = {a, t}`, and `b` its Bernoulli shift. For
`K >= 1` let `R_K = {a^2, [a, t^k a t^-k] : 1 <= k <= K}`. Every trivial word lies in some `N_(R_K)`. For a finite
list `R` of trivial words, let `K(R)` be the least `K` with `R ⊆ N_(R_K)`. Then

```text
m(R) >= gap(R) >= 2^-(K(R)+1) > 0,
```

while `C_sub(S) = C(b) = 1 = 1 + beta_1^(2)(Gamma)` and `lim_L m(P_L) = 0`.

**Separation.** In the notation of Section 5 of `bernoulli-morse-collapse-criterion.md`, Target and (Q3) hold for
this group, and (Q1) and (Q2) fail.

**Obstruction extracted.** Fixed-list Morse attainment is not a universal route to
`fpbs-bernoulli-cycle-tail-compactness`. The failing step is the mass bound `mu(M) <= rho(R)` of
`fpbs-morse-mass-bounded-by-relator-boundary-rank`, and the invariant is the relation gap `gap(R)`. Any group whose
gap is positive for every finite list is out of reach of (Q1), even when the cost–Betti equality holds.

**Proof idea.** Collapse the `a`-edges and quotient `t`-edges by right `B`-cosets, `B = <a_1, ..., a_K>`. This maps
the Cayley 1-cycles onto the 1-cycles of the Bass–Serre-type graph with vertex stabilizer `A = <a_0, ..., a_K>` and
edge stabilizer `B`, whose cycle module has dimension `1/|B| - 1/|A| = 2^-(K+1)`. The relators in `R_K` cancel in the
quotient, and a bounded right inverse is built from hypercube paths `t^k a t^-k` inside `A`-cosets. `C_sub(S) = 1`
comes from a nested Borel spanning forest over a hyperfinite exhaustion.

## Attempts

(none)
