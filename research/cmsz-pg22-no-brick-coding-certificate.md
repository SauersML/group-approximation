---
rg: 2
id: cmsz-pg22-no-brick-coding-certificate
kind: route
title: Verify the rigidity hypotheses exactly, then refute the forced dimension-two uniform instance with two SAT solvers
target: cmsz-pg22-rs-two-graphs-admit-no-brick-coding
requires:
  - two-graph-brick-codings-are-rigid-under-rank-two-h1
artifacts:
  - research/artifacts/nv-brick-codings-of-two-graphs-2026-09-17.md
  - experiments/nv-brick-coding-2026-09-17/certificate.py
  - experiments/nv-brick-coding-2026-09-17/certificate_uniform.py
  - experiments/nv-brick-coding-2026-09-17/certificate_uniform.log
  - experiments/nv-brick-coding-2026-09-17/brick_sat.py
  - experiments/nv-brick-coding-2026-09-17/certificate.log
  - experiments/nv-brick-coding-2026-09-17/control_product.py
  - experiments/nv-brick-coding-2026-09-17/control_product.log
---

Details: Part C of the artifact. Run `python3 certificate_uniform.py` in
`experiments/nv-brick-coding-2026-09-17/`, which writes `certificate_uniform.log`.

1. **Hypotheses (R1)–(R3), exact checks per T** (`certificate.main(solve_sat=False)`):
   - (A1)–(A3) hold, and the square map is a bijection with unique filling.
   - All row sums of `M_1` and `M_2` are 4, and both are primitive. Some power is
     positive: exponents 5,5 (T2: 4,4).
   - The coboundary `C^1 -> C^2` has rank 293 over `GF(1000003)`, so
     `h^1 ≤ 336 - 293 - 41 = 2`. The mod-`p` rank is a lower bound for the rank over `Q`, so
     `dim H^1(K;Q) ≤ 2`, and the independent classes `[d_1]`, `[d_2]` give `≥ 2`.
   - The transport relations `e ~ e'` and `f ~ f'` each have one class (union–find).
2. **Rigidity.** By `two-graph-brick-codings-are-rigid-under-rank-two-h1`, (c) with
   `α = β = 2`, every brick coding has `m ≤ 2` and total code length 2 on every edge.
   Padding a dimension-1 coding by an empty coordinate preserves (B1) and (B2). So it
   suffices that no dimension-2 map with total length 2 satisfies (B1) and (B2).
3. **SAT.** `brick_sat.solve(T, 2, uniform=True)` encodes exactly that. Its ingredients:
   - one-hot code variables over the 12 codes of total length 2;
   - per vertex and colour, a disjunction over the ordered 4-brick partitions of `C^2`
     into such bricks (all 7 are enumerated);
   - per square, product variables implied by both factorizations, with at most one
     true.

   Any coding gives a model, so UNSAT means no coding. For each of T0..T4 both
   CaDiCaL 1.5.3 and Glucose 4 (PySAT) return UNSAT.
4. **Cross-checks** (not needed for the proof):
   - The full-domain dimension-2 instance needs no rigidity input: it uses all 49 codes
     of total length `≤ 3`, which are all bricks of volume `≥ 1/8`, together with all 39
     four-brick partitions. It is UNSAT for T0 (both solvers) and for T1 (CaDiCaL), in
     `certificate.log`.
   - Controls: the product 2-graph `B_4×B_4` is SAT and recovers the expected coding.

**Trust base.** Python and PySAT solver runs with no DRAT proof log, mitigated by two
independent solvers per instance, the agreement of the full-domain runs, and the SAT
control.
