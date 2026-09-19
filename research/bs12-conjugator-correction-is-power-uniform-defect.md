---
rg: 2
id: bs12-conjugator-correction-is-power-uniform-defect
kind: claim
title: Fixed-base BS(1,2) conjugator correction is the power-uniform defect, so glued-cycle collapse is power-uniform Higman collapse
artifacts:
  - research/bs12-conjugator-correction-is-power-uniform-defect-proof.md
  - experiments/higman-power-uniform-2026-09-17/verify_power_uniform_averaging.py
  - experiments/higman-power-uniform-2026-09-17/run_trials40_seed1.txt
distinct_from:
  bs12-trivially-padded-opnorm-correction: that is the open padded correction in which the base B may move; this computes, with no spectral hypothesis and constants 1/2 and 2, how far a conjugator is from exact when the base is held fixed.
  higman-seam-gate-needs-only-padded-bs-correction: that proves (TPC)+(CGC) => (HMF5) with (TPC) possibly stronger than needed; this proves (HMF5) <=> (PUU)+(CGC) with both prerequisites necessary, and rewrites (CGC) without exact packets.
  higman-exact-packet-cycles-collapse-opnorm: that is the open glued-cycle collapse; this proves it equivalent to a statement about four unitaries alone, and does not decide it.
  higman-opnorm-collapse-is-a-one-unitary-z4-problem: that reduces the ordinary relator profile to one unitary over an order-four symmetry; this changes the relator norm (supremum over all powers) instead of the number of unknowns.
  three-higman-bs-seams-vanish-fourth-is-product-holonomy: that classifies exact packets and scalarizes the fourth seam in normalized HS; this is an operator-norm averaging estimate valid for every base unitary.
---

**ESTABLISHED** by `bs12-conjugator-correction-is-power-uniform-defect-proof`
(elementary; not Lean-verified).  All norms are operator norms, and all
unitaries are finite-dimensional.

For unitaries `A,B` in `U(N)` put

```text
Delta(A,B) = sup_(k in Z) || A B^k A^* - B^(2k) ||,
I(B)       = { C in U(N) : C B C^* = B^2 }.                         (PU0)
```

`Delta(A,B)` is at least the ordinary `BS(1,2)` defect `||A B A^* - B^2||`
(the case `k=1`), and it is `0` exactly when `A` is in `I(B)`.

1. **Two-sided fixed-base estimate.**  For all `A,B`,

   ```text
   dist(A, I(B)) >= Delta(A,B)/2.                                   (PU1a)
   ```

   If `Delta(A,B) < 1`, then `I(B)` is nonempty and

   ```text
   dist(A, I(B)) <= 2 Delta(A,B).                                   (PU1b)
   ```

   A witness is the polar part of the Haar average
   `X = int_G g^2 A g^(-1) dg` over the compact group `G`, the closure of the
   powers of `B`.  No separation, orbit-length, or multiplicity hypothesis
   on `spec B` is used.

2. **Glued-cycle collapse without exact packets.**  Let `(PUC)` be:
   for every `epsilon>0` there is `kappa>0` such that for all `M` and all
   `U_0,...,U_3` in `U(M)`,

   ```text
   max_(i in Z/4) Delta(U_i, U_(i+1)) <= kappa  =>  max_i ||U_i-1|| <= epsilon.   (PUC)
   ```

   Then `(PUC)` is equivalent to `(CGC)` of
   `higman-exact-packet-cycles-collapse-opnorm`, with explicit constants:
   `kappa_PUC(epsilon) = min(eta_CGC(epsilon/2), epsilon/2, 1/2)/2` and
   `eta_CGC(epsilon) = min(kappa_PUC(epsilon/2)/2, epsilon/2)`.  So `(CGC)` is
   the marked Higman collapse `(HMF5)`, with the relator defect replaced by
   its supremum over all powers of the conjugated generator.

3. **Necessary-and-sufficient decomposition of `(HMF5)`.**  Let `(PUU)` be
   `higman-tuples-are-near-power-uniform-tuples`: for every `epsilon>0` there
   is `delta>0` such that every tuple `U` in `U(N)^4` with Higman relator
   defect at most `delta` has some `k>=0` and a tuple `V` in `U(N+k)^4` with

   ```text
   ||V_i - (U_i (+) 1_k)|| <= epsilon,   max_i Delta(V_i,V_(i+1)) <= epsilon.   (PUU)
   ```

   Then:

   - (a) `(HMF5) => (PUU)`, with witness `V_i = 1`;
   - (b) `(TPC) => (PUU)`, where `(TPC)` is
     `bs12-trivially-padded-opnorm-correction`;
   - (c) `(PUU)` and `(CGC)` together imply `(HMF5)`;
   - (d) `(HMF5) => (CGC)` (item 2 of
     `higman-seam-gate-needs-only-padded-bs-correction`).

   Hence

   ```text
   (HMF5)  <=>  (PUU) and (CGC)  <=>  (PUU) and (PUC).
   ```

   Unlike `(TPC)`, each prerequisite is **necessary** for `(HMF5)`.  If
   `(TPC)` fails, for instance because a sharp fixed-base counterexample
   refutes the same-dimension case and padding does not help, the packet
   route survives through `(PUU)`.

4. **The power-uniform norm is not the relator norm.**  Let `o` be odd, let
   `B e_x = w^x e_x` on `C^(Z/o)` with `w = exp(2 pi i/o)`, and let
   `A e_x = e_(x/2 + 1)` (halving mod `o`, then a unit shift).  Then
   `A B A^* = w^(-2) B^2`, so the relator defect is `2 sin(2 pi/o) -> 0`.
   But `Delta(A,B) = 2 cos(pi/(2o))`, so by `(PU1a)` every exact conjugator of
   the base `B` lies at distance at least `cos(pi/(2o)) >= sqrt(3)/2` from
   `A`.  This twisted pair is exactly correctable once `B` may move (the
   conjugator-half attempt on `bs12-trivially-padded-opnorm-correction`).
   So the whole fixed-base obstruction is measured by `Delta`, and nothing
   else.

## Evidence (numerical, not part of the proof)

`verify_power_uniform_averaging.py` builds random exact packets in normal form
(odd orders `3..31`, random monodromies and kernel blocks, random basis),
perturbs the conjugator, and forms the average and its polar part.  In all
`40` trials of `run_trials40_seed1.txt`, the polar part is exact to `1e-14`,
satisfies `(PU1b)` with worst ratio `||C-A||/Delta = 0.695`, and the original
exact conjugator satisfies `(PU1a)`.  The script also evaluates item 4 at
`o = 27, 81, 243`: relator defects `0.461, 0.155, 0.052` against
`Delta = 1.997, 2.000, 2.000`.

## What this does not do

It does not prove `(CGC)`, `(PUU)` or `(HMF5)`.  It moves the open content
into two statements, each about Higman tuples only, and it shows that
same-dimension or padded `BS(1,2)` stability is only one sufficient way to
feed the first of them.
