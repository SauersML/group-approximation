---
rg: 2
id: atlas-fractional-pauli-return-network
kind: claim
title: The atlas Pauli sector carries a finite weighted return network with reproduction number above one
artifacts:
  - notes/TRUE_PAULI_BRANCH_TRANSFER_PACKET.md
  - notes/TRUE_RAW_PAULI_COEFFICIENT_CUT.md
  - research/artifacts/fractional-branch-pressure-2026-08-19.md
distinct_from:
  atlas-pauli-range-packing-recurrence: that requires every edge's source to be exactly a state projection, i.e. an approximate range containment; this only requires a measured coverage fraction per edge and accepts an edge that captures any positive fraction of its state.
  atlas-pauli-branch-recurrence-automaton: that is the same whole-source requirement stated in leakage and Gram norms, and needs only strong connectivity because its matrix is integer; this needs no strong connectivity and instead needs the rational reproduction number to exceed one.
  atlas-supercritical-pauli-branching-cycle: that asks for an integer branch incidence matrix with a supercritical strongly connected component; this asks for a rational coverage matrix and its supercriticality is a numerical property of measured block moments.
  atlas-pauli-aggregate-range-recurrence: that packages all incoming branches at a state into one aggregate almost-projection and still demands whole sources; this keeps branches separate and lets each cover a fraction.
  atlas-one-cut-finite-multiplicity-extraction: that forces one transported carrier back under one smaller cut; this permits many partial returns through many sectors and only scores their total.
---

For the fixed finite atlas presentation underlying the regular-`A_8` chart,
construct a finite list of state projections `P_1,...,P_m` containing the exact
Pauli cell `E,R_0,R_1` of `pauli-two-child-transfer-packet`, a finite menu of
branch words `w_e : i -> j`, and a threshold `t in (0,1)`, all fixed
independently of matrix dimension, with the following property.

In every sufficiently accurate trace-preserving atlas microstate of relator
defect `delta`, write

```text
m_e = ||P_j w_e P_i||_2^2,
g_(ef) = ||(P_j w_e P_i)^* (P_j w_f P_k)||_2^2,
c_e = [ (m_e/tau(P_i) - t^2)/(1 - t^2) ]_+,
B_(ji) = sum_(e: i->j) c_e.
```

Require:

1. the two exact Pauli edges `E -> R_0`, `E -> R_1` are in the menu with
   coverage `c=1`;
2. there are a fixed positive rational vector `y` and a fixed rational
   `kappa>0`, independent of `delta`, with

   ```text
   B^T y >= (1 + kappa) y;
   ```

3. the total error is a fixed power of the defect,

   ```text
   sum_j y_j ( 2 l_j + o_j ) <= C delta^c,
   ```

   where `l_j` and `o_j` are the leakage and ordered-pair Gram sums of the
   thresholded branches supplied by `soft-block-mass-yields-fractional-branch`
   (so `l_j = 0` identically and `o_j <= t^(-4) sum g_(ef)`);
4. the canonical regular-character constraints keep the weighted carrier mass
   bounded below, `sum_j y_j tau(P_j) >= c_0 > 0`.

By `fractional-source-branch-pressure` this is a contradiction with
`delta -> 0`, so no such microstate sequence exists.

## What changed relative to the earlier branch targets

The earlier targets ask for a *word* whose range lands inside the next state.
This asks for a *number*: the reproduction number of a weighted network.  Two
consequences.

- Nothing has to return completely.  In the two-child case the entire
  requirement is `q_0 + q_1 > 1` by `(FSB4)`.
- The scoring quantities `m_e` and `g_(ef)` are ordinary block moments, so the
  existing trace-word and four-holonomy backends can compute them directly, and
  the search becomes a sweep over `(state family, word menu, threshold)` rather
  than a hunt for an exact containment.

## Attempts

- **Threshold sweep on the known table.**  Score every candidate word at
  several thresholds `t`, convert `m_e` into `c_e`, build `B(t)`, and search for
  a rational `(y,kappa)`.  This is the same certificate format the existing
  `experiments/branching_pf_certificate.py` already verifies exactly with
  `fractions.Fraction`; only the matrix becomes rational.
- **Read the dual on failure.**  If every network stays at reproduction number
  at most one, the dual of the search is a capacity cut that absorbs the
  missing mass.  Adding that cut as a new state is the next iteration, so a
  failed search still returns information.  No such dual has been extracted
  yet.
- **Character cuts are provably not enough.**  `(NCC3)` of
  `supercritical-network-needs-noncanonical-cuts` computes that the raw/comb
  Fourier-flat character cuts give total coverage at most `1/2` at every
  threshold at which they give any, and at most `1` unconditionally for
  `t >= 1/sqrt(2)`.  So the state family must refine them; the natural
  refinement is by finite multiplicity, as in
  `atlas-one-cut-finite-multiplicity-extraction`.
- **Falsification gate, mandatory.**  `(NCC1)` of
  `supercritical-network-needs-noncanonical-cuts` proves that a network whose
  states, words and thresholds are all canonical cannot be supercritical, since
  the exact model would then have zero carrier mass on the component.  Every
  candidate must therefore be checked to consume genuinely non-canonical
  finite-multiplicity or coordinate data, and a candidate that does not is
  wrong regardless of what the numerics say.
- **Where the factor is missing.**  A single soft return step through the known
  flat table gives coverage of order `1/8`; `(FSB4)` needs the two returns to
  total above `1`.  The gap is therefore roughly a factor of four per child,
  and closing it means exhibiting spikiness of the return blocks, not better
  bookkeeping.  This is the productive branch of
  `pauli-block-tail-or-flat-rigidity-dichotomy`.
