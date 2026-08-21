---
rg: 2
id: cyclic-conjugacy-does-not-synchronize-swap-sources
kind: claim
title: Cyclic conjugacy of partial-isometry swaps does not synchronize their sources
distinct_from:
  pairwise-cross-grams-do-not-supply-one-game-state: that uses edge-indexed overlap states on pair blocks; this gives an exact stationary model even when every entire swap cell is transported coherently around one finite cycle.
  even-partial-swap-star-has-canonical-trace-floor: that obtains a trace floor after all swaps literally share one source; this proves that a transitive cycle of isomorphic sources does not supply that hypothesis.
  matrix-only-cyclic-carrier-invariance: that asks for a finite-dimensional-only invariance estimate for one carrier; this is an exact finite-dimensional stationary obstruction to deriving such invariance from cyclic transport alone.
---

No finite cycle, expander incidence graph, or transitive permutation action
aligns source projections merely by transporting the corresponding swap
cells.

Fix `m>=2` and a nonzero finite-dimensional space `K`.  Put

```text
H=directSum_(v in Z/m) K_v,
Q_v=projection onto K_v.                              (CCS1)
```

Let `U` cyclically permute the summands, so

```text
UQ_vU^*=Q_(v+1).                                      (CCS2)
```

Take `S_v=Q_v`, viewed as a partial isometry with initial and range
projection `Q_v`, and form `J_(S_v)` in `M_2(B(H))`.  Then, exactly,

```text
diag(U,U) J_(S_v) diag(U,U)^*=J_(S_(v+1)).            (CCS3)
```

The cycle closes after `m` steps, every local partial-isometry and swap
identity is exact, and all source projections are mutually orthogonal:

```text
Q_vQ_w=0       (v!=w),
tau(Q_v)=1/m.                                          (CCS4)
```

Common amplification preserves every identity and normalized trace in
`(CCS2)--(CCS4)`.  The same construction works on any finite vertex-
transitive graph by using its permutation representation and one coordinate
projection.  Spectral expansion of the incidence graph is irrelevant:
the labels and carriers covary, so every transport edge has zero defect.

Therefore a cyclic self-verifier made only of conjugate swap cells has an
exact stationary/rectangular escape.  To invoke the common-source game
lemma or the even-star trace floor, the presentation must additionally do
one of the following:

1. expose one literal source projection used by every swap;
2. compare the transported sources after pulling them into one fixed
   coordinate chart; or
3. impose a mixed moment which detects that the cycle holonomy moves the
   source.

Adding more transport edges without one of these common-coordinate tests
does not spread normalized-HS error.

## Attempts

- **Replace the cycle by an expander.**  The permutation representation on
  vertices still satisfies every transport edge exactly, so expansion does
  not see a covarying carrier.
- **Add canonical trace tests for the individual sources.**  Those tests
  control ranks, not coordinates; equal-rank coordinate projections remain
  permutable.
- **Use a literal source equalizer.**  This defeats the countermodel, but it
  is precisely the extra common-coordinate syntax which the bare transport
  architecture lacks.
