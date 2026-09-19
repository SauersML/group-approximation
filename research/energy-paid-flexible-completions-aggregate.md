---
rg: 2
id: energy-paid-flexible-completions-aggregate
kind: claim
title: Energy-paid flexible completions aggregate across arbitrary moving faces
distinct_from:
  positive-fixed-corner-cubic-energy-charges-deleted-rank: that constructs and charges the missing boundary for one authenticated positive compression; this proves that any collection of such individually charged completions can be summed without losing the normalized-HS scale.
  dyadic-face-repair-needs-cost-tail-tightness: that permits face-dependent repair constants with an uncontrolled tail; this assumes one uniform energy-to-cost constant and proves that neither moving levels nor heterogeneous direct sums create a new obstruction under that hypothesis.
  active-residuals-do-not-name-passive-endpoint: that shows common residual data cannot choose between two passive endpoint types; this observes that adaptive choice of either exact passive endpoint has zero cost, so such ambiguity cannot obstruct flexible repair.
---

Fix a finite presentation with generator set `S`.  For each `j`, let `U_j`
be a unitary tuple on `H_j`, put `d_j=dim(H_j)`, and let `e_j` be its
**unnormalized squared** presentation energy.  Suppose there is an exact
tuple `V_j` on `H_j (+) K_j`, with `k_j=dim(K_j)`, such that, after one
isometric identification of `H_j` with the old carrier,

```text
k_j + sum_(s in S) ||P_j V_j(s)P_j-U_j(s)||_F^2
    + sum_(s in S) ||(1-P_j)V_j(s)P_j||_F^2
 <= C e_j.                                             (EFA1)
```

Here `C` is independent of `j`; the levels, dimensions, and exact endpoint
types may all vary.  Then every finite block sum

```text
U= (+)_j U_j,             D=sum_j d_j,
E=sum_j e_j                                                   (EFA2)
```

has an exact flexible completion `V=(+)_j V_j` satisfying

```text
K=sum_j k_j <= C E,
(1/(D+K)) sum_(s in S) ||V(s)-(U(s)(+)1_K)||_F^2
 <= C_S E/D.                                             (EFA3)
```

The harmless choice of comparison tuple on the new carrier changes `C_S`
by at most a presentation-dependent constant.  In particular, if
`E/D -> 0`, then `K/D ->0` and the generalized flexible distance to the
exact representation variety tends to zero.

This is simply additivity, but it closes an important quantifier hole.
Frobenius squares and leakage squares add on orthogonal blocks, as do the
padding ranks.  Summing `(EFA1)` gives `K<=CE` and total squared generator
cost at most `CE`; division by `D+K>=D` proves `(EFA3)`.  Thus distributing
mass among an unbounded number of congruence levels cannot turn uniformly
energy-paid local completions into a soft delocalized enemy.

## Consequences for the named candidates

1. **Compressed Weil/fixed-line packets.**  Whenever the deleted boundary
   is the positive fixed corner of
   `positive-fixed-corner-cubic-energy-charges-deleted-rank`, `(PFC3)` pays
   its rank by cubic Frobenius energy and the original exact dilation gives
   `(EFA1)`.  Hence arbitrary heterogeneous block sums of those packets are
   flexibly repairable.  Repeating or spreading the one-line defect over
   moving primes cannot produce positive flexible distance.

2. **Cuspidal redistribution.**  Every redistributed passive block in
   `cuspidal-redistribution-refutes-regular-core-orbit-basin` is already an
   exact endpoint, so it satisfies `(EFA1)` with zero cost.  Adding any
   energy-paid active family remains flexibly repairable by the direct-sum
   construction.  The large separation from the *regular* endpoint orbit
   is therefore only a failure of nonadaptive type selection.

3. **The explicit metacyclic substitution.**  In
   `metacyclic-cross-stratum-energy-is-inverse-dimensional`, the original
   regular endpoint is a same-space exact comparator.  Its squared movement
   is `alpha_m/D_m`, while the first cubic energy is `3 alpha_m/D_m`.
   Consequently arbitrary block sums of these isolated substitutions obey
   `(EFA3)` with no padding.  Any metacyclic counterexample must use coupled
   substitutions whose endpoint residuals interact across the regular
   coset branches; it cannot be a diffuse sum of the known one-packet cell.

4. **Long return phases.**  The monodromy reset of
   `bs14-long-packet-monodromy-reset-creates-fixed-sources` is not itself an
   exact endpoint completion, so it is not an application of `(EFA1)`.
   It nevertheless gives a precise reduction: on all packets of length at
   least `M`, the exact BS core moves by at most `pi/M`, independently of
   the number of packets.  A positive-distance enemy therefore survives
   after first resetting every long monodromy to one; the free return phase
   alone cannot carry its positive distance.  What remains could still be
   cross-packet coupling of the two cubic rows.

5. **Rational `H^2` packets.**  The standard relative index has density
   `O(epsilon)` by
   `relative-h2-does-not-supply-passive-hs-obstruction`, and hence is
   compatible with discarding `o(D)` dimensions.  More fundamentally, the
   available Dadarlat packets have exact torsion rows, not the exact
   BS-plus-inversion core required here.  They therefore do not give a
   counterexample; a new exact-on-the-core relative construction with a
   positive-density invariant would be needed.

## Exact surviving scope

This theorem does **not** prove the moving-face repair target.  Its premise
already assigns each block to an authenticated native endpoint face and
supplies its efficient completion.  An arbitrary exact BS core and raw
involution need not preserve such a block decomposition.  Thus the only
surviving soft enemy has to mix distinct moving congruence atoms through
the endpoint involution before those atoms can be selected, or exhibit a
single native face whose efficient completion constant diverges.  Neither
heterogeneous direct sums, passive cuspidal ambiguity, isolated metacyclic
substitutions, free long monodromy, nor the presently available rational
two-homology class realizes that enemy.
