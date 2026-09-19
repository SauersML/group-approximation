---
rg: 2
id: global-marked-type-cycle-selector-decoder
kind: claim
title: A global permutation of marked types turns cyclic selector rows into one matrix-only BCS energy bound
distinct_from:
  cyclic-coarse-fine-selector-rows-spread-carrier-error: that proves the trace inequality on one already decoded carrier cycle; this packs cycles over an exhaustive finite isotypic decomposition and charges all of their compressed rows to one ordinary word menu
  exhaustive-marked-type-energy-summation: that sums independent typewise predicate estimates after they have been proved; this gives a concrete sufficient form of those estimates using a global permutation holonomy and coarse-to-fine cyclic pressure
  matrix-only-cyclic-carrier-invariance: that audits why bounded ordinary product words do not authenticate selector rows; this keeps the rows analytic and type-compressed, and states exactly which finite-matrix decoder estimate would suffice
  algebraic-exhaustive-marked-type-detectors-violate-induction: that rules out multiplicity-insensitive operator inequalities on every representation; this criterion is required only after finite-dimensional packet exactification and makes no assertion on induced infinite representations
---

**ESTABLISHED DECODER CRITERION.**  Fix a finite context-packet menu and let
`Omega` be the finite set of all pairs `(c,lambda)` of a context and a marked
type which the menu is to cover.  In a finite-dimensional microstate after
exactifying the packet tables, let

```text
Q_c=sum_(lambda:(c,lambda) in Omega) Q_(c,lambda)      (GTC1)
```

be the orthogonal marked isotypic decomposition inside each context packet.
Projections belonging to different contexts need not commute or be
orthogonal.  Write `L` for the number of contexts; then every matrix `X`
satisfies

```text
sum_omega ||XQ_omega||_2^2<=L||X||_2^2.               (GTC1')
```

Suppose a global actuator induces a permutation `sigma` of `Omega`.  For
every `omega`, suppose the finite-matrix decoder supplies a carrier
`P_omega<=Q_omega`, coarse and fine selectors

```text
e_omega,f_omega<=P_omega,
tr(e_omega)=tr(P_omega)/2,
tr(f_omega)=tr(P_omega)/4,                             (GTC2)
```

and a decoded unitary `U_omega`.  Put

```text
d_omega=||U_omega e_omega U_omega^*
                    -f_(sigma(omega))||_2.             (GTC3)
```

Assume two genuinely matrix-only estimates for a fixed finite ordinary word
menu `T`, constants `K<infinity`, `alpha>0`, and moduli tending to zero:

```text
sum_omega d_omega^2
 <=K sum_(r in T) sum_omega ||(r(U)-1)Q_omega||_2^2
   +eta(delta),                                        (GTC4)

sum_omega tr(P_omega)
 >=alpha E_forbid(U)-zeta(delta).                      (GTC5)
```

Here `E_forbid` is the total ordered forbidden-product mass of the original
shared BCS tuple, before its context occurrences are separated.  Then

```text
sum_(r in T)||r(U)-1||_2^2
 >=alpha/(4KL) E_forbid(U)
   -(eta(delta)+zeta(delta)/4)/(KL).                   (GTC6)
```

Neither alignment of carrier multiplicities nor a preferred marked type is
needed.  The permutation may have arbitrarily many cycles, and every local
transport may contain an arbitrary unitary multiplicity twist.

## Global non-CE endpoint

Let `E_base(U)` be the involution and shared-context commutator part of the
robust BCS energy.  If the actuator presentation also bounds `E_base` by a
fixed multiple of its ordinary relator energy, then
`non-ce-bcs-has-robust-approximate-energy-gap` and `(GTC6)` give a constant
presentation-energy floor.  Indeed

```text
E_base(U)+E_forbid(U)>=beta_B^rob,                      (GTC7)
```

so either the base rows already pay at least `beta_B^rob/2`, or `(GTC6)` pays
at least `alpha beta_B^rob/(8KL)-o(1)`.  Canonical microstates of a group with
vanishing presentation defect are therefore impossible whenever exact
completeness keeps the central mark nontrivial.

This uses the non-CE BCS globally: `(GTC5)` must be proved from the same
shared tuple and may sum carriers over all contexts and marked types.  No
single context is asked to carry a fixed positive mass, avoiding the existing
single-context circularity.

## Why the criterion is not algebraic

The projections `Q_omega` and `P_omega` in `(GTC4)--(GTC5)` are analytic
finite-matrix decodings.  Individual selector rows are not relators and need
not vanish in the regular representation.  If instead `(GTC3)=0` followed
from universal group-algebra identities on positive packet projections, the
cyclic trace bound would kill all `P_omega` in the regular trace.  Likewise an
operator version of `(GTC4)--(GTC5)` on every representation would contradict
the induced-type firewall.

Thus `(GTC4)` is the exact holonomy gate: not a product of row words, but a
finite-coordinate estimate saying that the ordinary global actuator energy
dominates the **sum of type-compressed mixed rows**.  `(GTC5)` is the global
coverage gate.  Together they are sufficient, and neither can be replaced by
finite packet restriction tables or a local context calculation.

The coverage gate is now discharged at the analytic level.
`forbidden-weighted-type-carrier-coverage-is-rank-rounding` takes
`P_omega` to be the largest four-divisible subprojection of the marked
forbidden piece `F_cQ_omega`.  It loses at most three matrix dimensions per
type, so `(GTC5)` holds with `alpha=1` and `zeta=o(1)` over the fixed menu.
These carriers need not reduce the full context packet.  Requiring reducing
carriers is an additional, generally false condition unless the forbidden
projection acts only on the external multiplicity factor.  Consequently the
sole unresolved gate in this criterion is `(GTC4)` for the analytic
forbidden-weighted carriers.

One natural aggregate actuator is now excluded.
`one-hecke-holonomy-cell-cannot-pay-the-cyclic-selector-sum` takes the positive
regular stationary packet flow and closes an arbitrary single transport
holonomy two-cell by choosing the last edge multiplicity gauge.  All edge,
partial-swap Gram, and attaching-word energies are then zero, while the
coarse-to-fine cyclic sum remains at least one quarter of the carrier mass,
independently of those gauges.  Hence `(GTC4)` cannot come from one
uncompressed Hecke/partial-swap holonomy word.  A successful actuator must
see the analytic forbidden-weighted selector cuts at intermediate stages, or
otherwise remove the last-edge gauge by a genuinely matrix-coordinate rule.

The smallest multi-square repair has now been computed.
`compressed-k2m-locks-gauge-but-needs-matrix-separator` shows that the
`m-1` rectangles of `K_(2,m)` do remove the last column gauge and, after
compression by orthogonal source cuts, bound the source-capacity deficit by
twice rectangle energy plus compressed leakage. However exact row-column
factorizations make every rectangle word vanish while leaving the selector
capacity deficit positive. Universal word relators for the leakage would
contradict the regular trace. Therefore `K_(2,m)` closes the gauge part of
GTC4 but not its matrix-only authentication part: a shared-BCS separator for
the compressed leakage remains the irreducible input.
