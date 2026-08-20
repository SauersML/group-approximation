---
rg: 2
id: hs-one-level-expander-block-decomposition
kind: claim
title: One-level normalized-HS Kun decomposition for a Kazhdan group
distinct_from:
  hs-expander-block-decomposition: That is now the application-specific nested Leavitt pair, with coarse/fine compatibility and compressor transport; this claim has one Kazhdan group, one block partition, and no compressor clause.
  kun-expander-decomposition-formalized: That is the established permutation/Hamming theorem; this asks for its finite-level normalized-HS analogue for unitary almost-representations.
  centralizer-capture-controls-nonspiky-gap-failures: That proves a bounded-witness consequence under an additional exact-centralizer-capture hypothesis; this claim assumes only small almost-representation defect and asks for the whole partition.
---

Let `Gamma` be a finitely generated group with property `(T)`, with fixed
finite symmetric generating set `S` and Kazhdan constant `kappa`.  Ask for a
function

```text
eps(delta) -> 0  as delta -> 0
```

and a constant `kappa'>0`, depending only on the Kazhdan data, such that every
`delta`-almost representation

```text
phi:Gamma -> U(d)
```

in normalized Hilbert--Schmidt norm admits a projection `p in M_d` and an
orthogonal decomposition

```text
p=p_1+...+p_k,
tau(1-p)<=eps(delta),
```

with the following two properties.

### Vanishing total block boundary

For every `s in S`,

```text
sum_i ||[phi(s),p_i]||_2^2 <= eps(delta).
```

### Uniform scalar adjoint gap on every block

Writing `tau_i=tau(.)/tau(p_i)` and `a_(i,s)=p_i phi(s) p_i`, require for
every self-adjoint `x in p_i M_d p_i`

```text
sum_(s in S) ||a_(i,s)x-x a_(i,s)||_(2,p_i)^2
  >= (kappa')^2 ||x-tau_i(x)p_i||_(2,p_i)^2.
```

No lower bound on `tau(p_i)` and no bound on the number of blocks is asked.
Vanishing-trace atoms are allowed.

For a genuine representation the statement holds with zero boundary by
splitting the restriction into irreducible summands; property `(T)` gives the
adjoint gap on each summand because its commutant there is scalar.  The
content is dimension-uniform control at positive normalized-HS defect, where
there is no exact irreducible decomposition.

This is the analytic core which can legitimately be called the normalized-HS
analogue of Kun's expander decomposition.  The compressor/nesting problem is
separate: `nonmonomial-multiplicity-obstructs-hs-compressor-transport` proves
that no universal compressor clause can be appended to this statement.

## What is already proved around it

`bounded-low-gap-witness-gives-balanced-cut` and
`low-gap-witness-spike-or-balanced-cut` reduce a failure of the block gap to
one of two local objects: a balanced low-boundary spectral cut or a
small-trace spike carrying a definite fraction of the normalized witness's
`L2` mass.

`small-trace-rank-one-quarantine` then shows that an **identified** projection
`e` of trace `eta` can be shattered into rank-one blocks at total generator
boundary at most `2 eta` per generator.  Those atoms have the scalar gap
vacuously.  Thus a single spike support is cheap; the problem is controlling
the union produced by repeated splitting.

Under the additional hypothesis that exact finite-level centralizers capture
the tracial ultraproduct commutant,
`centralizer-capture-controls-nonspiky-gap-failures` eliminates every family
of bad blocks admitting a fixed `L^infinity/L2` bound.  The established
`rank-one-lift-perturbation-gap-no-go` shows why this does not settle the
claim: normalized low-energy vectors may concentrate on vanishing-rank
supports and never define bounded ultraproduct elements.

There is now a sharper finite-window fence.  The established
`finite-window-hs-tests-ignore-low-rank-generator-surgery` proves that a
vanishing-relative-rank perturbation of the generators is invisible to every
fixed word window.  Combining it with the rank-one surgery construction gives
`irrep-window-does-not-force-hs-gap`: even when the perturbed generator algebra
is irreducible, so its exact block decomposition is the single block `1`, all
fixed relation defects can tend to zero while the scalar adjoint gap of that
full-trace block tends to zero.  Thus the missing selection principle cannot
score exact irreducible generator blocks by finite relator defect.  It has to
see and refine the low-energy support itself.

## Attempts

1. **Recursive balanced cutting.**  If every gap failure produced a balanced
   cut whose boundary were controlled by the ambient almost-representation
   defect, recursion would terminate with a Kun-style partition.  The current
   coarea lemmas control a cut by the *witness energy*, but a block can fail a
   fixed gap threshold with energy bounded away from the model defect; no
   summable global budget has yet been extracted.
2. **Clip, then quarantine spikes.**  The clipping dichotomy plus
   `small-trace-rank-one-quarantine` repairs one low-gap witness.  Naive
   iteration can expose fresh disjoint spike supports, and nothing currently
   prevents their total trace from becoming order one.  A monotone potential
   or a common-support theorem for the spiky low-energy subspace is the
   missing step.
3. **Exact-centralizer capture.**  Aggregation in the tracial ultraproduct
   works for uniformly bounded witnesses and fails exactly on the spike
   regime.  Any successful version must control the Hilbert-space `L2`
   ultraproduct / uniform integrability, not merely the algebra ultraproduct.
4. **Rank-one everything.**  Rank-one blocks always have the gap, but
   `small-trace-rank-one-quarantine` gives total boundary `2 tau(e)` only on a
   small region.  Shattering all of `1` costs order one and cannot provide
   `eps(delta)->0`.
5. **Exact irreducible generator blocks plus relator selection.**  Dead by
   `irrep-window-does-not-force-hs-gap`.  The bad gap can occur on the unique
   full-trace irreducible block even while every fixed relation word has
   vanishing normalized-HS defect.  Any successful decomposition must be
   scale-adaptive and cut inside an irreducible generator algebra when its
   low-energy directions demand it.
