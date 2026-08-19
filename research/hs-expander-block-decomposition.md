---
rg: 2
id: hs-expander-block-decomposition
kind: claim
title: Nested normalized-HS Kun decomposition for the Leavitt compression pair
distinct_from:
  hs-one-level-expander-block-decomposition: That is the universal one-group Kazhdan decomposition problem with no ambient compressors; this is the stronger application-specific simultaneous decomposition for the explicit Leavitt pair, including nesting and compressor transport.
  nonmonomial-multiplicity-obstructs-hs-compressor-transport: That proves the corresponding compressor statement is false for arbitrary Kazhdan pairs; this claim is deliberately restricted to the Leavitt pair used by the consumer.
  tracial-median-concentration: That concentrates the fine block traces once this nested transported partition exists; this claim produces the partition and its gaps.
  leavitt-steinberg-hs-stable: That is the branch selection for the Steinberg cover; this is the missing structural input used to select it.
artifacts:
  - docs/TRUE_DIAGONAL_NORMALIZER_RIGIDITY.md
  - docs/TRUE_SPECTRAL_COAREA_INVARIANT_CUT.md
  - c1168433:official/counterexample.tex
---

Use the explicit compression triple from
`openai-nine-leaf-leavitt-configuration`.  Thus, for the binary Leavitt
algebra `R=L_(F_2)(1,2)`, there are Kazhdan groups

```text
Gamma = EL_alpha(R) ~= EL_3(R) <= G = EL_D(R) ~= EL_9(R)
```

and compressors `u,v in G` such that

```text
G=<Gamma,u,v>,
u Gamma u^(-1) <= Gamma,
v Gamma v^(-1) <= Gamma.
```

Fix finite symmetric generating sets `S_Gamma` and `S_G` and Kazhdan
constants for the two groups.  Ask for a function

```text
eps(delta) -> 0  as delta -> 0
```

and positive constants `kappa'_Gamma,kappa'_G`, all dimension-independent,
such that every `delta`-almost representation

```text
phi:G -> U(d)
```

in normalized Hilbert--Schmidt norm admits a projection `p in M_d` with
`tau(1-p)<=eps(delta)` and **nested** finite-dimensional abelian block
algebras

```text
B_G <= B_Gamma <= p M_d p.
```

Write the coarse atoms of `B_G` as `q_A` and the fine atoms of `B_Gamma` as
`p_i`, so every `p_i` lies under a unique `q_A` and both families sum to `p`.
The required properties are the following.

### Fine Gamma decomposition

For every `s in S_Gamma`,

```text
sum_i ||[phi(s),p_i]||_2^2 <= eps(delta).
```

On every nonzero fine block, with normalized corner trace `tau_i` and
`a_(i,s)=p_i phi(s) p_i`, require

```text
sum_(s in S_Gamma) ||a_(i,s)x-x a_(i,s)||_(2,p_i)^2
  >= (kappa'_Gamma)^2 ||x-tau_i(x)p_i||_(2,p_i)^2
```

for every self-adjoint `x in p_i M_d p_i`.

### Coarse ambient decomposition

For every `s in S_G`,

```text
sum_A ||[phi(s),q_A]||_2^2 <= eps(delta).
```

On every nonzero coarse block, with normalized corner trace `tau_A` and
`b_(A,s)=q_A phi(s) q_A`, require

```text
sum_(s in S_G) ||b_(A,s)x-x b_(A,s)||_(2,q_A)^2
  >= (kappa'_G)^2 ||x-tau_A(x)q_A||_(2,q_A)^2
```

for every self-adjoint `x in q_A M_d q_A`.

### Compressor transport of fine blocks

For each `t in {u,v}` and every fine atom `p_j`, there is a fine atom
`p_(sigma_t(j))` such that

```text
||phi(t)p_j phi(t)^* - p_(sigma_t(j))||_2 <= eps(delta),
tau(p_(sigma_t(j))) >= tau(p_j)-eps(delta).
```

No injectivity of `sigma_t` is assumed at this stage; the later median and
majority argument is what extracts the matching on the nonexceptional mass.

This is the exact structural input used by
`tracial-median-from-block-decomposition` and
`hs-block-decomposition-to-steinberg-stable`: the fine `Gamma` atoms define
the block-size observable, the coarse `G` atoms provide its fiberwise medians,
and the two compressors provide the one-sided size drift.

## Why the claim is application-specific

A previous version quantified over an arbitrary Kazhdan group `Gamma` and
then used `phi(t)` for ambient compressors which were not even in the stated
domain of `phi`.  Repairing the domain to a general pair `Gamma<=G` does not
save that universal statement.

`nonmonomial-multiplicity-obstructs-hs-compressor-transport` gives an exact
fixed-dimensional counterexample with

```text
Gamma = SL_3(Z),
G = Gamma x A_5.
```

The representation is trivial on `Gamma` and is the irreducible
three-dimensional icosahedral representation on the `A_5` factor.  A positive
scalar `Gamma`-gap forces every fine block to have rank one, while compressor
transport would make `A_5` permute three lines, contradicting irreducibility.
The same exact representation defeats every putative error modulus tending to
zero by compactness.  Thus compressor-monomiality is not a consequence of
property `(T)` or of exact multiplicativity.

This also fixes an error in the former "exact case collapses" paragraph.  If
`A` is an abelian algebra in `pi(Gamma)'`, the relation
`t Gamma t^(-1)<=Gamma` shows only that `pi(t)^* A pi(t)` is another subalgebra
of `pi(Gamma)'`; it does **not** imply `pi(t)^* A pi(t)<=A`.  The full finite
image algebra `C^*(pi(Gamma))` is normalized in an exact finite-dimensional
representation because its conjugate is an included subalgebra of the same
finite dimension, but an abelian refinement of the multiplicity commutant
need not be normalized.  Choosing such a refinement simultaneously for all
compressors is precisely a monomiality problem.

The Leavitt pair therefore needs its own argument.  The permutation proof has
the missing coordinate algebra for free; a unitary microstate does not.

## The one-level analytic core is still live

Remove nesting and compressors and ask only for one Kazhdan group to split
into almost-invariant blocks with a uniform scalar adjoint gap.  That problem
is now isolated as `hs-one-level-expander-block-decomposition`.

The current Cairn neighborhood gives three useful pieces.

- `bounded-low-gap-witness-gives-balanced-cut`: a uniformly bounded low-gap
  witness yields a quantitatively balanced almost-invariant spectral cut.
- `low-gap-witness-spike-or-balanced-cut`: without the operator-norm bound,
  either such a cut exists or a fixed amount of `L2` mass sits on a
  small-trace spike support.
- `small-trace-rank-one-quarantine`: once a small-trace region is known, it
  can be shattered into rank-one atoms with at most linear total HS boundary
  cost; rank-one atoms have the scalar gap vacuously, and their individual
  compressor drift is automatically `O(sqrt(tau(e)))`.

So a **known** spike support is not the local obstruction.  The unresolved
one-level issue is to organize all successive low-gap directions so that the
total quarantined trace and the total cut boundary remain `o(1)`, rather than
finding fresh spikes until order-one mass has been consumed.

## Exact-centralizer capture does not close the one-level gap

Alekseev--Thom Open Problem 6.2 asks, in particular, whether generator lifts
can be chosen whose exact finite-level centralizers capture the ultraproduct
commutant.  That algebraic statement is insufficient here.

`centralizer-capture-controls-nonspiky-gap-failures` proves the positive
bounded part: for a fixed `L^infinity/L2` bound, capture forces the total trace
of bad minimal centralizer blocks to vanish.  But
`rank-one-lift-perturbation-gap-no-go` gives a Kazhdan example with scalar
ultraproduct commutant and exact scalar finite-level centralizers while the
finite-level adjoint gap still tends to zero.  The normalized witnesses live
on vanishing-rank directions and have diverging operator norm, so they exist
in the Hilbert-space ultraproduct but not as bounded elements of the tracial
algebra ultraproduct.

The missing strengthening is therefore a finite-level anti-spike/summability
statement, not bare algebraic centralizer capture.

## Other dead ends already fenced off

- Pimsner--Popa index is discontinuous for tiny refinements in normalized HS
  norm and takes a maximum where the consumer needs fiberwise information.
- `kazhdan-projection-rounding` needs a genuine representation and therefore
  lives on the exact/ultraproduct side, after finite-level spike structure may
  already have disappeared.
- normalizing a masa is too strong: `docs/TRUE_DIAGONAL_NORMALIZER_RIGIDITY.md`
  converts that hypothesis back into a permutation model of comparable
  defect.
- operator-norm almost-invariance is a different problem; it rules out the
  normalized-HS spike regime by assumption and is not an admissible upgrade.

## Attempts

1. **Direct spectral splitting.**  Bounded low-gap witnesses can be cut by
   spectral coarea, but the clipping dichotomy leaves small-trace spikes.
   `small-trace-rank-one-quarantine` repairs one identified spike; no
   dimension-free potential is known that makes repeated repairs summable.
2. **Exact centralizers first.**  This works for uniformly bounded witnesses
   but fails on the established rank-one lift perturbation.  Any revival must
   control the Hilbert-space `L2` ultraproduct, not only the tracial algebra
   ultraproduct.
3. **Make compressor transport formal from property `(T)`.**  Refuted by
   `nonmonomial-multiplicity-obstructs-hs-compressor-transport`.  The Leavitt
   pair needs a specific compatibility mechanism between its two nested
   decompositions and its prefix compressors.
4. **Index or invariant masa.**  Both are already fenced by the metric
   discontinuity and diagonal-normalizer results above.
