---
rg: 2
id: code-distance-upgrades-pair-energy-to-full-pinching
kind: claim
title: Code distance upgrades averaged generator commutators to full pinching after one commuting reference exists
distinct_from:
  joint-pinching-costs-linear-generator-gap: that gives the sharp factor L for an arbitrary commuting reference; this shows that code support removes that factor completely.
  gapped-face-pinchings-give-same-hilbert-code-pvm-rounding: that projects the original tuple using a common face-Hamiltonian gap; this is a one-reflection orthogonalization relative to an already commuting reference tuple.
  all-dual-unique-neighbors-contract-operator-tails: that contracts sparse coordinate tails before a common PVM exists; this gives the dimension-free diffuse correction once a commuting reference PVM has been obtained.
---

ESTABLISHED.  Let `C=ker(H) subset F_2^L` have relative distance `delta`
and normalized classical test soundness `kappa`:

```text
|Hx|/M >= kappa dist(x,C)/L.                              (CDP1)
```

Let `S_1,...,S_L` be commuting reflections in a finite tracial von Neumann
algebra, and define their parity energy

```text
E_par=(1/M)sum_h ||prod_(i:h_i=1)S_i-I||_2^2.             (CDP2)
```

For every reflection `R`, put

```text
D(R,S)=(1/L)sum_i ||[R,S_i]||_2^2.                       (CDP3)
```

Then there are commuting reflections `S'_1,...,S'_L` with one joint PVM
supported on `C`, and a reflection `R'` commuting with every `S'_i`, such
that

```text
(1/L)sum_i ||S_i-S'_i||_2^2 <= E_par/kappa,              (CDP4)
||R-R'||_2^2
 <= (10/delta)D(R,S)+(40/(delta kappa))E_par.             (CDP5)
```

All corrections lie in the original algebra.  The constants are independent
of `L`, the number of codewords, and the matrix dimension.

The key point is that code distance deletes the weight-one obstruction from
`joint-pinching-costs-linear-generator-gap`.  If `(q_c)_(c in C)` is the
joint code PVM of `(S'_i)`, then the adjoint Fourier blocks of any operator
are indexed by differences `c+c' in C`.  Hence every nonzero adjoint
character has weight at least `delta L`, and `(JPG4)` improves to

```text
||R-E_Q(R)||_2^2 <= D(R,S')/(4 delta).                    (CDP6)
```

Applying `de-la-salle-full-pinching-rounds-one-reflection` gives `(CDP5)`
after the elementary perturbation estimate in the proof route.

This is a genuine parity-aware orthogonalization theorem, but it is a
**basin theorem**, not the missing basin-capture theorem.  It starts with one
commuting reference tuple.  The balanced occurrence input instead gives
many exact or approximate bounded face PVMs with no common joint PVM.
`all-dual-unique-neighbors-contract-operator-tails` can move sparse bad sites
to a shortened core, but its Loewner inequalities do not manufacture the
commuting reference on the diffuse core.  The exact remaining inequality is:

> From balanced equality, local-face, parity, and complete-pair energy,
> construct a commuting reference `(S_i)` with average displacement `o(1)`
> and parity energy `o(1)`, without first assuming a global joint PVM.

Once that inequality is available, `(CDP4)`--`(CDP5)` give a
cardinality-free same-algebra terminal correction; no further PVM
orthogonalization theorem is missing.

