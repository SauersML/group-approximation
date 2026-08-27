---
rg: 2
id: lin-introspection-payload-is-global-gauge-covariant
kind: claim
title: Lin's introspection payload shares the Pauli extraction gauge
distinct_from:
  lin-gap-wrappers-retain-oracular-atlas-holonomy: that shows the final static game's projection atlas still has groupification holonomy; this proves that global Pauli-frame conjugacy is not an additional obstruction inside the game soundness argument.
  single-anchor-cannot-pin-pauli-gauge: that characterizes external-frame anchoring; this bypasses anchoring by transporting every payload measurement through the same extraction isometry.
  tree-transitive-site-noise-localization: that needs physical bad sites for the BGV tape architecture; this shows the native introspection/game route can instead remain entirely gauge-covariant.
---

After replacing Lin's erroneous code-space sampler by de la Salle's spanning
generator-column sampler, the Pauli rigidity theorem supplies a global
extraction isometry.  Lin's introspection construction does **not** keep the
computation observables in an old physical frame.  In the soundness proof of
Theorem 7.3, for every question `x` and answer `a` it defines

```text
Ahat_a^x=V_A A_a^x V_A^*,          Bhat_a^x=V_B B_a^x V_B^*.  (LGC1)
```

It then forms a new strategy using all the transformed PVMs in `(LGC1)`,
and only afterwards replaces the distinguished Pauli PVMs by their standard
extracted versions.  The `Read`, `Hide`, `Sample`, and `Intro` payload PVMs
remain in the same transformed gauge.  Acceptance probabilities are
unchanged by the simultaneous conjugacy, and their consistency with the
standard Paulis is charged by the cross-tests.

Therefore an exact global conjugation, including the dense coherent and
multiplicity-valued conjugacies from
`generator-column-pauli-test-globalizes-but-does-not-pin-sites`, is harmless
for the native introspection computation.  No fixed external anchor and no
sparse physical bad-site set are needed at this stage: the computation is
defined relationally inside the recovered Pauli incidence.

The corrected column sampler retains the classical succinctness needed by
the game.  For an explicit `[K,n,d]` code with `K=Theta(n)`, sample a
`ceil(log K)`-bit index and let the polynomial-time decider compute the
corresponding generator column.  If necessary, pad to a power-of-two index
set by duplicating columns a bounded number of times; the measure changes by
a bounded density ratio, so the spectral-gap constant remains uniform.  The
typed conditionally-linear sampler transports the short seed; the classical
decider performs the column lookup and parity check.

This does **not** solve ordinary groupification.  The game verifier may read
an `n`-bit Pauli outcome and compute its parity against a dense column at
classical cost `poly(n)`.  A group presentation instead needs an ordinary
word representing that dense Pauli product and a bounded-area derivation of
each sampled consistency/magic-square relation.  Replacing the classical
decoder by such words is exactly
`uniform-halting-pauli-word-oracle`.  Global gauge pinning and
`clifford-hs-defect-becomes-adversarial-site-noise` are not additional gates
on this gauge-covariant route; bounded-area self-similar query naming is.

