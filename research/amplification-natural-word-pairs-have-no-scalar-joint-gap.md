---
rg: 2
id: amplification-natural-word-pairs-have-no-scalar-joint-gap
kind: claim
title: Amplification-natural word pairs cannot have a scalar joint-commutant gap
distinct_from:
  amplification-natural-words-cannot-read-packet-multiplicity: that proves fixed word statistics and PI degree cannot read raw multiplicity; this directly contradicts a scalar Poincare inequality for the joint word action on a canonical corner.
  central-polynomial-tapes-do-not-exhaust-commutant: that rules out certifying equality between one named tape and a packet commutant; this applies to any finite pair of word-generated algebras, even when both are scalable and equipped with uniform internal actor gaps.
  three-gauge-tests-leave-a-tensor-spectator: that gives one concrete Pauli-reservoir countermodel; this proves the tensor-spectator obstruction for every amplification-natural word pair and corner.
---

Let `P(U)` be a nonzero canonical corner obtained from a finite represented
tuple `U` by word evaluation and spectral functional calculus, and let `S(U)`
be any finite family of represented words compressed to that corner.  If the
construction is natural under spectator amplification, then no constant
`kappa>0` can make

```text
||Y-tau_P(Y)P||_2
 <= kappa^(-1)
    (sum_(s in S(U)) ||[Y,s]||_2^2)^(1/2)              (ANJ1)
```

hold for every finite-dimensional model and every `Y in P M_d P`.

Indeed amplify one nonzero exact model by `I_l`, `l>=2`.  Naturality gives

```text
P(U tensor I_l)=P(U) tensor I_l,
s(U tensor I_l)=s(U) tensor I_l.
```

For any traceless nonzero `Z in M_l`, take `Y=P(U) tensor Z`.  Every
commutator on the right of `(ANJ1)` is zero, whereas `tau_P(Y)=0` and the
left side is `||P tensor Z||_2>0`.  This is an exact zero-defect
countermodel, not a deterioration of the gap constant.

Consequently the dual-prefix Pauli packet plus a transitive Kazhdan actor,
the self-similar Clifford quantum-expander tape, and a scalable product-socle
normalizer all fail the scalar joint-gap test whenever their corner and
letters are supplied by the currently proposed word-natural constructions.
Their internal expansion can round an operator to the actual joint
commutant, but cannot force that commutant to be scalar after amplification.

The amplification-stable replacement is a **relative** estimate

```text
||Y-E_(S(U)')(Y)||_2
 <= C (sum_(s in S(U)) ||[Y,s]||_2^2)^(1/2),           (ANJ2)
```

whose target commutant grows from `S(U)'` to `S(U)' tensor M_l` under
amplification.  Such an estimate may authenticate the named tensor factors
only modulo a common spectator.  Eliminating that spectator, or naturally
selecting one irreducible copy, is not expressible by fixed group-word
relations on all matrix microstates.
