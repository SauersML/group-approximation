---
rg: 2
id: exact-expander-a5-carriers-collapse-marked-center
kind: claim
title: Every exact finite actor carrier collapses the marked A5 center with a Kazhdan-uniform bound
distinct_from:
  exact-models-cannot-separate-marked-pair: that treats the complete two-point label specification with a deleted exceptional set and an expander-sheet argument; this is the direct Hilbert-space estimate for one A5 center projection and gives the explicit marked-center inequality consumed by the lamp route.
  finite-quotient-blindness: that is the algebraic statement that the finite image of Gamma is normal; this combines that collapse with the Kazhdan projection estimate and the canonical A5 separation mass.
  two-site-a5-plancherel-center-separates-mark: that establishes positive marked separation in the canonical lamp trace; this proves every exact finite actor carrier forces the opposite profile.
---

**ESTABLISHED DIMENSION-UNIFORM EXACT-CARRIER OBSTRUCTION.**  Let
`Gamma<G` be the pinned Kun--Thom pair, let `h` be its marked compressor, and
fix a finite symmetric Kazhdan set `S_Gamma` for `Gamma` with constant
`kappa>0`.  Let

```text
phi:G -> Sym(Y)                                          (AEC1)
```

be any genuine action on a finite set.  For a subset `E subset Y`, use the
normalized counting norm and suppose

```text
max_(gamma in S_Gamma)
  |E triangle phi(gamma)E|/|Y| <= delta.                (AEC2)
```

Then

```text
|E triangle phi(h)E|/|Y| <= 4 delta/kappa^2.            (AEC3)
```

In particular an exactly `Gamma`-invariant binary center label is fixed by
`h` in every exact finite actor carrier.

The estimate applies directly to a proposed finite A5 lamp chart.  If
`E_p,E_q subset Y` are the `z=1` labels at the marked sites and

```text
|E_q triangle phi(h)E_p|/|Y| <= delta_h,                (AEC4)
```

then

```text
(|E_p triangle E_q|/|Y|)^(1/2)
 <= 2 sqrt(delta)/kappa + sqrt(delta_h).                (AEC5)
```

But the canonical rational five-dimensional A5 center has

```text
tau(E_p triangle E_q)=35/72.                            (AEC6)
```

Thus no family of exact finite quotient, expander, or other genuine finite
`G`-set carriers can realize the canonical marked A5 profile with
`delta,delta_h -> 0`.  The obstruction is independent of `|Y|` and of every
lamp multiplicity fiber.

This sharply fences the non-path attack.  Finite quotient expanders do close
the actor boundary, but that exact closure erases the marked lamp separation.
Therefore an argument cannot first replace the actor maps by a genuine finite
action and then attach the A5 labels.  To prove
`two-site-a5-center-classicalization` one must extract genuinely approximate
permutations and the labels simultaneously; doing so would immediately
contradict `two-point-approximation-fails`.  The remaining analytic gate is
still the passage from unitary multiplicity couplings to that simultaneous
approximate permutation table.  Residual-finite quotient packets do not make
the passage: their surviving kernel cocycle is exactly
`finite-quotient-fell-untwisting-leaves-kernel-cocycle`.

DERIVATION
exact-expander-a5-mark-collapse-proof

