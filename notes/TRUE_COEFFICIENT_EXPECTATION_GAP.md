# The transported cut has a fixed distance from the raw coefficient algebra

Date: 2026-08-13

## Outcome

The `7/32` minimal-cut anti-normalizer gap can be weakened to a membership
obstruction for the entire raw coefficient algebra.  No permutation or
minimal-projection matching is required.

Let `F_epsilon`, `epsilon in {+1,-1}^2`, be the four raw coefficient character
cuts and let

```text
q=sum_epsilon F_epsilon.
```

For a transported character cut `G=U*F_eta U`, trace-flatness gives

```text
tau(q)=1/2,
tau(G)=1/8,
tau(G q)=sum_epsilon tau(G F_epsilon)=4/64=1/16.  (CEG1)
```

The Hilbert--Schmidt orthogonal projection of `G` onto the nonunital
coefficient space

```text
A_0=span{F_epsilon}
```

is

```text
E_(A_0)(G)=sum_epsilon
  tau(F_epsilon G)/tau(F_epsilon) F_epsilon
            =(1/8)q.                                  (CEG2)
```

Direct expansion therefore gives

```text
||G-q/8||_2^2
  =tau(G)-2(1/8)tau(Gq)+(1/64)tau(q)
  =15/128.                                            (CEG3)
```

The matrix identity `(CEG3)` is kernel-checked in
`GroupApproximation/Sofic/DoublePauliCoefficient.lean` as
`hsNormSq_projection_sub_eighth_carrier_eq_fifteen_div_128`.

## Stronger terminal reduction

It is enough to prove that one transported cut becomes close to the raw
coefficient *space* at finite matrix coordinates:

```text
dist_2(G_n,A_(0,n)) -> 0.                             (CEG4)
```

One no longer needs to identify which raw character it matches.  Since
`q_n/8` is its exact Hilbert--Schmidt projection under the limiting flat
moments, `(CEG3)` contradicts `(CEG4)` by a fixed margin.

Equivalently, adjoining `1-q` gives a unital finite-dimensional coefficient
algebra.  Projection rigidity and the trace `1/8` then recover a nearby
minimal raw cut, returning to the `7/32` formulation.  The nonunital
expectation statement is shorter because it avoids this last perturbation
step.

## Remaining gate

The needed matrix-specific theorem is now only:

> finite-multiplicity recovery places one comb-transported coefficient cut
> asymptotically in the raw four-character coefficient space.

This remains unproved.  It cannot follow from abstract group-algebra
relations, since the regular representation realizes `(CEG3)` exactly.  Nor
does ordinary Reynolds averaging imply it: the relative comb implementer is
not close to the relevant commutant.  The theorem must use simultaneous
coordinate recovery of the two chart multiplicity modules or the equivalent
one-sided multiplication-support relation.

The gain is conceptual and quantitative: the endpoint is membership in a
fixed four-dimensional space, not equality of two algebras, a permutation of
four cuts, or a full Leavitt family.

