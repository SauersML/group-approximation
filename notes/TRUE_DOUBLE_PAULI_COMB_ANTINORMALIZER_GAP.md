# The comb has a fixed coefficient anti-normalizer gap

Date: 2026-08-13

## Outcome

The trace-flat table from `TRUE_DOUBLE_PAULI_COMB_IS_FOURIER_FLAT.md` gives a
sharper terminal obstruction than a generic positive-mass estimate.  The comb
conjugate of every coefficient character cut stays a fixed distance from
every original character cut.

Let

```text
A = span{F_epsilon : epsilon in {+1,-1}^2},
G_eta = U* F_eta U.
```

The exact trace identities are

```text
tau(F_epsilon)=tau(G_eta)=1/8,
tau(F_epsilon G_eta)=1/64.
```

For projections `F,G`,

```text
||F-G||_2^2=tau(F)+tau(G)-2 Re tau(FG).
```

Therefore, for all sixteen pairs,

```text
||F_epsilon-G_eta||_2^2 = 7/32.                     (ANG1)
```

This is independent of the characters and of matrix dimension.  It persists
in every trace-preserving hyperlinear microstate sequence because all three
traces are fixed group-algebra moments.

The projection-distance formula and the specialization to `7/32` are
kernel-checked in `GroupApproximation/Sofic/DoublePauliCoefficient.lean` as

```text
hsDistSq_projections_eq_re_normTrace
hsDistSq_projections_eq_seven_div_thirty_two.
```

## Anti-normalizer interpretation

Every automorphism of the four-dimensional commutative algebra `C^4` permutes
its four minimal projections.  Hence if comb conjugation normalized `A`, then
each `G_eta` would equal some `F_epsilon`.  Equation `(ANG1)` rules this out by
a fixed gap.  More quantitatively, no transported minimal projection can be
`o(1)`-close to any permutation of the raw minimal projections.

Thus a matrix-coordinate theorem which forced the recovered coefficient
algebra to align with its comb conjugate would immediately contradict the
canonical trace.  The terminal step would not need rank counting, a spectral
condition number, or the full Leavitt contraction inequality.

## The exact remaining gate

This is still a reduction, not a proof of a nonhyperlinear group.  The fixed
group-algebra coefficient algebra is not comb-normalized in the regular
representation; `(ANG1)` explicitly measures that failure.  Therefore
normalization cannot be deduced from abstract group relations alone.

What remains is specifically matrix-coordinate finite-multiplicity recovery:

> Show that, in a hypothetical trace-preserving matrix microstate sequence,
> the coefficient multiplication module canonically recovered from the two
> Kazhdan charts makes the raw coefficient `C^4` and its comb transport
> asymptotically the same finite multiplicity algebra, up to permutation of
> their minimal cuts.

Once this statement gives

```text
min_epsilon ||F_epsilon-G_eta||_2^2 -> 0
```

for one `eta`, `(ANG1)` gives the contradiction `0=7/32`.

This is a cleaner version of the compatible-coordinate-commutant gate.  The
fixed `C^4` packet removes gauge ambiguity and supplies a quantitative
anti-normalizer witness; the unresolved content is the coordinate recovery
which identifies the two multiplicity algebras.  A positive answer to a
generic ultraproduct commutant-lifting problem is not automatically enough:
the recovery must be simultaneous and comb-compatible.

