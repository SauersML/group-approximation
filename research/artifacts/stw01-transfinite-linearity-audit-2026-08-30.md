# Problem I: transfinite quasitrace-linearity audit

## The new permanence theorem

Let a unital C*-algebra `A` have a continuous increasing ideal filtration

```text
0=I_0 subset I_1 subset ... subset I_gamma=A
```

of arbitrary ordinal length.  If every bounded `2`-quasitrace on each
successor quotient `I_(alpha+1)/I_alpha` is a trace, then every bounded
`2`-quasitrace on `A` is a trace.

The result permits nonzero traces on every layer.  It is therefore strictly
broader than the earlier transfinite theorem for quasitrace-invisible
successor layers.

## Why nonunital intermediate ideals cause no gap

One should not argue that quasitraces on an intermediate ideal extend to
its unitization and then invoke the unital extension theorem.  No such
extension assertion is needed.  Fix an ambient quasitrace `tau` on `A` and
induct only on the statement that `tau|I_alpha` is linear.

At a successor, the approximate-unit-net proof for arbitrary extensions
uses the multiplier extension of the already linear restriction.  It splits
`tau` into a linear head supported on `I_alpha` and a quasitracial tail on
`A/I_alpha`.  On the next ideal the tail is a trace precisely because its
restriction factors through the successor quotient.  At a limit ordinal,
simultaneous norm approximation of two self-adjoint elements by one earlier
ideal and norm continuity of the ambient bounded quasitrace prove
additivity.  This works at uncountable cofinality without choosing a
sequence.

## Consequence for the counterexample search

For every continuous ideal filtration of a counterexample to Problem I,
some successor quotient is itself a counterexample.  Thus transfinite
assembly cannot create a quasitrace-additivity defect from linear layers;
the defect must already occur in an indivisible layer of any available
composition analysis.  This is a reduction, not a solution of the
unrestricted problem, because an arbitrary algebra need not admit a
composition series whose successor quotients belong to a known
quasitrace-linear class.
