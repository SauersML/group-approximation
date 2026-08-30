# XCIII residual trace kernel: hereditary-exhaustion audit

## Question

After quotienting the XCIII central sequence algebra by the ideal generated
by all trace-zero Jiang--Su central slices, write

```text
E=D/K_Z^sat,                  R=I/K_Z^sat.
```

Can a sigma-unital or hereditary exhaustion of `R`, combined with the new
extension permanence for bounded quasitraces, force every quasitrace on `E`
to annihilate `R`?

## Exact answer

Such an exhaustion has two logically separate outputs.

First, if every finite residual packet lies in a sigma-unital hereditary
subalgebra on which bounded quasitraces are traces, then every bounded
quasitrace on `R` is a trace.  The quotient `E/R=D/I` is a II_1 factor, so
arbitrary extension permanence makes every bounded quasitrace on `E` a
trace as well.  The absence of a countable approximate unit for `R` is not
a problem: the extension theorem uses a cofinal ultrafilter on an arbitrary
approximate-unit net.

Second, linearity is not annihilation.  A nonzero bounded trace on `R`
extends canonically through `M(R)` to a bounded trace on `E`, and after
normalization gives a negative XCIII witness.  Conversely, once all
quasitraces on `E` are traces, any negative witness restricts to a nonzero
bounded trace on `R`.  Therefore the residual leaf becomes exactly

```text
R has no nonzero bounded trace.
```

Equivalently, `E` must have a unique normalized trace.  This is strictly
stronger than quasitrace-linearity of the hereditary exhaustion.

## Why sigma-unital hereditary pieces are the right local scale

Every finite subset `{x_1,...,x_m}` of a C*-algebra lies in a sigma-unital
hereditary subalgebra.  One may use the hereditary algebra supported by

```text
h=sum_j (x_j*x_j+x_j x_j*).
```

Thus verifying quasitrace-linearity on every sigma-unital hereditary
subalgebra is enough to linearize every bounded quasitrace on the whole
possibly non-sigma-unital residual ideal.  More economical exhaustive
families which contain every finite packet work equally well.

## Exact obstruction to an exhaustion-only proof

The model extension

```text
0 -> (0 direct_sum C) -> (C direct_sum C) -> C -> 0
```

has unique-trace quotient and a residual ideal which is itself
finite-dimensional, hereditary, sigma-unital, and quasitrace-rigid.  The
second coordinate trace nevertheless charges the ideal.  Hence even the
best possible sigma-unital quasitrace-rigid exhaustion cannot force
invisibility without an independent bounded-trace-free input.

## Remaining XCIII tasks

This reduction exposes two concrete questions, either of which can now be
studied with ordinary traces rather than general quasitraces once local
rigidity is established:

1. Are the sigma-unital hereditary subalgebras of `R` quasitrace-rigid (for
   example through exact or quasitrace-rigid ideal filtrations)?
2. Does `R` carry a nonzero bounded trace?

A positive answer to the second question would disprove XCIII immediately.
A negative answer to the second, together with a positive answer to the
first, would prove XCIII.  Neither assertion is made here.
