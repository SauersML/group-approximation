# STW XXII: the convergent-sequence fibre gap

## Question tested

Could Problem XXII be reduced to proving the strong equality `J_x=K_x`, or
could the weaker trace-free condition still be genuinely necessary in an
actual nuclear uniform tracial completion?

## Exact model

Take the convergent sequence `X={infinity,1,2,...}`, an infinite-dimensional
UHF algebra `U`, and `A=C(X) tensor U`.  Its trace simplex is Bauer with
extreme boundary `X`, and the completion is the algebra of bounded
`R`-valued sequences converging at infinity in `2`-norm, where `R` is the
hyperfinite II_1 factor.

At infinity, the gap is

```text
{(a_n): ||a_n||_2 -> 0}/{(a_n): ||a_n|| -> 0}.
```

Shrinking projections show that it is nonzero.  Spectral cutoff followed by
arbitrarily many orthogonal copies in each finite-factor coordinate shows
that it has no nonzero bounded positive trace.  A diagonal projection
against any proposed countable approximate identity also shows that the gap
is not sigma-unital.

## Consequence

Even zero-dimensional nuclear Bauer completions need not have equal norm
and `2`-norm fibre ideals.  The trace-free formulation is therefore not
merely a technical weakening: it captures examples that equality misses.
The proof does not establish stability of the gap in the non-sigma-unital
sense, and standard sigma-unital stability tests are unavailable.  Any use
of stability here would require an additional theorem and is unnecessary
for the trace problem.

## Wider boundary

The orthogonal-copy argument works for the full sequential ideal because
all coordinate choices may be made independently.  For a general compact
base, those choices must be realized by continuous bundle sections on a
whole neighbourhood of `x`; this is exactly the continuous-selection or
CPoU gluing issue.  Thus the sequence calculation does not solve the
general Bauer case, but it identifies why a counterexample cannot come
from one shrinking sequence of independent finite-factor coordinates.
