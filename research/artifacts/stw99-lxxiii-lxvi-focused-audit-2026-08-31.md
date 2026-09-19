# STW LXXIII/LXVI focused attack — 2026-08-31

## Verdict

Neither root is promoted.

* Global Glimm / Problem LXXIII remains **OPEN**, but its exact finite-packet
  fusion step is now proved for laminar packet ideals and hence for algebras
  with laminar closed ideal lattice.
* Problem LXVI remains **OPEN**.  A new simple conical-monoid model proves
  that the coherent dyadic chain and every currently recorded order-theoretic
  obstruction are mutually consistent.  The remaining issue is C-star
  realizability, not a contradiction among the `V`-monoid equations.

## LXXIII: support-preserving destabilization for laminar packets

Let `x_1,...,x_n` be square-zero and `I_i=Ideal(x_i)`.  Assume every pair of
packet ideals is comparable or has zero intersection.  Retain one generator
from each distinct maximal packet ideal.  Distinct retained ideals are
incomparable and therefore orthogonal.  For their sum `x`,

```text
x^2=0,
x*x=sum_i x_i*x_i,
Ideal(x)=sum_i Ideal(x_i*x_i)=sum_i I_i.
```

This is exact intrinsic fusion: no matrix stabilization, perturbation, or
spectral-gap loss.  Composing it with the established finite primitive-ideal
packet theorem proves Global Glimm for every algebra without nonzero
finite-dimensional representations whose ideal lattice satisfies

```text
I subset J,  or J subset I,  or I intersect J=0.
```

This strictly extends the previously recorded chain-ideal case.  It also
sharpens the general obstruction: a failed packet must contain overlapping
incomparable generated ideals.  Merely having several maximal packet ideals
is harmless when their supports are disjoint.

## LXVI: the projection-monoid equations do not contradict one another

Let

```text
M=Z[1/2] intersect [0,1],        r plus s=min(1,r+s).
```

This is a countable simple conical commutative monoid.  Its order unit `u=1`
is properly infinite, while `p=1/2` is finite.  The elements

```text
x_n=2^(-(n+1))
```

satisfy `x_0=p` and `x_n=2x_(n+1)` for all `n`.  Every `x_n` is finite and
full.  The least `m_n` with `u<=m_n x_n` is exactly

```text
m_n=2^(n+1)>2^n,
```

and `m_n x_n=u` while `u not<=x_n`.  Thus the model sharply realizes the
comparison pattern proved necessary by
`stw99-lxvi-car-forces-unbounded-cu-perforation`.

No C-star realization is claimed.  The model instead closes a proposed
negative route: the coherent dyadic `V`-chain cannot be ruled out using only
conicality, simplicity, finiteness of the seed, proper infiniteness of the
unit, or the known unbounded comparison coefficients.  A successful no-go
must add a genuine C-star realizability axiom; a successful construction must
realize this saturated dyadic order without the analytic rank-growth failures
of the Rordam designs.
