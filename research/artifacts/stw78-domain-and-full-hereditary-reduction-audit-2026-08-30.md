# STW LXXVIII: domain dichotomy and full-hereditary audit

## Exact problem boundary

Problem LXXVIII asks whether every unital map from a unital simple separable
nuclear `Z`-stable algebra into a unital algebra without normalized
quasitraces is `O_infinity`-stable.  It does not ask whether the map is zero;
nonzero unital maps into quasitraceless targets such as bounded-operator
algebras certainly exist.

## Traceless domains are automatic

For an exact domain, quasitraces are traces.  Rordam's theorem says that a
separable nuclear `Z`-stable traceless algebra is `O_infinity`-stable.  A
central copy of `O_infinity` in the domain sequence algebra pushes through
any unital homomorphism and lands in the sequence relative commutant of the
map.  No property of the target is used.

Therefore the open problem is unchanged if it is restricted to traceful
domains.  Simplicity makes every normalized trace faithful, so this is
exactly the stably finite domain branch.

## Full hereditary image cuts

Every nonzero positive element of a simple domain is full.  Under a unital
map its image remains full in the target.  For a full positive `c in B`,
Morita invariance gives the equivalence

```text
QT(B) nonempty
  iff closure(cBc) has a nonzero bounded 2-quasitrace.
```

The only delicate point is boundedness after extending from the hereditary
algebra.  Fullness and compactness of the unit provide
`[1_B] <= m[h]` for some `h` in the hereditary algebra; Cuntz monotonicity
then bounds the extended quasitrace at `1_B`.

Hence every nonzero positive image cut in an LXXVIII map has a full
hereditary algebra with no nonzero bounded quasitrace.

## Trust boundary

This hereditary conclusion is weaker than pure or strong pure infiniteness.
It does not exclude unbounded lower semicontinuous quasitraces and does not
supply almost-unperforated comparison.  The Toeplitz--Cuntz nonunital-layer
example is not contradicted: its compact ideal is proper and not full in the
unital extension algebra.  No solution of LXXVIII or LXXVII is claimed.
