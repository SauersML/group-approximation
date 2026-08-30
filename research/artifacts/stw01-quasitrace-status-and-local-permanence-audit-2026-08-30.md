# STW Problem I: status and local-permanence audit (2026-08-30)

## Current status from primary sources

Problem I remains open.  There is a potentially misleading chronology:

- Alec Gow, *Every 2-quasitrace is a trace*, arXiv:2501.13088 (submitted
  January 2025), claimed a solution.  The arXiv record now marks it withdrawn
  and states the critical gap explicitly.
- Alec Gow, *On the Quasitrace Problem and a Characterization of
  W*-algebras*, arXiv:2601.04431v2 (revised July 2026), again labels
  “Every 2-quasitrace is a trace” as a conjecture, calls Haagerup's exact
  case the best partial result, and acknowledges a gap identified in the
  previous version.  Its theorem is an equivalence between the quasitrace
  conjecture, the assertion that every finite AW*-factor is a von Neumann
  algebra, and a MASA characterization; it is not a proof of the
  conjecture.
- Schafhauser--Tikuisis--White, arXiv:2506.10902v2, whose addenda run through
  April 2026, likewise records Problem I as open.

Accordingly the 2025 preprint is superseded evidence, not a solved-status
input.  The primary-source URLs are
`https://arxiv.org/abs/2501.13088`,
`https://arxiv.org/abs/2601.04431`, and
`https://arxiv.org/abs/2506.10902`.

## Local mechanism audited here

Write `QL(A)` for the assertion that every bounded 2-quasitrace on the
unital C*-algebra `A` is a trace.  The useful elementary observation is that
`QL` is detectable one pair of self-adjoint elements at a time.  Hence it
passes from unital subalgebras which locally approximate finite subsets to
the ambient algebra.  Combining this with quotient permanence gives
permanence under arbitrary unital directed C*-inductive limits, with no
injectivity assumption on the connecting maps.

This does not solve Problem I: an arbitrary nonexact algebra is not known to
have such local models.  It does isolate a precise route by which local or
inductive constructions can avoid an ambient exactness hypothesis.

## Continuity trust boundary

The proof uses only the standard axioms of a bounded 2-quasitrace:
positivity and monotonicity on self-adjoint elements, additivity on commuting
self-adjoint elements, and the usual complexification.  In the unital case
these axioms give the needed norm continuity directly.  If `a,b` are
self-adjoint and `||a-b|| <= delta`, then

```text
b-delta 1 <= a <= b+delta 1.
```

Since `b` commutes with `1`, monotonicity and commuting additivity give

```text
|tau(a)-tau(b)| <= delta tau(1).
```

Thus no unproved extension or uniform exactness assertion is hidden in the
limit argument.

## Relation to Problem X(2)

The hyperfinite `II_1` factor already has no quasitrace-additivity defect:
its normalized quasitrace is its unique normal trace (the classical finite
factor case recalled in STW immediately before Problem I).  Problem X(2)
asks whether that trace/algebra is quasidiagonal.  Consequently X(2) is not
a residual special case of Problem I.  The obstruction is operator-norm
finite-dimensional approximation, not additivity of the dimension
function; hyperfiniteness supplies only strong/2-norm approximation.

## Stable-ideal mechanism

There is also a nonexact extension mechanism.  A bounded 2-quasitrace on a
stable C*-algebra is zero: in `I ~= I tensor K`, arbitrarily many orthogonal
and equivalent diagonal copies of a fixed positive element have uniformly
bounded norm, while commuting additivity would make their quasitrace grow
linearly.  Hence, if `I` is a stable ideal in `A`, every bounded 2-quasitrace
on `A` vanishes on `I` and factors through `A/I`.  If all bounded
2-quasitraces on the quotient are traces, the same holds for `A`.

This is not an exactness argument.  For any separable nonexact C*-algebra
`D`, the unitization

```text
A=(D tensor K)~
```

is separable, unital, and nonexact, but every bounded 2-quasitrace on `A` is
a scalar multiple of the quotient character `A -> C`.  Thus the positive
class contains nonexact algebras with nonzero traces; it is not merely a
vacuous quasitraceless example.

The precise extension principle is slightly more general: stability is used
only to show that the ideal is invisible to bounded quasitraces.  Any ideal
on which every bounded 2-quasitrace is zero has the same transfer property.

## Sharp free-group tensor test

STW, footnote 54, records an exact universal reformulation.  For every
unital `A`, let restriction along the first-factor embedding be

```text
QT_1(A tensor_min C*_r(F_2)) -> QT_1(A).
```

Kaplansky's quasitrace conjecture is equivalent to this map being an affine
homeomorphism for every `A`.  In the positive direction all quasitraces are
traces and the unique trace on `C*_r(F_2)` forces the product extension.  In
the negative direction one passes to a finite AW*-factor carrying a
quasitrace but no trace; Haagerup's proper-infiniteness criterion makes its
tensor product with `C*_r(F_2)` properly infinite and hence removes all
normalized quasitraces.  This gives a concrete tensorial failure certificate,
but it is an equivalence, not a solution.
