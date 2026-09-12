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

More concretely, the usual increasing matrix algebras in `R` have 2-norm
dense union, but their operator-norm closure is a separable UHF algebra and
is therefore proper in `R`.  Indeed `R` is operator-norm nonseparable: a
diffuse abelian von Neumann subalgebra contains an uncountable family of
projections at pairwise norm distance one.  Thus neither the local theorem
above nor an ordinary sequential inductive-limit argument can be fed the
standard hyperfinite approximation.

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

The stable-algebra vanishing argument is now isolated as
`stw01-stable-algebras-are-bounded-quasitrace-invisible`, so it can be used
without first placing the stable algebra in an extension.  This also supports
an arbitrary transfinite version.  If

```text
0=J_0 subset J_1 subset ... subset J_gamma=J
```

is a continuous increasing ideal filtration and every successor quotient
`J_(alpha+1)/J_alpha` has no nonzero bounded `2`-quasitrace, then `J` has
none.  For a bounded quasitrace `q` on `J`, transfinite induction puts every
`J_alpha` in its closed square-null ideal `N_q`.  At successors, factor
through `J/J_alpha` and use invisibility of the next layer.  At a limit
`lambda`, closedness of `N_q` gives

```text
closure(union_(alpha<lambda) J_alpha) subset N_q.
```

No cofinal sequence is selected, so neither separability nor countable
cofinality is needed.  If `J ideal A`, quasitrace linearity on `A/J` then
passes to `A`.  Stable successor layers and an exact terminal quotient give
the concrete corollary by stable invisibility and Haagerup's theorem.

There is now a complementary transfinite theorem in which the successor
layers need not be quasitrace-invisible.  If every bounded quasitrace on each
successor quotient is a trace, then every bounded quasitrace on the terminal
unital algebra is a trace.  The proof fixes one ambient quasitrace.  At a
successor, the arbitrary approximate-unit net splits it into a linear head
and a quotient tail, whose restriction is linear on the next layer.  At an
arbitrary limit ordinal, norm continuity and the dense union give
additivity.  Hence arbitrary transfinite assembly preserves quasitrace
linearity even when every layer carries nonzero traces.

## Central-projection ideal splitting

The ideal need not be quasitrace-invisible if it is exhausted by projections
central in the ambient algebra.  Suppose

```text
p_n in I intersect Z(A),             p_n increasing, p_n -> 1 strictly on I,
```

every bounded quasitrace on `p_n A` is a trace, and every bounded
quasitrace on `A/I` is a trace.  For an ambient bounded quasitrace `tau`, the
central decomposition `A=p_n A direct_sum (1-p_n)A` gives

```text
tau(x)=tau(p_n x)+tau((1-p_n)x)       (x=x*).
```

The first summand is tracial.  Along a free ultrafilter, the second summands
converge pointwise to

```text
sigma(a)=lim_omega tau((1-p_n)a).
```

This is a bounded `2`-quasitrace because every cut
`a |-> (1-p_n)a` is an actual star homomorphism, including after `M_2`
amplification.  Since `(1-p_n)i -> 0` for `i in I`, its square-null ideal
contains `I`; only at this point is the standard quotient-factorization
lemma applied.  The induced quasitrace on `A/I` is a trace.  The additivity
defect of `tau` equals the complementary defect for every `n`, because the
central-corner defect is zero, and its ultralimit is the defect of `sigma`.
Hence it vanishes.

This permits arbitrary nonzero traces on the ideal corners and is therefore
different from the stable/quasitrace-invisible extension theorem.  It uses
neither exactness nor separability.

The same proof does not apply to a merely quasicentral projectional
approximate unit.  Then

```text
a |-> (1-p_n)a(1-p_n)
```

has multiplicative defect `(1-p_n)a p_n b(1-p_n)`.  Although that defect
tends to zero in operator norm, composition with a quasitrace is not thereby
a quasitrace: its commuting-additivity axiom is exact, and approximate
commutation alone supplies no descent theorem.  Indeed this compression is
a star homomorphism exactly when `p_n` is central.  Thus no quotient
quasitrace is inferred from the general quasicentral cuts.

## Universal quasitrace-null commutators

Exact centrality in `A` can be weakened to exact centrality in every
quasitracial quotient.  Define

```text
J_bQT(A)=intersection_(tau in QT_b(A))
         {x:tau(x*x)=0}.
```

If an ideal has an increasing projectional approximate unit `(p_n)` with
`[p_n,A] subset J_bQT(A)`, every bounded quasitrace on every corner
`p_n A p_n` is a trace, and every bounded quasitrace on `A/I` is a trace,
then every bounded quasitrace on `A` is a trace.

For a fixed ambient quasitrace `tau`, pass first to `A/N_tau`.  The images
of all `p_n` are central there, so the complementary cuts are exact star
homomorphisms.  Their quasitrace compositions have a tail ultralimit which
vanishes on `I`, descends to `A/I`, and is a trace.  The corner term is a
trace by hypothesis, so the ambient additivity defect equals the tail
defect and vanishes.  This order of operations is essential: `tau` itself
need not vanish on `I` and is never descended to `A/I`.

The weakening is strict.  In

```text
A=C direct_sum K~,             I=C direct_sum K,
p_n=(1,e_n),
```

the finite-rank `e_n` make `p_n` noncentral, but their commutators lie in
the stable summand `0 direct_sum K`, which belongs to every bounded
quasitrace square-null ideal.  Meanwhile `I` has the nonzero scalar trace,
so it is not quasitrace-invisible.  The corners are
`C direct_sum M_(rank(e_n))` and the quotient is `C`.

For a projection `p` and fixed `tau`, the tail cut into `A/N_tau` is a star
homomorphism if and only if `[p,A] subset N_tau`.  Thus universal
quasitrace-nullity of these commutators is the exact algebraic threshold for
the tail-homomorphism proof.  It does not show that a merely quasicentral
approximate unit suffices.

## Positive cuts which are projections only quasitracially

The projectional hypothesis is not intrinsic to the argument.  If an ideal
has an increasing positive-contractive approximate unit `(e_n)` with

```text
e_n-e_n^2 in J_bQT(A),             [e_n,A] subset J_bQT(A),
```

then the image of `e_n` in every individual square-null quotient is a central
projection.  The hereditary head term is tracial whenever all bounded
quasitraces on `Her_A(e_n)` are traces, and the complementary central tail
has the same quotient ultralimit as before.  This proves
`stw01-qt-idempotent-approximate-units-preserve-linearity`.

This is strictly broader than projectional splitting.  Let

```text
D=C_0((0,1]) tensor K,
A=C direct_sum D~,                 I=C direct_sum D.
```

The stable algebra `D` is invisible to bounded quasitraces, but it is stably
projectionless: a projection section would have nonempty compact-open support
in the connected noncompact space `(0,1]`.  Hence `I` has no projectional
approximate unit, while it still carries the scalar trace.  The cuts

```text
e_n=(1, min(1,nt) tensor k_n)
```

have universally null commutators and idempotence defects.  Their hereditary
algebras are a scalar summand plus `C_0((0,1]) tensor M_(rank(k_n))`, and the
quotient is scalar.  Thus the positive-cut theorem reaches an extension
covered by neither central/projectional splitting nor whole-ideal
quasitrace invisibility.

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
