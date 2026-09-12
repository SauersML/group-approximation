# RR0 mixed realization: reduction to finite projection-patch amalgamation

Date: 5 September 2026. This is an independently checked reduction,
not a proof of mixed target realization or full LXXVI. It does not
repeat the separate comparison/order-reflection argument.

Let `D` be separable, simple, stably finite, pure, and real rank zero.
Put `E=D tensor Z`, `B=D tensor K`, `F=E tensor K`, and let `phi`
denote first-factor inclusion. Let `X` be a finite CW complex.
The same reductions work for compact metrizable `X` whenever the
available all-base V theorem is used.

## 1. The target coefficient also has real rank zero

The coefficient first-factor map induces `Cu(D) ~= Cu(E)`. Lin's
theorem gives stable rank one on both coefficient algebras. Since
`D` has real rank zero, every element of `Cu(D)` is an increasing
supremum of compact elements. This property transfers through the
Cu isomorphism. Coward--Elliott--Ivanescu, Corollary 5, now gives
real rank zero of `E` (and hence of `F`).

The primary statement is on manuscript pages 33--36 of
<https://arxiv.org/pdf/0705.0341>. Its stable-rank-one hypothesis
is present here. No assertion that `C(X,E)` has real rank zero is
made or needed.

## 2. Every target cutoff has a finite projection-patch sandwich

**Proposition.** Let `b in C(X,F)_+` be a contraction and let
`epsilon>0`. There exist a finite open cover `U_i`, continuous
projection fields `q_i:U_i->F` with
`q_i(x) in Her(b(x))`, and nonnegative continuous functions `f_i`
with `sum f_i=1` and `supp(f_i) subset U_i`, such that the section

`d = sum_i f_i q_i`,

where each summand is extended by zero, satisfies

`[(b-epsilon)_+] <= [d] <= [b]` in `Cu(C(X,E))`.        (1)

Zero projection patches are allowed where `b` is small.

**Proof.** Fix `eta` with `0<eta<epsilon`. At a point `x_0`, choose
a projection `q in Her(b(x_0))` with

`||(1-q)b(x_0)^(1/2)|| < eta/4`.

Real rank zero gives such a projection. Because
`q in closure(b(x_0)F)`, choose `e in F` with
`||b(x_0)e q-q||` as small as desired. On a neighborhood of
`x_0`, the corner element

`q e* b(x)^2 e q`

is invertible in `qFq`. Thus

`w(x)=b(x)e q (q e* b(x)^2 e q)^(-1/2)`

is a continuous partial isometry with `w(x)*w(x)=q`.
Its range projection `q_(x_0)(x)=w(x)w(x)*` belongs to
`Her(b(x))`. By choosing the first approximation sufficiently
close and shrinking the neighborhood, it satisfies

`||(1-q_(x_0)(x)) b(x)^(1/2)|| < eta`.                (2)

When `q=0`, simply use the zero projection on a neighborhood where
`||b(x)^(1/2)||<eta`; the initial cutoff choice can be made with
a smaller tolerance to ensure this case has that neighborhood.

Compactness gives finitely many such neighborhoods and a subordinate
partition of unity with support compactly contained in the chosen
neighborhoods. The section `d` is a positive contraction. Equation
(2) implies

`||(1-d)b^(1/2)|| <= sum_i f_i ||(1-q_i)b^(1/2)|| < eta`.

Consequently `c=b^(1/2)d b^(1/2)` satisfies `||b-c||<eta`.
The standard cutoff comparison gives `(b-epsilon)_+ precsim c`.
Writing `t=d^(1/2)b^(1/2)`, we have `c=t*t`, while
`tt*=d^(1/2)b d^(1/2)<=d`; therefore `[c]<=[d]`.

Finally each summand `f_iq_i` lies globally in `Her(b)`. This can
be checked by functional-calculus approximate units of `Her(b)`:
pointwise convergence on the section is uniform by compactness
(or Dini applied to the corresponding decreasing norm errors).
Thus `d in Her(b)` and `[d]<=[b]`, proving (1). QED.

In particular, given `y'<<y=[b]`, choose `epsilon` so that
`y'<=[(b-epsilon)_+]`. It remains only to realize an intermediate
class for the finite sum `d` in (1).

## 3. Every individual patch is already in the actual image

Set `K_i=supp(f_i)`, a compact subset of `U_i`. The all-base V
isomorphism supplies a source projection
`p_i in C(K_i,B)` and a continuous target partial isometry
`v_i in C(K_i,F)` with

`v_i*v_i=phi(p_i)`, `v_i v_i*=q_i|K_i`.

Define `a_i=f_i p_i` on `K_i` and zero elsewhere. This is a
continuous source positive section: at the boundary of `K_i`,
the scalar `f_i` tends to zero and the projection norm is bounded.
There is no need to extend the projection itself over all of `X`.
Similarly `z_i=sqrt(f_i) v_i`, extended by zero, is continuous.
Then

`z_i*z_i=phi(a_i)`, `z_i z_i*=f_iq_i`.

Hence `Cu(phi)([a_i])=[f_iq_i]` exactly. This already realizes
positive sections which are scalar cutoffs of a projection bundle
on an arbitrary compact part of the base.

The conclusion for each summand cannot be added as an equality for
the ordinary positive sum `d`. Cu addition represents orthogonal
direct sum, whereas the ranges of the target `q_i` overlap.

## 4. The exact finite amalgamation lemma still required

The following concrete lemma would finish target realization when
combined with the independently proved order reflection. It is
**unproved** here.

> **Finite-frame Gram descent.** Let `K_1,...,K_s` be compact
> subsets of `X`, let `f_i>=0` be continuous scalar functions
> with `supp(f_i) subset K_i`, and let `p_i in C(K_i,B)` be
> projections. Suppose `v_i in C(K_i,F)` are partial isometries
> with `v_i*v_i=phi(p_i)`. Put
> `z_i=sqrt(f_i)v_i`, extending by zero, and
> `d=sum_i z_i z_i*`. Then `[d]` belongs to the range of
> `Cu(phi):Cu(C(X,D))->Cu(C(X,E))`.

With the data from Sections 2--3 this would give a source `a` with
`y'<=phi[a]=[d]<=y`, the requested hereditary sandwich. Applying
it successively to a rapidly increasing sequence and using order
reflection would produce full surjectivity.

Equivalently, form the finite row `T=(z_1,...,z_s)`. Its Gram
matrix `G=T*T` has entries

`G_ij=sqrt(f_i f_j) v_i* v_j`.

Its diagonal entries are exactly the source images `phi(a_i)`,
and `[G]=[TT*]=[d]`. The missing statement descends its Cu class
while retaining the relations among the off-diagonal entries.
No approximate coefficient lift for those entries follows from
the first-factor map; it is not a norm-dense map.

## 5. What the new strict embedding theorem does and does not give

For source coefficient projections `p,q`, extension of scalars on
the actual spaces of embeddings is already a weak homotopy
equivalence whenever these spaces are nonempty. If `[p]<[q]`,
both spaces are weakly contractible by the proper-Stiefel result.
If `[p]=[q]`, cancellation identifies the embedding spaces with
the corresponding corner unitary groups, and their first-factor
map is a weak homotopy equivalence by corner K-stability. A
projection cannot embed when its Cu class is not below the other
one; coefficient order reflection matches that condition.

This is strong evidence for coherent projection-module descent,
and the strict relative positive embedding theorem supplies exact
boundary extension once the source and target modules have been
specified. It does not by itself descend the configuration formed
by several overlapping ranges. Such a configuration includes the
module of their sum and its changing compact strata; assuming
that this module already comes from the source would be circular.

The elementary fixed-fiber example makes the distinction explicit.
Two rank-one projections can each have the same V class while
their positive sum has support of rank one (equal ranges) or two
(orthogonal ranges). The individual projection classes do not
record which sum is intended. This example is not a counterexample
to finite-frame Gram descent; it rules out proving the lemma by
adding the separate patch lifts without controlling their overlap.

The bounded progress here is target RR0, the finite projection-patch
sandwich (1), and exact realization of every individual localized
patch. Coherent realization of the finite Gram matrix remains the
explicit missing step. No new Cairn closure claim is made.

## Inputs

- Coward--Elliott--Ivanescu, Corollary 5:
  <https://arxiv.org/pdf/0705.0341>.
- The reviewed all-base V theorem:
  `stw99-lxxvi-all-base-compact-k-stability-audit-2026-09-05.md`.
- The reviewed strict relative positive embedding theorem:
  `stw99-lxxvi-rr0-cutoff-relative-selection-audit-2026-09-05.md`.

The RR0 transfer is a direct prior-art consequence. The finite local
projection/polar transport and cutoff comparison use standard
operator-algebra constructions; their precise assembly above is
written out to isolate the remaining realization assertion.
