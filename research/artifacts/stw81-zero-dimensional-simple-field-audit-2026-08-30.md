---
title: STW LXXXI audit --- zero-dimensional simple fields and the primitive-spectrum firewall (2026-08-30)
---

## Source statement

Problem LXXXI in Schafhauser--Tikuisis--White asks whether a C-star algebra
whose commutative hereditary subalgebras in all quotients have spectra of
dimension at most one must have nuclear dimension `0`, `1`, or `infinity`.
The cached source is `tmp/pdfs/stw99.txt`, lines 3664--3693.  The source
explicitly motivates the question by asking whether finite nuclear
dimension at least two can be detected by any mechanism other than such
commutative shadows.

## New positive class

Let `A` be a separable locally trivial continuous field over a
second-countable zero-dimensional locally compact base `X`, with simple
separable nuclear fibres.  A disjoint clopen refinement of the bundle
charts gives

`A ~= direct_sum_k^(c0) C_0(U_k) tensor B_k`.

Each `C_0(U_k)` is AF, so approximation by finite-dimensional commutative
subalgebras and evaluation at a point give the exact formula

`dim_nuc(A)=sup_x dim_nuc(A_x)`.

Every simple fibre has nuclear dimension `0`, `1`, or `infinity` by the
simple structure theorem, so the same trichotomy holds for `A`.

The shadow hypothesis is automatic and in fact zero-dimensional.  A
commutative hereditary subalgebra is Morita equivalent to the ideal it
generates.  Such an ideal is type I, so it vanishes on every non-type-I
simple-fibre component.  On an elementary-fibre component it is
continuous trace over an open subset of the zero-dimensional base.

This class is not contained in the previously recorded subhomogeneous or
full-AF-by-O-infinity cases: fibre dimensions may be infinite, fibres may
be stably finite or purely infinite, and the ideal lattice may be
infinite.

## Exact primitive-spectrum firewall

The hypothesis cannot control the dimension of the full primitive
spectrum.  For any second-countable locally compact `X`,

`A_X=C_0(X) tensor O_2`

has `Prim(A_X)=X`, no nonzero commutative hereditary subalgebra in any
quotient, and nuclear dimension one.  The last fact is the main theorem of
Bosa--Gabe--Sims--White,
[*The nuclear dimension of O-infinity-stable C-star algebras*](https://arxiv.org/abs/1906.02066),
applied to `A_X`; exactness follows because `A_X` has quotient `O_2` and
therefore is not AF.

Hence even an infinite-dimensional primitive spectrum is compatible with
an empty shadow invariant.  A general proof of LXXXI cannot proceed by
bounding `dim Prim(A)`.  It must distinguish the elementary/type-I locus
from non-type-I fibres and control colour reuse where those strata
accumulate.  The zero-dimensional field theorem succeeds precisely
because clopen refinement removes that boundary-gluing problem.

For context, Thiel,
[*The topological dimension of type I C-star algebras*](https://arxiv.org/abs/1210.4314),
shows that Brown--Pedersen topological dimension is the appropriate
primitive-space invariant inside the type-I category, while explicitly
not identifying it with nuclear dimension in general.  The O2-field
example explains why that type-I topology cannot simply be extended to
the whole primitive spectrum.
