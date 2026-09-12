# Exact two-patch realization with a controlled angle remainder

Date: 5 September 2026. This proves an exact mixed-class case of the
finite projection-patch realization problem. It does not establish
unrestricted Gram descent or full LXXVI.

Let `D` be separable, simple, stably finite, pure, and real rank zero,
let `E=D tensor Z`, and let `X` be compact metrizable. Write
`B=D tensor K`, `F=E tensor K`, and `phi:B->F` for first-factor
inclusion. We use the already established soft Cu isomorphism for
`C(X,D)->C(X,E)` and its all-compact-subset V isomorphisms.

## 1. The two-patch hypothesis

Let `f_1,f_2:X->[0,1]` be continuous, let `K_i=supp(f_i)`, and
let `q_i` be continuous target projection fields on neighborhoods
of `K_i`. Extend `f_i q_i` by zero and set

`d=f_1 q_1+f_2 q_2`.

Assume only the following relation between the scalar supports:

`U_2={f_2>0} subset U_1={f_1>0}`.                     (1)

The projections need not commute, and their ranges need not be
orthogonal or comparable. There is no positive uniform lower bound
on `f_1`, even on `U_2`. Since `K_2 subset K_1`, the expression

`c=f_2(1-q_1)q_2(1-q_1)` on `K_2`,

extended by zero, is a continuous positive target section. The
symbols `1-q_1` are taken in the multiplier algebra if necessary.

**Proposition 1 (exact module decomposition).** Under (1),

`[d]=[f_1q_1]+[c]` in `Cu(C(X,E))`.                  (2)

**Proof.** Work first in the ideal `I=C_0(U_1,F)`. The field `q_1`
is a projection in `M(I)`. The scalar function `f_1` is strictly
positive on `U_1`, so

`H_(f_1q_1)=q_1 I`.

This assertion concerns the closed Hilbert module; it does not
assert invertibility of `f_1` in a unitization. Put
`t=sqrt(f_2)q_2`, extended by zero. Assumption (1) ensures `t in I`.
The standard range-module identities for positive sums give

`H_d=closure(q_1 I+t I)`.

For completeness, the closure of the range of a row `(a,b)` is
the closed sum of the closures of the ranges of `a` and `b`, and
equals the range module of `aa*+bb*`; use
`a=sqrt(f_1)q_1` and `b=t`.

Because `q_1 I` is complemented, the displayed closed sum splits
orthogonally as

`q_1 I direct_sum closure((1-q_1)t I)`.

Both inclusions follow directly from
`t=q_1t+(1-q_1)t`; multiplication by `q_1` preserves `I`.
The second summand is `H_c`, since
`((1-q_1)t)((1-q_1)t)*=c`. Thus the modules are actually
isomorphic, not just pointwise Cu-equivalent. Passing to Cu and
then including the ideal into `C(X,F)` proves (2). QED.

This is the correct nonorthogonal correction term. Replacing `c`
by `f_2q_2` would in general double-count the overlap.

## 2. Exact realization in two substantial cases

**Theorem.** Under the hypotheses of Proposition 1, `[d]` belongs
to the actual first-factor Cu image if either condition holds:

1. `c` is functionally soft in `Cu(C(X,E))`; a sufficient explicit
   condition is that every nonzero `c(x)` has spectrum accumulating
   at zero.
2. The angle compression
   `a(x)=(1-q_1(x))q_2(x)(1-q_1(x))`, `x in K_2`, has a uniform
   spectral gap at zero: for some `delta>0`,
   `spec(a(x)) subset {0} union [delta,1]` for every `x in K_2`.

In particular, in either case every prescribed `y'<<[d]` has a
source class `w` with `y'<=Cu(phi)(w)=[d]`. If `[d]<=y` in a
larger target hereditary sandwich, this same `w` lies between
`y'` and `y`.

**Proof.** The all-base V isomorphism on `K_1` gives a source
projection `p_1` and target partial isometry `v_1` with
`v_1*v_1=phi(p_1)` and `v_1v_1*=q_1`. Multiplication by
`sqrt(f_1)`, and extension by zero, show that the source section
`a_1=f_1p_1` satisfies

`Cu(phi)([a_1])=[f_1q_1]`.

In case 1 the already proved soft isomorphism gives a source class
`w_c` with `Cu(phi)(w_c)=[c]`. Then
`w=[a_1]+w_c` has image `[d]` by (2).

To verify the stated pointwise sufficient condition, recall the
established softness criterion for these residually stably finite
section algebras: a nonsoft positive class has a nonzero compact
restriction to some closed subset. A nonzero such restriction has
a nonzero fiber. Evaluation preserves compactness, while a positive
element in a stably finite coefficient has compact Cu class only
when zero is isolated in its spectrum. This contradicts the
pointwise condition. Thus the condition implies softness globally;
it is not an assumption that pointwise Cu order determines all
mixed classes.

In case 2, continuous functional calculus gives a continuous
projection field `r=1_(0,infinity)(a)` on `K_2`. The uniform gap
ensures continuity, including at points where `a=0`. We have

`delta f_2 r <= c <= f_2 r`.

These inequalities show `[c]=[f_2r]`. Lift `r` by the V
isomorphism on `K_2`, and multiply its source lift by `f_2`;
the same zero-extension/partial-isometry argument as for `a_1`
gives a source class `w_c` with the required image. Equation (2)
again finishes the proof. QED.

Case 2 permits the scalar weight `f_2` to vanish. Thus it covers
localized projection remainders which are globally noncompact; it
is stronger than requiring the positive section `c` itself to have
a uniform spectral gap.

## 3. A genuinely nonorthogonal family covered by case 1

For an illustration, work in a nonzero unital projection corner
with unit `e`, and let `s(x)` be any continuous family of positive
contractions in its target corner. The block matrices

`q_1 = diag(e,0)`,

`q_2 = [[e-s, sqrt(s(e-s))], [sqrt(s(e-s)), s]]`

are projections. Their ranges are generally neither orthogonal
nor equal, and the coefficients `s(x)` need not come from the
source algebra. The angle remainder of Proposition 1 is exactly

`c=diag(0,f_2 s)`.

If each nonzero `s(x)` has spectrum accumulating at zero, case 1
applies for arbitrary nested scalar supports as in (1). The exact
target class is realized without lifting the off-diagonal entry
`sqrt(s(e-s))` in norm. The soft theorem lifts the remainder's Cu
class, while the module decomposition preserves the entire overlap
contribution.

## 4. A transverse case with nonnested scalar supports

The nesting assumption can also be removed in a concrete transverse
case. Let `K=K_1 union K_2`, and suppose the first projection extends
to a continuous projection `p` on a neighborhood of `K`. On `K_2`
assume, for some `delta>0`,

`p q_2 p >= delta p`.                                (3)

There is no assumption that `p<=q_2`; (3) permits a nonzero angle
between the two ranges. Put

`d=f_1p+f_2q_2`, `h=f_1+f_2`, `U={h>0}`.

On `U`, the positive corner element `pdp` is invertible in `pFp`,
since `pdp>=min(1,delta) h p`. Define

`w=d^(1/2)p (pdp)^(-1/2)`, `r=w w*`.

These are continuous bounded multiplier sections over `U` and
`w*w=p`. Their norms are controlled even if `h` tends to zero:
equivalently compute the same formula using `d/h` in place of `d`,
whose compression is bounded below by `min(1,delta)p`.

Set `c_r=(1-r)d(1-r)` on `U`, extending it by zero outside `U`.
It is continuous because `||c_r(x)||<=||d(x)||<=h(x)`. There is
the exact identity

`[d]=[hp]+[c_r]`.                                    (4)

To prove it, let `I=C_0(U,F)`. The columns `w` embed `pI` into
`H_d`. Pointwise hereditary membership gives global membership
after multiplying by any element of `I`: on compact subsets of
`U` it follows uniformly from the displayed normalized formula;
outside such a compact subset the multiplying element is small.
Thus `rI subset H_d`, and `r` restricts to an adjointable
projection on `H_d`. Its complementary module is `H_(c_r)`.
The column `w` identifies `rI` with `pI=H_(hp)`, proving (4).
Equivalently `sqrt(h)w`, extended by zero, implements the Cuntz
equivalence between the two localized projection summands.

The V theorem on the compact set `K` realizes `[hp]` in the
source. Therefore, whenever `[c_r]` is soft, the soft theorem
and (4) realize `[d]` exactly. The same pointwise sufficient
condition as in Section 2 applies to `c_r`. Neither scalar
support has to contain the other. No lift of the coefficients of
`w` through the first-factor inclusion is asserted or required.

For example, for the block projections in Section 3, (3) holds
whenever `s<= (1-delta)e`. The transverse statement therefore
allows arbitrary scalar supports for such angles, provided its
computed complementary section `c_r` is soft. The latter condition
is separate and has not been inferred merely from transversality.

## 5. Exact remaining boundary

These arguments do not cover arbitrary two-patch data. Sections
1--3 use a first patch whose nonzero set contains that of the
second, so that its projection splits the whole relevant range
module. Section 4 replaces nesting by the uniform transverse
condition (3), which constructs a different splitting projection.
Without either hypothesis such a splitting has not been supplied.

Even with nested supports, the remainder `c` may have both soft
fibers and compact restriction strata with a closing angle gap.
The theorem does not realize that arbitrary mixed remainder.
The algebraic identity (2) still holds, but invoking the soft
isomorphism for a nonsoft remainder would be invalid. The next
two-patch difficulty is precisely this variable mixed angle
remainder, together with gluing for nonnested scalar supports
outside the transverse case of Section 4.

The result is an exact positive case of the finite-frame Gram
descent task, not an unrestricted two-patch theorem or a named
open-problem resolution.

## Dependencies

- `stw99-lxxvi-rr0-finite-projection-patch-realization-2026-09-05.md`:
  localized projection lifts and the general finite Gram task.
- `stw99-lxxvi-soft-realification-surjectivity-audit-2026-09-05.md`:
  the specified soft first-factor isomorphism and softness criterion.
- `stw99-lxxvi-all-base-compact-k-stability-audit-2026-09-05.md`:
  V isomorphisms on the compact sets `K_i`.

The range-module decomposition is elementary Hilbert-module algebra.
The new content recorded here is its exact application to two
nonorthogonal localized patches, including vanishing scalar weights
and the two verified classes of remainder.
