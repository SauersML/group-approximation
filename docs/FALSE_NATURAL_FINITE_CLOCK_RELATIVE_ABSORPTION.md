# Natural finite ring quotients absorb the clock Schur class relatively

Date: 2026-08-11

## 1. Outcome

The explicit finite clock class from
`FALSE_SPLIT_SQUARE_ZERO_H2_AMPLIFIER.md` does not survive the relative
Shapiro--Mackey quotient for the natural finite coefficient-ring images of
the Kun--Thom pair.

In those images the positive subgroup is normal and contains the marked
translation `h`.  Hence every double-coset stabilizer contains the full
finite translation subgroup

`H_k=<h> ~= C_(p^(k+1))`.                             `(NRA1)`

The induced map

`H_1(H_k,J_k) -> H_1(B_k,J_k)`                       `(NRA2)`

surjects onto the clock coordinate

`J_k/(c-(1+p))J_k ~= C_(p^k)`.                       `(NRA3)`

Therefore the sum of stabilizer images contains the clock generator, and
the relative curvature class is zero.  This closes the most direct induced-
module globalization of the finite metacyclic clock through finite ring
quotients.

## 2. The subgroup homology map

Put

`q=1+p`, `M=p^k`, `n=p^(k+1)`,

`B_k=<h,c | h^n=c^M=1, c h c^-1=h^q>`,               `(NRA4)`

and

`J_k=Aug_(Z/n)(C_M)`.                                 `(NRA5)`

The subgroup `H_k=<h>` acts trivially on `J_k`, and `nJ_k=0`.  The standard
cyclic-group resolution gives

`H_1(H_k,J_k)=ker(n:J_k->J_k)/(h-1)J_k=J_k`.          `(NRA6)`

The Fox splitting for `(NRA4)` gives the clock projection

`Pi_k:H_1(B_k,J_k) -> J_k/(c-q)J_k`.                 `(NRA7)`

Represent `x in J_k` by the one-cycle `x[h]` for `H_k`.  Under subgroup
inclusion, the same chain is a `B_k` one-cycle.  Its `h`-coordinate is `x`,
so

`Pi_k(i_*(x[h]))=x mod (c-q)J_k`.                    `(NRA8)`

Thus the composite of `(NRA2)` with `(NRA7)` is the canonical quotient map

`J_k -> J_k/(c-q)J_k`.                                `(NRA9)`

It is surjective.  Since the finite clock class maps to a generator of
`(NRA3)`, the image of `(NRA2)` already contains a class with the same clock
coordinate.

## 3. Why every natural stabilizer contains `H_k`

In a finite coefficient-ring quotient, the positive and Laurent coefficient
images coincide.  The finite positive image `A_(+,k)` is consequently normal
in the full finite vertex image `A_k`; this is the calculation in
`FALSE_SQUARE_ZERO_FINITE_RING_QUOTIENT_NO_GO.md`.

The marked translation `h` belongs to the Laurent elementary factor, which
coincides with the positive elementary image after passage to the finite
ring.  Hence

`h in A_(+,k)`.                                       `(NRA10)`

For every double-coset representative `x`, normality gives

`x^(-1) A_(+,k) x=A_(+,k)`.                           `(NRA11)`

Therefore

`B_(k,x)=B_k cap x^(-1)A_(+,k)x`
`       =B_k cap A_(+,k)`                             `(NRA12)`

contains `H_k=<h>`.

## 4. Relative absorption theorem

Let the induced tangent module be

`N_k=Ind_(B_k)^(A_k) J_k`.                            `(NRA13)`

The relative Shapiro--Mackey formula identifies the mixed relative quotient
with

`H_1(B_k,J_k) / sum_x im H_1(B_(k,x),J_k)`.           `(NRA14)`

By `(NRA12)`, every stabilizer image contains the image of `(NRA2)`.  By
`(NRA8)--(NRA9)`, that image surjects onto the clock coordinate.  Hence:

**Theorem 1 (natural-tower relative no-go).**  The finite clock generator
has zero image in the clock-coordinate quotient of `(NRA14)`.  In
particular the canonical character detecting the exact `p^k` clock order
cannot annihilate the positive stabilizer images.

This statement is stronger than bounded depth: the minimum normal-coordinate
depth of the stabilizers is zero, and the entire `C_(p^k)` clock projection is
absorbed at every level.

## 5. Relation to the mod-`p` finite-cycle transgression

This no-go does not contradict the nonzero augmentation transgression in
`FALSE_RADICAL_BS_FINITE_CYCLE_TRANSGRESSION.md`.  That theorem studies the
connecting map associated with the `B`-set augmentation sequence.  The
present theorem studies a second globalization step: inducing the already
constructed coefficient module into a finite vertex and quotienting by the
positive subgroup's mixed homology.  The local transgression is nonzero, but
its induced Schur class is then absorbed by the positive subgroup because
the finite ring image has made `h` positive.

## 6. Computational consequence

Do not compute Schur multipliers for larger natural finite coefficient-ring
quotients in the hope that the clock coordinate survives: the relative
answer is exactly zero at every level.

A live finite model must avoid `(NRA10)`.  It must keep the Laurent fold
translation projectively distinct from the positive image even though no
honest finite ring quotient can do so.  This points back to:

1. genuinely projective finite quotients not induced by a finite ring map;
2. approximate/nonexact vertex models with normalized-HS boundary error; or
3. a different relative Schur class whose stabilizer restriction misses the
   translation coordinate.

The explicit cocycle remains a useful local building block, but the natural
finite ring tower is now rigorously excluded as its relative globalization.

