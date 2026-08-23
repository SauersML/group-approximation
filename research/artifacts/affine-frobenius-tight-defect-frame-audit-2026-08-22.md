# Affine--Frobenius tight-defect frame audit

**Date:** 2026-08-22

## Outcome

The cubic route was not closed, but its proposed frame mechanisms can now
be classified exactly.

For reducing incidence masks put

```text
e_i=(1-A_i)/2,
r_i=e_iq_i,
D_i=(1-A_i)q_i=2r_i.
```

After shared-involution compatibility, the `r_i` are precisely the negative
pieces of the masks inside the canonical interpolation carrier.  For
positive weights `w_i`, the cubic equation

```text
D_wD_w^*D_w=lambda D_w
```

is equivalent to

```text
sum_i w_i r_i=(lambda/4)(join_i r_i).
```

Thus it is exactly a weighted tight fusion-frame equation.

## Consequences for the attempted constructions

1. **Column repetition.** Repeating column `i` only replaces `w_i` by an
   integer.  It introduces no new range direction.  For two nonzero
   incidence projections, positive weighting works only if they are equal
   or orthogonal.
2. **External Weyl/ETF frame.** If the external orbit attached to incidence
   `i` sums to `c_iI`, the enlarged frame operator is
   `(sum_i c_ir_i) tensor I`.  Hence the external construction only performs
   scalar column weighting and cannot flatten the internal spectrum.
3. **Universal Julia/polynomial padding.** A finite polynomial complement
   would imply on scalar spectra
   `t+sum_j |f_j(t)|^2=lambda` on an interval.  A sum of polynomial squares
   cannot equal the decreasing affine function `lambda-t`.  Functional
   calculus or an input-specific algebraic spectral relation is essential.
4. **Internal equal-angle frames.** These exist abstractly, but the intended
   high-density masks rule out a nontrivial one.  If `p=join_i r_i` and the
   frame is tight, either all `r_i=p`, or the deleted pieces
   `p-r_i=p(1-q_i)` cover `p`.  Therefore

   ```text
   either r_i=p for every i,
   or tau(p)<=sum_i tau(1-q_i).
   ```

   At the strict Frobenius scale the second alternative is impossible.  For
   `r` deficits `1/P` and an oriented marginal with negative mass at least
   `1/2`, it is impossible once `P>2(r+1)`.

## Sharp remaining construction

In the regime relevant to the rowwise BCS gap, a successful cubic packet
must therefore construct one algebraic projection `p_x` satisfying

```text
e_(c,x)q_(c,x)=p_x
```

for every occurrence of `x`.  The cubic is then automatic.  This is a
common negative carrier, not a distributed fusion frame.

This does not refute the route: such a common finite-support carrier would
solve the projection CRT and make major progress toward the non-hyperlinear
group.  It does refute the hope that repetition, an external Weyl frame, or
a universal algebraic Julia dilation supplies an easier generic route to
it.  A viable construction must correlate the packet interiors themselves
or impose an input-specific algebraic spectral identity.  In particular it
must cross the existing non-Bass--Serre/global-BCS compatibility firewall;
external stabilization alone cannot do so.

## Cairn entries

- `tight-defect-cubic-is-weighted-fusion-frame`
- `high-density-tight-defect-frame-collapses-to-common-carrier`
- `external-weyl-tightening-is-only-column-weighting`
- `polynomial-julia-padding-cannot-flatten-spectrum`
