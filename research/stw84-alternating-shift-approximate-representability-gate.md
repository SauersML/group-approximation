---
rg: 2
id: stw84-alternating-shift-approximate-representability-gate
kind: claim
title: The alternating shift has exact finite-set implementers but coherent stages must cross approximate representability
distinct_from:
  stw84-invariant-coefficient-stages-restore-two-fourier-colours: that theorem assumes uniform near-innerness on a whole finite-dimensional stage; the present theorem tests that assumption on the alternating shift and identifies the exact weaker and stronger gates.
artifacts:
  - research/artifacts/stw84-alternating-shift-coherence-audit-2026-08-30.md
---

Let

```text
K=Alt_fin(Z),       B=C*(K),
alpha(lambda_g)=lambda_(s g s^(-1)),
```

where `s(j)=j+1`.  Then the following hold.

1. **Finite-set covariance holds, even exactly.**  Given a finite
   `F subset B` and `epsilon>0`, there are finite-dimensional unital
   subalgebras

   ```text
   E subset D subset B
   ```

   and `v in U(D)` such that `dist(a,E)<epsilon` for `a in F` and

   ```text
   alpha(e)=v e v^*                 (e in E).          (ASC1)
   ```

   One can take `E=C*(H)` for a finite alternating group, `v=lambda_p`
   for a finitary even permutation extending translation on the support
   of `H`, and `D=C*(<H,p>)`.

2. **The group-stage implementers fail coherence by a fixed amount.**
   Every nontrivial `p in K` satisfies

   ```text
   ||alpha(lambda_p)-lambda_p|| >= sqrt(3).            (ASC2)
   ```

   Consequently no construction using a group-unitary partial-shift
   implementer can satisfy the coherently-inner-stage estimate with error
   less than `sqrt(3)`: testing that estimate on `d=v` already gives the
   contradiction.

3. **Arbitrary coherent stages have a stronger consequence.**  If `alpha`
   has coherently inner finite stages in the sense of
   `stw84-invariant-coefficient-stages-restore-two-fourier-colours`, then
   `alpha` is approximately representable.  Explicitly, for every finite
   `F subset B` and `epsilon>0`, there is `v in U(B)` with

   ```text
   ||alpha(v)-v||<epsilon,
   ||alpha(a)-v a v^*||<epsilon       (a in F).        (ASC3)
   ```

   Thus the unresolved arbitrary-unitary version of the alternating-shift
   stress test is not ordinary approximate innerness.  It is at least the
   approximate-representability problem, equivalently the Rokhlin-property
   problem for the dual circle action on `B rtimes_alpha Z`.

4. A finite-set-only replacement for whole-stage control does not justify
   the Haar-averaging step.  Exact commutation on a prescribed coefficient
   subalgebra can coexist with distance one from the commutant of the
   containing stage.  Finite-set control suffices only when the controlled
   set is a sufficiently fine norm net for the entire unit ball of the
   eventual finite-dimensional stage; that is the original uniform
   hypothesis in finite form.

Therefore the alternating shift passes every coefficientwise/local-inner
test while defeating the natural group-stage coherent implementation by a
uniform gap.  The cyclic core is not closed by finite-set averaging.  The
remaining precise question is whether non-group unitaries can make the
shift approximately representable and, beyond that, whether they can be
placed in finite-dimensional stages with uniform near-innerness.
