---
rg: 2
id: disjoint-private-pairs-expand-the-full-exterior-square
kind: claim
title: Degree-one private pairs uniformly detect the full exterior square
distinct_from:
  radial-parallelograms-kill-simplex-class-two: that uses one algebraic orbit over the entire exponential simplex table; this uses only disjoint pairs among O(r squared) selected random labels.
  positive-rate-tanner-tests-have-contextual-models: that gives a class-two escape when too few jointness directions are tested; this shows the private-label budget is large enough to test every direction with constant degree.
---

There is a universal `C` such that for every sufficiently large `r` one can
choose `2M<=C r^2` labels `v_1,...,v_(2M) in F_2^r`, paired disjointly, so
that every nonzero alternating form `beta` on `F_2^r` obeys

```text
(1/M)|{t:beta(v_(2t-1),v_(2t))=1}| >=1/4.                (DPE1)
```

Thus the degree-one commutation overlay consisting of these `M` pair
contexts spans the whole `Lambda^2(F_2^r)` and has a uniform signed gap.
Each selected coordinate occurs in at most one added context.

For any exact local reflection presentation whose scalar abelianization is
the corresponding character code, adjoining these pairwise joint-PVM views
kills every central class-two commutator twist.  Its maximal class-two
quotient is abelian.  This uses only `O(r^2)` bounded-arity checks, so the
exterior-square obstruction does not refute the selected-label architecture.
The remaining possible exact contextual quotient is genuinely nonnilpotent,
as in the radial-simplex audit.
