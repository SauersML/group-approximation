---
rg: 2
id: stw77-type-i-von-neumann-targets-solve-map-proof
kind: route
title: Pass to essential type-I fibres and select absorbers measurably
target: stw77-type-i-von-neumann-targets-solve-map
requires:
  - stw77-bounded-operator-target-case
  - oinfty-map-stability-is-central-isometry-splitting
---

Use the standard direct-integral form

```text
M=integral_X^direct B(H_x) d mu(x),
phi=integral_X^direct phi_x d mu(x).
```

The fibres are separable. Since `phi(1)=1_M` is properly infinite,
finite-dimensional fibres occur only on a null set.

We first show that `phi_x` is an essential representation for almost every
`x`. Let `(a_n)` be a norm-dense sequence in the positive unit ball of
`A`. If `phi_x` is not essential, some positive contraction `a` has
`phi_x(a)` nonzero and compact. Approximating `a` by an `a_n` shows that
there is a positive rational `r` such that

```text
||phi_x(a_n)||>r
and
||phi_x(a_n)||_ess<r.
```

Conversely, these two inequalities imply that
`(phi_x(a_n)-r)_+` is nonzero and finite rank: the spectrum above `r` is
finite because the essential norm is below `r`. The norm and essential norm of a
measurable operator field are measurable, so the nonessential fibres are a
countable union of the measurable sets defined by these inequalities.

If the nonessential fibres had positive measure, one fixed pair `(n,r)`
would work on a positive-measure set. Put `c=(a_n-r)_+`. Then `phi(c)` is
nonzero, while `phi_x(c)` is a nonzero finite-rank positive operator on that
positive-measure set. This contradicts proper infiniteness of `phi(c)`:
proper-infiniteness witnesses in the direct integral evaluate to witnesses
in almost every fibre, whereas a nonzero finite-rank positive operator in
`B(H_x)` is not properly infinite. Hence `phi_x` is essential almost
everywhere.

For an essential representation into `B(H_x)`, every nonzero positive image
operator is noncompact and therefore properly infinite. The
bounded-operator target theorem now applies to almost every `phi_x`.

Fix a finite set `F subset A` and `epsilon>0`. For almost every `x`, let
`S_x` be the set of pairs of contractions `(s_1,s_2)` satisfying

```text
s_i^*s_j=delta_(i,j)1
and
max_(a in F,i=1,2)||[s_i,phi_x(a)]|| <= epsilon/2.
```

Each `S_x` is nonempty by the bounded-operator theorem. On the strong-star
unit ball of `B(H_x)^2` it is closed, and its graph is measurable: the
isometry equations are tested on a countable dense set of vectors, while the
commutator norm is the supremum over such a set. The standard measurable
selection theorem therefore gives measurable fields
`x |->(s_1(x),s_2(x)) in S_x`.

The resulting `s_1,s_2 in M` are exact isometries with orthogonal ranges,
and

```text
max_(a in F,i=1,2)||[s_i,phi(a)]||
 = max_(a in F,i=1,2) ess_sup_x
   ||[s_i(x),phi_x(a)]||
 <= epsilon/2 < epsilon.
```

Thus every finite-set centralization defect vanishes. The central-isometry
criterion proves that `phi` is O-infinity-stable.
