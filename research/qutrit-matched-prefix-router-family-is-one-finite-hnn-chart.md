---
rg: 2
id: qutrit-matched-prefix-router-family-is-one-finite-hnn-chart
kind: claim
title: Every matched Leavitt qutrit router family lies in one finite HNN chart
artifacts:
  - research/qutrit-matched-prefix-router-flow-firewall-proof.md
distinct_from:
  qutrit-full-leavitt-prefix-conjugator-realizes-phase-star: that constructs one positive central-line-to-leaf-line selector; this classifies the entire family obtained by reusing its rectangular prefix equivalence.
  qutrit-jacobson-central-line-twist-is-similarity-impossible: that forbids even one selector in the augmented one-sided chart; this shows why arbitrarily many selectors exist in the full chart but still do not close a Hall cycle.
  qutrit-line-hnn-router-has-full-source-but-coincident-range: that is an abstract one-line HNN router; this proves that the natural finite atlas of explicit Leavitt matrices has exactly the same finite-edge HNN firewall.
---

For every `(r,s) in F_3 times F_3^x` put

```text
h_(r,s)=J^r Z^s.
```

Each `h_(r,s)` has six three-cycles and a `16`-dimensional fixed
space over `F_2`. Reuse the rectangular prefix equivalence from
[[qutrit-full-leavitt-prefix-conjugator-realizes-phase-star]] to obtain
explicit matrices

```text
g_(r,s) J g_(r,s)^(-1)=h_(r,s).
```

The scalar normal-form changes can be chosen coherently so that, after
fixing one base pair `(r_0,s_0)`,

```text
g_(r,s)=B_(r,s) g_(r_0,s_0),
B_(r,s) in K:=GL_28(F_2).                               (QMF1)
```

Consequently every pair ratio is scalar:

```text
g_(r,s)g_(r',s')^(-1)=B_(r,s)B_(r',s')^(-1) in K.       (QMF2)
```

Thus every finite support cycle made from the matched atlas is a
potential cycle inside the finite group `K`. No such ratio is a
non-scalar Leavitt root or a normal-generating infinite coefficient
element.

This also has an exact nonnegative-flow formulation. For joint
`C=<J,Z>` character weights `w_(a,b)>=0`, the conjugacy by
`g_(r,s)` imposes, for every `p in F_3`,

```text
sum_b w_(p,b) = sum_(ra+sb=p) w_(a,b).                  (QMF3)
```

For every finite or infinite choice of target lines, the uniform vector

```text
w_(a,b)=1/9
```

solves all equations simultaneously. Hence no finite family of these
line-conjugacy rank inequalities can force the active `J=omega` sector
to vanish. The canonical qutrit weight vector is itself a stationary
point.

More strongly, `<K,g_(r_0,s_0)>` is a quotient of the single HNN group

```text
<K,U | U J U^(-1)=h_(r_0,s_0)>.                         (QMF4)
```

Its edge group is cyclic of order three, hence amenable, and all the
other matched routers are the words `B_(r,s)U`. The HNN cover is
hyperlinear and has exact finite-dimensional regular packet models with
the uniform weights above. Therefore neither adding all matched routers,
nor imposing their scalar pair-ratio and telescoping-cycle relations,
turns the phase star into a normalized-Hilbert--Schmidt obstruction.

This is a firewall only for the matched prefix atlas and its
character-weight inequalities. The concrete matrix quotient may have
additional relations. The first eligible continuation must use two
inequivalent rectangular prefix equivalences. Their relative element
centralizes a leaf line but need not lie in `K`; one must test whether
that non-scalar centralizer element returns the leaked qutrit mass or
again admits a stationary multiplicity model.
