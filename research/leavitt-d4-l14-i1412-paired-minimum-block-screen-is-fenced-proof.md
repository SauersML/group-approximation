---
rg: 2
id: leavitt-d4-l14-i1412-paired-minimum-block-screen-is-fenced-proof
kind: route
title: Kill the four residual inverse boundaries by the coprime square-cube relations
target: leavitt-d4-l14-i1412-paired-minimum-block-screen-is-fenced
requires:
  - leavitt-d4-l14-i1412-first-carrier-kills-free-survivor
---

The coordinate-preserving paired screen is implemented by
`enumerate-l14-i1412-carrier-pairs.py`; cyclic boundary cuts are implemented
by `enumerate-l14-i1412-boundary.py`.  MSI job `16679319` reports

```text
eq3_substitution_states=458
distinct_transformed_eq1_inputs=223
transformed_eq1_schemes=395
combined_substitution_states=43
combined_abstract_presentations=4
boundary_states=195
nontrivial_q_images=18
cyclic_relator_killed_q_images=14
unresolved_q_images=4.
```

The complete printed list identifies the four non-cyclic-relator cases.
Their target words are

```text
x12^-1 x6^-6 x12,
x2 x6^-6 x2^-1,
x2 x6^-6 x2^-1,
x6^-6.                                                   (I14-10)
```

Every one of the four residual presentations contains the two relators

```text
x6^-2,   x6^-3.                                         (I14-11)
```

Thus `x6^2=x6^3=1`, and consequently

```text
x6=x6^3 (x6^2)^-1=1.                                   (I14-12)
```

Equation `(I14-12)` kills each word in `(I14-10)`.  Together with the
fourteen cases already identified by exact cyclic-relator comparison, this
kills all eighteen syntactically nonempty target images.  Empty target
images are trivial by definition, proving the claim for all 195 boundary
states.

The enumeration begins with globally minimum-block Eq3 schemes and, after
coordinate-preserving substitution, minimum-block Eq1 schemes.  Therefore
the proof does not cover a non-minimal cancellation of either carrier word;
this restriction is part of the statement rather than an inferred global
fence.

