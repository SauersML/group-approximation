---
rg: 2
id: projective-incidence-characters-give-regular-factors
kind: route
title: Cancel the two marked subgroup characters using projective points and incidence cycles
target: leavitt-first-relation-has-a-4608-dimensional-seed
requires:
  - leavitt-24k-first-relation-has-exact-finite-model
artifacts:
  - research/artifacts/leavitt-4608-projective-incidence-seed-2026-09-08.md
---

The prerequisite supplies the `F_8` coefficient assignment and the
first-relation identity. On the projective plane it gives 73 points,
73 lines, and 657 incident pairs. The bipartite incidence graph is
connected, so its complex cycle space `J` has dimension
`657-146+1=512` and character
`chi_J=chi_flags-chi_points-chi_lines+1`.

A nonidentity root transvection fixes nine points, nine lines,
and seventeen flags. Both `c` and `c^2` fix one point and one
line, which are nonincident, so they fix no flags. Thus the
72-dimensional point augmentation `V` has character eight on
the nonidentity root group and zero on `c,c^2`, while `J`
has the respective values zero and minus one.

The identity `chi_(Lambda^2 V)(g)=(chi_V(g)^2-chi_V(g^2))/2`
gives minus four on a root involution and zero on `c,c^2`.
Therefore `Lambda^2 V direct-sum 4(J direct-sum 1)` has
trace zero on every nonidentity element of both marked finite
subgroups. Its dimension is 4608, so finite abelian character
orthogonality gives the asserted regular multiplicities and
the frozen `24k` form at `k=192`. The point-only alternative
`V direct-sum 2 Lambda^2 V` has dimension 5184 and the same
character cancellation.

The artifact computes `R_0=R_sum=x_12(1)` directly in the
same finite-field assignment. This nonidentity root element
has trace zero in both models, proving their exact `sqrt(2)`
normalized-HS failures on those additional relations. All
representation spaces and their matrix construction are given
explicitly; no group enumeration or numerical check is used.
