---
rg: 2
id: jacobson-ts-cell-seven-ray-transvection-proof
kind: route
title: Compute the TS word as one finite transvection in the improved seven-ray model
target: jacobson-ts-cell-is-independent-after-first-raw-commutation
requires:
  - jacobson-two-braid-infimum-is-zero
  - binary-jacobson-first-alternating-ts-closure-relation
artifacts:
  - research/artifacts/jacobson-ts-cell-after-seven-ray-countermodel-2026-09-08.md
---

Use the explicit seven-ray quotient supplied by the first prerequisite.
There `HcH=z_P`, `HzH=Dc`, and `[HcH,k]=(I+E_21)_P`, where
`D` adds `a_(1,1)` at source `a_(3,0)`. Conjugation by the last
tail element moves that added vector to `b_(3,1)`. The commutator
identity then evaluates `W` as the product of these two commuting
transvections and the head transvection `z_Q`.

Their three target basis vectors are distinct, so the product is nontrivial.
Conjugation by `(I+E_12)_Q` adds `a_(1,0)` to that target vector,
so the commutator is exactly `w`. The unitary commutator norm bound
therefore forces TS-word defect at least one in every representation
of this quotient retaining the head.
The second prerequisite supplies the literal `TS=1` calculation killing
the same word in `EL_3(J)`. The literal head action remains nontrivial,
which establishes the strengthened presentation's marked consistency.
