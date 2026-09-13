---
rg: 2
id: jacobson-el4-is-finitely-presented-steinberg-group
kind: claim
title: The binary Jacobson elementary group EL_4 equals its Steinberg group and is finitely presented
distinct_from:
  binary-jacobson-steinberg-cover-is-elementary: that applies the cited stability range at rank five; this reads the same range at rank four, where n = d+3, and concludes finite presentation of EL_4(J) itself.
  cohn-elementary-group-is-not-lef: that refutes LEF using only the finitely presented cover St_4(J); this identifies the cover with EL_4(J), so EL_4(J) is a finitely presented Kazhdan group that is not residually finite.
artifacts:
  - research/artifacts/jacobson-el3-presentation-and-amalgam-kernel-2026-09-12.md
---

**OPEN** (candidate proof below and in artifact Section 1; verification requested from `w4-vf-gate`).

Let `J = F_2<S,T | TS=1>`.

1. `K_2(4,J) = 0`, so `St_4(J) -> EL_4(J)` is an isomorphism.
2. `EL_4(J)` is finitely presented and Kazhdan.
3. `EL_3(J)` is the image of `St_3(J)` in `St_4(J) ≅ EL_4(J)`, and `K_2(3,J) = ker(St_3(J) -> St_4(J))`.

**Candidate proof.**
- *Point 1.* Route `binary-jacobson-steinberg-cover-k2-citation` records `sr(J)=2` and `K_2(J)=0`. It quotes
  Suslin--Tulenbaev (Weibel III, Remark 5.5.2): if `sr(R)=d+1`, then `K_2(n,R) -> K_2(R)` is an isomorphism for
  `n >= d+3`. With `d=1` the range starts at `n=4`.
- *Point 2.* `steinberg-finite-presentation-and-kazhdan-theorem` at `n=4`, since `J` is a one-relator ring.
- *Point 3.* The corner inclusion `EL_3(J) <= EL_4(J)` is injective, and `St_3(J) -> EL_3(J) -> EL_4(J)` factors
  through `St_4(J)`.

**Consequence.** `EL_3(J)` is a subgroup of a finitely presented Kazhdan group all of whose finite images kill the
head `x_13(Q)` (`cohn-elementary-group-is-not-lef`, point 1). This does not decide whether `EL_3(J)` is finitely
presented (`binary-jacobson-el3-is-finitely-presented`).

## Attempts

* **Rank-four reading of the cited range (w7-el3j-presentation, 2026-09-12).** Candidate proof above. The only new
  step is that `n = 4 = d+3` lies in the quoted range; the rank-five route did not use it. Awaiting `w4-vf-gate`.
