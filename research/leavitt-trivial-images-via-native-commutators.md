---
rg: 2
id: leavitt-trivial-images-via-native-commutators
kind: route
title: "The killed native Leavitt word normally generates every elementary root subgroup"
target: binary-leavitt-tracial-ultraproduct-images-are-trivial
requires: ["leavitt-native-strict-kazhdan-compression-pair", "kazhdan-compression-pairs-normalize-all-tracial-models"]
artifacts:
  - research/artifacts/leavitt-direct-normalization-obstruction-2026-09-20.md
---


The pair prerequisite permits normalization of D=pi(L)' cap M.
The artifact's k centralizes L and uku^-1=x_12(e), so pi(x_13(e))=1.
Normality of the kernel and be=b, ba=1 then kill, successively,

```text
[x_41(b),x_13(e)]=x_43(b),
[x_43(b),x_32(a)]=x_42(1),
[x_14(r),x_42(1)]=x_12(r)   (r in R).
```

Elementary permutation conjugations give all root subgroups, which
generate Q. Hence every such homomorphism is trivial. This is a
native proof of the existing claim, with no simplicity assumption.
The analytic input retains Liu's internality and Thom's conditional
normalization attribution in the named prerequisite and artifact.
