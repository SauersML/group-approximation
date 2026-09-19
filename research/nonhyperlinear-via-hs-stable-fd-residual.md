---
rg: 2
id: nonhyperlinear-via-hs-stable-fd-residual
kind: route
title: Apply HS stability to a nontrivial finite-dimensional residual word
target: non-hyperlinear-group
requires:
  - hs-stability-plus-fd-residual-forces-nonhyperlinearity
  - finitely-presented-hs-stable-nontrivial-fd-residual
---

Choose the group and word from the explicit-witness claim and apply the
stability theorem.  The word is nontrivial in the abstract group but is killed
by every exact finite-dimensional representation; stability would force any
canonical matrix microstate to kill it as well, contradicting its canonical
trace separation.
