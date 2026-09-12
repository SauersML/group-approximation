---
rg: 2
id: thompson-v-not-hyperlinear-from-kl-violation
kind: route
title: A Kervaire--Laudenbach violation over Thompson's V proves V is not hyperlinear
target: thompson-v-not-hyperlinear
requires: [kl-violating-equation-over-thompson-v, kervaire-laudenbach-holds-for-hyperlinear]
---

If V were hyperlinear, `kervaire-laudenbach-holds-for-hyperlinear` would make
every nonsingular coefficient map over V injective, which contradicts the
prerequisite. So V is not hyperlinear.

By `leavitt-kl-violation-from-thompson-v-violation` the same word is also a
violation over the binary Leavitt unit group. The non-hyperlinearity of that
group then follows from this route as well, since hyperlinearity passes to
subgroups.
