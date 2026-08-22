---
rg: 2
id: sl2-amalgamated-free-exclusion-from-exact-leak
kind: route
title: An amalgamated-free Haar unitary has the exact quasi-regular profile, so excluding that profile excludes it
target: sl2-hnn-admits-no-amalgamated-free-haar-unitary
requires:
  - no-exact-quasi-regular-leak
---

Let `k in L(C)' cap M` be a Haar unitary free from `L(A)` with
amalgamation over `B = L(C)`, `C = SL_2(Z) <= A = SL_2(Z[1/2])`.  For
`g in C`, `k` commutes with `u_g` and `tau(k^* u_g k u_g^*) = 1`.  For
`g notin C`, `E_B(u_g) = 0`, and the word `k^* u_g k u_g^*` alternates
between `W^*(B,k) (-) B` (the letters `k^*, k`, since `E_B(k^(+-1)) = 0`)
and `L(A) (-) B` (the letters `u_g, u_g^*`), so amalgamated freeness gives
`E_B(k^* u_g k u_g^*) = 0` and `tau(k^* u_g k u_g^*) = 0`.  Hence

```text
tau(k^* u_g k u_g^*) = 1_C(g)      for all g in A,
```

which is exactly the profile `(EQL1)` of `no-exact-quasi-regular-leak`.
That claim forbids any subgroup-central unitary with this profile, so no
amalgamated-free `k` exists.  The converse fails in general: a unitary
with profile `1_C` need not satisfy `E_B(k^2) = 0` or the higher
alternating-word conditions, so the target is strictly weaker than the
prerequisite, and `no-exact-quasi-regular-leak` sits strictly between
the relative-commutant collapse and the target in the lane's hierarchy.
