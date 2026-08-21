---
rg: 2
id: mark-relative-fanizza-reverse-kleene-proof
kind: route
title: Let NONHALT soundness make every surviving marked corner contradictory
target: mark-relative-fanizza-ultraproduct-decoder-suffices
requires:
  - fanizza-et-al-computable-bcs-signal-family
  - canonical-profile-kleene-higman
---

On a NONHALT input, set the BCS strategy error to zero in the Fanizza bound

```text
phi(D_m)<=C_m epsilon.
```

Every perfect strategy therefore kills `D_m`.  If a matrix-ultraproduct
homomorphism had `pi(p_m)!=0`, clause `(MRF3)` would produce a perfect
strategy with positive `D_m` mass, a contradiction.  Hence all such
homomorphisms kill `p_m`; in particular every canonical microstate sequence
does.

Now make the fixed-point program enumerate finite group-algebra certificates
for `p_m=0` and halt when it finds one.  If it halted, `(MRF1)` would say the
same mark is nonzero.  Hence it does not halt.  Completeness of certificate
enumeration gives `p_m!=0` at the fixed point, while the preceding paragraph
gives canonical-profile collapse.  Apply
`canonical-profile-kleene-higman` and then effective Higman embedding.

The proof never calls the decoder on `pi(p_m)=0`; this is exactly why the
trivial-homomorphism CE obstruction does not apply.
