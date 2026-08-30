---
rg: 2
id: stw63-semifinite-shadow-invisibility-proof
kind: route
title: Compose with the shadow representation and use semifinite uniqueness
target: stw63-counterexamples-are-invisible-in-all-semifinite-shadows
requires:
  - stw63-semifinite-von-neumann-codomains-have-uniqueness
---

If `M!=0`, the compositions `pi phi` and `pi psi` are unital.  Since `Z` is
simple, every unital star homomorphism out of `Z` is injective.  They are
therefore two unital embeddings into the separably acting semifinite von
Neumann algebra `M`.  The required theorem supplies unitaries `u_n in M`
with

```text
||u_n pi(phi(a))u_n* - pi(psi(a))|| -> 0             (a in Z).
```

Taking `B=Z*_(C)Z`, `phi=i_0`, and `psi=i_1` gives the free-product clause.
Taking `pi` to be a tracial GNS representation gives the final clause.

Notice that the implementing unitaries need not lie in `pi(B)`.  Returning
them from `M` to the represented C-star algebra is exactly the lifting step
which this theorem does not provide and which an LXIII counterexample must
defeat.

