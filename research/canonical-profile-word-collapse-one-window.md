---
rg: 2
id: canonical-profile-word-collapse-one-window
kind: claim
title: Canonical-profile word collapse is certified by one finite trace and relator window
distinct_from:
  canonical-profile-collapse-compactness: that permits a rational group-algebra mark and consequently needs finite windows at every epsilon; tensor powers make one cutoff sufficient only for a word mark.
  hyperlinear-radical-is-finitely-witnessed: that is unconditional and yields radical membership in a finite-prefix group; canonical trace side conditions here refer to the full quotient and cannot be discarded.
  trace-conditioned-reverse-kleene-collapse: that requires computable side-test data; this certificate exists non-effectively.
---

Let `F=F(S)`, let `Gamma=F/<<R>>` for a finite or recursively enumerable
relator list, and put

```text
chi(v)=tau_Gamma(v) in {0,1}.
```

For a word `w in F` and any fixed `alpha<sqrt(2)`, the following are
equivalent.

1. Every homomorphism `theta:Gamma->prod_omega U(d_n)` with
   `tau_omega(theta(v))=chi(v)` for all words `v` kills `w`.
2. There are finite sets `E subset R`, `T subset F` and `delta,eta>0` such
   that every finite-dimensional tuple satisfying

   ```text
   max_(r in E)||r(U)-I||_2<delta,
   max_(v in T)|tr(v(U))-chi(v)|<eta
   ```

   also satisfies `||w(U)-I||_2<alpha`.

This does not assert that `w` lies in the hyperlinear radical of the
finite-prefix group: the side conditions use the canonical character of the
full quotient, which may differ from that of the prefix.
