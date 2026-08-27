---
rg: 2
id: pointed-weighted-defect-gap-pulls-back
kind: claim
title: Pointed weighted-defect gaps pull back with the homomorphism constant
artifacts:
  - research/artifacts/qutrit-moment-exact-psync-splice-2026-08-23.md
distinct_from:
  non-ce-bcs-has-robust-approximate-energy-gap: that obtains a compactness gap for one fixed BCS; this transports any already defined pointed gap through a weighted homomorphism.
  exact-support-gap-nonexact-checks-no-advantage: that sparsifies a finite exact relator menu; this is an algebraic defect inequality preserving one chosen nontrivial moment.
---

Let `(A,mu)` and `(B,nu)` be weighted star algebras, let `w in A`, and put
`v=alpha(w)` for a `C`-homomorphism

```text
alpha:(A,mu) -> (B,nu).
```

For `delta>0`, define

```text
gamma_(A,w)(delta)
 = inf { def_A(tau): tau tracial, ||w-1||_tau^2>=delta }.
```

Then

```text
gamma_(B,v)(delta) >= C^(-1) gamma_(A,w)(delta).        (PDG1)
```

Thus weighted-algebra reductions preserve not only an unpointed soundness
gap but any selected moment separation carried by a word or global-variable
polynomial.

