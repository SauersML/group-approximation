---
rg: 2
id: nielsen-cocycle-compactification-proof
kind: route
title: Compactify the hidden affine basepoint with the Nielsen one-cocycle
target: finite-dimensional-nielsen-cocycle-models-kill-mark
requires: [free-lamp-radical-is-free, infranormal-compact-closure-normal]
artifacts:
  - notes/UNIQUE_TRACE_KUN_THOM_DOUBLE.md
---

Put `c(g)=b_(g o)` and `d(g)=c(g)^(-1)`.  The Nielsen formula `(NCM1)`
gives

```text
alpha_g(c(k)) = b_(g k o) b_(g o)^(-1),
c(g k) = alpha_g(c(k)) c(g),
d(g k) = d(g) alpha_g(d(k)).                                (NCP1)
```

Thus the basepoint which disappeared on passing from the free `C_2` lamps to
their even subgroup survives as the nonabelian one-cocycle `d`.

Given `(B,beta,theta)` as in `(NCM2)`, define

```text
Psi : G -> U(B) semidirect Aut(B),
Psi(g) = (theta(d(g)), beta_g),                              (NCP2)
```

where `(u,a)(v,b)=(u a(v),ab)`.  Equation `(NCP1)` says exactly that `Psi`
is a homomorphism.  Since `B` is finite-dimensional, both `U(B)` and
`Aut(B)` are compact, so the target semidirect product is compact.

For `gamma in Gamma`, `gamma o=o`, hence `d(gamma)=1`.  Therefore

```text
closure(Psi(Gamma)) <= {1} semidirect Aut(B).                (NCP3)
```

By `infranormal-compact-closure-normal`, this closure is normal in
`closure(Psi(G))`.  It contains `Psi(Gamma)`, so it contains the image under
`Psi` of the normal closure `H=<<Gamma>>_G`.  If `h in H`, `(NCP3)` forces
the first coordinate of `Psi(h)` to be `1`; hence

```text
theta(d(h))=1,
theta(b_(h o))=1.                                           (NCP4)
```

This proves `(NCM3)`.  If `h o != o`, `b_(h o)` is one of the displayed free
basis elements of `N`; its regular unitary has spectrum the whole unit circle,
so `(NCM4)` follows and strong convergence is impossible.

The proof uses neither property `(T)` nor a trace.  Its only rigidity input is
compact recurrence, packaged by `infranormal-compact-closure-normal`; the new
step is the cocycle compactification `(NCP2)`, which makes that theorem apply
despite the absence of the odd base lamp `a_o` from the split radical.
