---
rg: 2
id: split-mf-equivalences-preserve-matricial-stability-proof
kind: route
title: Prove stability invariance under split MF-equivalence
target: split-mf-equivalences-preserve-matricial-stability
requires:
  - mf-equivalences-form-a-colimit-stable-localization
---

Given `Phi:G->U(Q_d)`, let `M=Phi(G)`.  The group `M` is countable and MF
because it is a subgroup of a norm-corona unitary group.  Apply the defining
Hom-bijection of an MF-equivalence to the map `G->M`; composing the resulting
map `Q->M` with `M<=U(Q_d)` gives `(SCE2)`.

Assume first that `G` is point-norm matricially stable.  Let
`alpha_n:Q->U(d_n)` be asymptotically multiplicative and put

```text
phi_n=alpha_n pi.                                      (SCP1)
```

Stability of `G` supplies homomorphisms
`sigma_n:G->U(d_n)` with

```text
||phi_n(g)-sigma_n(g)||->0                 (g in G).   (SCP2)
```

The maps `rho_n=sigma_n s` are homomorphisms on `Q`; at `q in Q`,

```text
phi_n(s(q))=alpha_n(pi(s(q)))=alpha_n(q),              (SCP3)
```

so `(SCP2)` proves stability of `Q`.

Conversely assume `Q` stable and let `phi_n:G->U(d_n)` be asymptotically
multiplicative.  Denote its corona homomorphism by `Phi`.  By `(SCE2)`,

```text
Phi=Psi pi                                               (SCP4)
```

for a unique `Psi:Q->U(Q_d)`.  Since `pi s=id`, necessarily
`Psi=Phi s`, which is represented by the coordinate maps `phi_n s`.  Equality
`(SCP4)` in the quotient by the norm-null sequences says exactly that

```text
||phi_n(g)-phi_n(s(pi(g)))||->0.                       (SCP5)
```

Stability of `Q` supplies homomorphisms `rho_n:Q->U(d_n)` satisfying

```text
||phi_n(s(q))-rho_n(q)||->0                 (q in Q).  (SCP6)
```

For fixed `g`, combine `(SCP5)` and `(SCP6)` at `q=pi(g)`:

```text
||phi_n(g)-rho_n(pi(g))||
 <=||phi_n(g)-phi_n(s(pi(g)))||
   +||phi_n(s(pi(g)))-rho_n(pi(g))|| ->0.              (SCP7)
```

The maps `rho_n pi` are genuine homomorphisms `G->U(d_n)`, proving
stability of `G`.
