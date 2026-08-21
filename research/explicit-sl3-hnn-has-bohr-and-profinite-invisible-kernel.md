---
rg: 2
id: explicit-sl3-hnn-has-bohr-and-profinite-invisible-kernel
kind: claim
title: An explicit noninjective quotient induces isomorphisms on both Bohr and profinite compactifications
distinct_from:
  explicit-sl3-hnn-mark-is-fd-invisible: that isolates one invisible word; this identifies the complete finite-dimensional representation functor and both compactifications.
  sln-z-thin-codense-tau-pair: that supplies co-density data but does not form the HNN quotient.
---

Let `A=SL_3(Z)`, let `C=<a,b>` be the displayed profinitely dense free
subgroup of `explicit-sl3-thin-codense-tau-pair`, and put

```text
G_exp = < A,t | [t,a]=1, [t,b]=1 >.
```

There is a natural quotient

```text
q:G_exp -> A x Z,   q|A=id,   q(t)=(1,1).              (BPK1)
```

It is not injective: for the displayed order-three `r notin C`, Britton's
lemma gives

```text
[t,r] != 1 in G_exp,
q([t,r])=1.                                            (BPK2)
```

Nevertheless precomposition with `q` is a bijection

```text
Hom(A x Z,U(d)) -> Hom(G_exp,U(d))                     (BPK3)
```

for every `d`.  Indeed, if `sigma:G_exp->U(d)` and `rho=sigma|A`, then
`rho(A)` is finite and congruence.  Profinite density gives
`rho(C)=rho(A)`.  Since `sigma(t)` centralizes `rho(C)`, it centralizes all
of `rho(A)`, so `sigma` factors uniquely through `(BPK1)`.

The same proof applies to arbitrary finite target groups.  Consequently `q`
induces isomorphisms

```text
G_exp^prof  ~= (A x Z)^prof,
bG_exp      ~= b(A x Z),                               (BPK4)
```

where `^prof` denotes profinite completion and `b` the Bohr compactification.
Thus `(BPK1)` is an explicit noninjective epimorphism invisible to every
finite quotient and every finite-dimensional unitary representation, with a
displayed torsion-certified kernel word.

The construction is an instance of a general lemma: if `C<=A` is finitely
generated and has the same image as `A` in every finite-dimensional unitary
representation, then `<A,t | [t,C]=1> -> A x Z` induces a Bohr isomorphism;
profinite density gives the profinite statement.

