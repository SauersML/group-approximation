---
rg: 2
id: normal-state-free-near-representation-proof
kind: route
title: Restrict the near representation to the support of its density operator
target: normal-state-free-near-representation-forces-factorization
requires: []
---

Let `phi(a)=Tr(Da)`, where `D` is the positive trace-class density operator of
the normal state and `Tr(D)=1`.  Put `p=supp(D)`.

For every `g in G`, `phi`-invariance gives

```text
Tr(D pi(g)^* a pi(g)) = Tr(Da)       for all a in B(H).
```

By trace duality this says

```text
pi(g) D pi(g)^* = D.                                      (NSP1)
```

Hence `pi(g)` commutes with `D`, with all spectral projections of `D`, and in
particular with `p`.  Thus every `pi(g)` restricts to a unitary on `pH`.

For `g,h in G`, write

```text
d_(g,h)=pi(gh)-pi(g)pi(h).
```

The `phi`-near representation identity of Kahl--Schneider Definition 5.3(c)
is

```text
0=phi(d_(g,h)^* d_(g,h))
 =Tr(D d_(g,h)^* d_(g,h))
 =||d_(g,h) D^(1/2)||_HS^2.                              (NSP2)
```

Therefore `d_(g,h)D^(1/2)=0`.  The range of `D^(1/2)` is dense in `pH`, so
boundedness of `d_(g,h)` gives

```text
d_(g,h) p = 0.                                          (NSP3)
```

Consequently

```text
rho(g)=pi(g)|_(pH)
```

is a genuine unitary representation of `G`.

The state `phi` is supported on `p`, so it defines a normal state on `B(pH)`;
by `(NSP1)` it is `rho(G)`-invariant.  The assumed freeness survives unchanged:
for every `g != 1`,

```text
phi(rho(g))=phi(pi(g))=0.                                (NSP4)
```

Kahl--Schneider, *Hyperlinearity via amenable near representations*,
arXiv:2504.10988v2, Theorem 7.4(c) (Theorem D in the introduction), states
that existence of a genuine unitary representation carrying an invariant
state with `(NSP4)` is equivalent to Kirchberg's factorization property.
Applying that theorem to `(rho,phi)` proves the target.
