---
rg: 2
id: mikhailova-color-code-schreier-irs-firewall
kind: claim
title: The Mikhailova color code can be made faithful but is invisible to Schreier and IRS tests
distinct_from:
  mikhailova-left-right-soficity-is-one-color-code: that gives the one-base-color criterion; this rewrites it as a commuting-centralizer code, makes the actor embedding faithful, and proves why Schreier and IRS approximations test strictly stronger or different data.
  mikhailova-left-right-lef-iff-quotient-rf: that classifies LEF approximability; this isolates the exact failure of pointed Schreier and uniform-root IRS replacements for the weaker GKP problem.
  commuting-sofic-actions-need-not-combine: that blocks a general permanence claim; this identifies the precise special datum still required for the Mikhailova action.
---

Let `q:F=F(X)->H` be onto, write `N=ker(q)`, put
`G=F x F`, and set

```text
M={(u,v) in G:q(u)=q(v)}.
```

The left-right action `G acts on H=G/M` is GKP-sofic if and only if
there are commuting homomorphisms

```text
a,b:F->S_U
```

into a universal permutation ultraproduct and a color point `xi in X_U`
such that

```text
a(n)xi=xi                         for n in N,            (MSI1)
a(w)b(w)xi=xi                     for w in F,            (MSI2)
d_U(a(w)xi,xi)=1                  for w notin N.         (MSI3)
```

The witness may always be chosen so that

```text
Phi:G->S_U,       Phi(u,v)=a(u)b(v),                     (MSI4)
```

is injective.  Thus actor faithfulness is not the missing issue: the
remaining object is an isometric copy of `H` encoded by one external
color orbit, with left and right translations implemented by two commuting
lifts of the free cover.

If `H=<X|R>` is finitely presented, the invariant part of the criterion
is finite.  It is enough to require

```text
a(r)xi=xi             (r in R),
a(x)b(x)xi=xi         (x in X),                          (MSI5)
```

together with the global separation condition `(MSI3)`.  Diagonal
invariance and commutation propagate the relators through their whole
normal closure.

Neither of the two standard subgroup replacements captures this criterion.

1. Pointed finite Schreier convergence to `G/M` exists exactly when
   `M` is separable.  For finitely presented `H`, this is equivalent
   to residual finiteness of `H`.  It is therefore the already-excluded
   LEF route for the repository's non-residually-finite host.
2. A uniformly rooted finite action produces an invariant random subgroup.
   The point mass `delta_M` is an IRS exactly when `M` is normal, and
   here that is equivalent to `H` being abelian.  In the intended
   nonabelian host, `delta_M` is not even a candidate IRS limit.
3. After the faithful amplification in `(MSI4)`, every nonidentity actor
   has fixed-point proportion tending to zero, so the induced Loeb action
   is essentially free.  The stabilizer of the external color point remains
   exactly `M` in the zero/one metric sense.  GKP colors therefore record
   equality patterns not present in ordinary stabilizer statistics.

Consequently the unresolved root cannot be closed by proving subgroup
separability, co-soficity of an IRS, or freeness of the actor model.  Its
exact surviving content is the commuting-centralizer color code
`(MSI1)--(MSI3)`.

DERIVATION
[[mikhailova-color-code-schreier-irs-firewall-proof]]
