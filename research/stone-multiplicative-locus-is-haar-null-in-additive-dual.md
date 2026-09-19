---
rg: 2
id: stone-multiplicative-locus-is-haar-null-in-additive-dual
kind: claim
title: The Stone multiplicative locus is Haar-null in the additive dual of an atomless Boolean algebra
distinct_from:
  haar-algebraic-actions-have-permutation-koopman-spectrum: that constrains Koopman spectra of arbitrary compact-group Haar actions; this computes the exact Haar measure and trace of the tempting additive dual of a measure algebra.
  affine-haar-membership-does-not-promote-irs-trace: that shows an affine-Haar membership law need not promote an IRS trace; this proves the Boolean multiplicative law itself occupies a null sector of the canonical additive Haar model.
  manzoor-natural-subgroup-subshift-is-not-a-haar-envelope: that audits the compact objects already present in Manzoor's proof; this tests the new Stone/Pontryagin construction on a countable generating measure algebra.
---

Let `A` be a countable atomless Boolean algebra and forget its intersection
operation, retaining only the countable elementary abelian group

```text
K=(A, symmetric_difference).                            (SML1)
```

Write `X_add=dual(K)` with Haar probability `m`.  For `a in A`, let `u_a`
be the corresponding sign coordinate and `p_a=(1-u_a)/2`.  The canonical
trace of `L(K)=L^infinity(X_add,m)` is

```text
tau(u_a)=0 and tau(p_a)=1/2       for every a != 0.      (SML2)
```

Thus the additive dual remembers no event weights.

The Stone space of `A` embeds into `X_add`: a Boolean homomorphism
`epsilon:A -> F_2` gives the additive character
`chi_epsilon(a)=(-1)^(epsilon(a))`.  Its image is the multiplicative locus

```text
S={chi_epsilon: epsilon(1)=1 and
                   epsilon(a meet b)=epsilon(a)epsilon(b)}.  (SML3)
```

This locus has `m(S)=0`.  Indeed, for every finite Boolean subalgebra with
`n` atoms, restriction of a Haar-random additive character is uniform on
`2^n` characters, while exactly `n` restrictions are ultrafilters.  Hence

```text
m(S) <= n/2^n                                             (SML4)
```

for arbitrarily large `n`.

If `mu` is a probability measure on the Stone space, its canonical Stone
measure `nu_mu` in `(SML3)` satisfies

```text
integral u_a dnu_mu = 1-2mu(a),
integral p_a dnu_mu = mu(a),                              (SML5)
```

and is singular to `m`.  In particular the formal selector `1_S` is the zero
projection in `L(K)`.  No nonzero central corner of the additive group
algebra selects the Boolean-multiplicative points.

This remains true after placing `K` inside an arbitrary countable group
`G`.  The restriction of the regular representation of `G` to `K` is a
multiple of the regular representation of `K`.  If a nonzero projection
`q in L(G)` commutes with `K` (in particular if `q` is central), then the
spectral measure of the corner representation

```text
k |-> q lambda_G(k) q on q ell^2(G)                      (SML6)
```

is absolutely continuous with respect to additive Haar measure: its density
is the conditional expectation of `q` onto `L(K)`, normalized by `tau(q)`.
It therefore cannot equal the singular Stone measure `(SML5)`.

Ordinary group relators do not repair this.  Relators among the literal
generators of `K` replace `K` by a quotient `K/N`; the canonical trace is
Haar on the annihilator of `N`, and every surviving nonzero `p_a` still has
trace `1/2`.  The Boolean requirement

```text
p_(a meet b)=p_a p_b                                    (SML7)
```

is an operator-algebra polynomial relation, not an equality of words in the
additive group.  Enforcing `(SML7)` by auxiliary group words or a noncentral
compression is precisely a nonlinear projection/BCS groupification problem;
it is not achieved by Pontryagin duality.

For a finite Boolean algebra with `n` atoms, `S` has positive Haar mass
`n/2^n`, but its normalized Stone corner is uniform on the `n` atoms.  Along
an atomless refining sequence these corner traces tend to zero by `(SML4)`,
so the finite exception produces no nonzero limiting corner.

