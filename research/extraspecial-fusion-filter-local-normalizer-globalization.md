---
rg: 2
id: extraspecial-fusion-filter-local-normalizer-globalization
kind: claim
title: The extraspecial fusion filter gives exact one-hot corners, but every normalizer globalization is matricial
artifacts:
  - research/extraspecial-fusion-filter-normalizer-proof.md
distinct_from:
  odd-tensor-closure-forces-a-threehot-hidden-sector: that rules out literal selector spectral decoding; this gives the positive additive-Fourier escape and then proves its sharp normalizer boundary.
  finite-sheet-transport-networks-are-exactly-matricial: that treats finite coordinate-sheet bijections; this treats arbitrary representations of an ambient group normalizing an extraspecial matrix factor.
  source-specific-pointed-rank-router-face: that leaves a nonmultiplicative pointed corner open; this identifies nonnormal relative-position/Hecke data as mandatory for that corner.
---

Let `E_n` be an extraspecial (2)-group of order
`2^(1+2n)`, with center `<J>`, and put `d=2^n` and
`p_-=(1-J)/2`.  Then

```text
p_- C[E_n] p_- isomorphic to M_d(C).                    (EFF1)
```

If `A<=E_n` is a maximal abelian subgroup containing `J`, the Fourier
projections

```text
e_chi=|A|^(-1) sum_(a in A) conjugate(chi(a))a,
chi(J)=-1,                                               (EFF2)
```

are `d` mutually orthogonal rank-one projections summing to `p_-).
Thus the negative central corner carries an exact (d)-outcome one-hot PVM.
These outcomes are additive Fourier projections, not spectral projections
of (d) literal Boolean group words, so the odd-tensor three-hot theorem
does not apply.  Indeed the unique spin representation `rho` satisfies

```text
rho^tensor3 isomorphic to d^2 rho.                       (EFF3)
```

The fusion filter is nevertheless only local.  Let an ambient group
`Gamma` contain `E_n`, keep `J` central, and suppose `E_n normal
Gamma`.  In every marked representation `pi(J)=-I` there is a
multiplicity space `K` with

```text
H_pi isomorphic to C^d tensor K,
pi(E_n)''=M_d(C) tensor I_K.                             (EFF4)
```

Every ambient group element then has the form

```text
pi(g)=u_g tensor w_g                                    (EFF5)
```

after choosing an inner implementer `u_g` for its automorphism of the
matrix factor.  Consequently every Fourier outcome in `(EFF2)`, and every
outcome obtained from it by finite-group normalizer transport, lies in

```text
M_d(C) tensor I_K.                                      (EFF6)
```

If such projections reconstructed all contexts of the fixed Lin
independent-set SynchBCS, their first tensor factors would give a unital
finite-dimensional representation of its algebra, contradicting its
no-matrix property.

Therefore an extraspecial or finite-group fusion anchor can evade odd tensor
closure, but it cannot solve losing-pair orthogonality through normalizer
transport.  A viable globalization must use at least one **nonnormal**
conjugate matrix factor and make the relative position of two finite
subfactors carry the source payload.

For a finer isotypic idempotent `q in C[K]` which is not reducing for the
ambient words, there is an additional exact seam:

```text
(q pi(g)q)(q pi(h)q)-q pi(gh)q
 =-q pi(g)(1-q)pi(h)q.                                  (EFF7)
```

Thus an ambient solution-group word relation does not become the desired
multiplicative relation in the `q` corner unless the off-corner leakage is
also controlled.  Making all relevant words reduce `q` returns to the
matricial normalizer case.  Leaving leakage nonzero is precisely a
nonnormal Hecke/relative-position compiler, not a finite fusion-table
solution.

So the smallest anchor has a sharp outcome:

- **local one-hot fusion: constructed exactly;**
- **normal finite-group parity transport: impossible for the no-matrix
  source;**
- **nonnormal pointed Hecke transport with a quantitative leakage decoder:
  still open.**
