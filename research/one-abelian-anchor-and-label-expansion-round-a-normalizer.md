---
rg: 2
id: one-abelian-anchor-and-label-expansion-round-a-normalizer
kind: claim
title: One character-placement anchor and classical triple-label expansion round an abelian normalizer
artifacts:
  - research/artifacts/parallel-group-word-2026-09-04.md
distinct_from:
  abelian-root-average-placement-rounds-its-normalizer: that assumes placement of the entire character table on average; this derives that average from one character anchor and actor commutators under an explicit classical gap.
  two-pauli-anchors-localize-arbitrary-normalizer-twists: that uses a linear Weyl-coefficient profile to localize a matrix to a factor commutant; this uses a quadratic root-block profile to round a variable atom permutation and allows atom-dependent multiplicity twists.
---

Let `p` be prime, `n>=1`, `q=p^n`, and label `q` equal rank-`m` projections
by `x in F_p^n`. Put `A=span{P_x}` and

```text
U_h=sum_x exp(2 pi i h(x)/p) P_x       (h in (F_p^n)^*).
```

Let `S` be a symmetric generating multiset of `GL_n(F_p)`. On

```text
Omega={(x,y,z) in (F_p^n)^3:y!=z}
```

assume its simultaneous action has the classical counting-measure gap

```text
avg_s ||f-s.f||_2^2 >= kappa ||f-Pi f||_2^2,            (AEX1)
```

where `Pi` averages each orbit. For each `s`, let `D_s` be any unitary with
`D_s P_x D_s^*=P_(sx)`. Its unitaries between multiplicity blocks may depend
on `x` and need satisfy no actor multiplication relations.

For a unitary `V` and one nonzero `h_0`, define

```text
a=dist_2(VU_(h_0)V^*,A),
e^2=avg_s ||[V,D_s]||_2^2,
theta=p^(n-1)(p-1)/(p^n-1),     gamma_p=2 sin(pi/p).
```

Then the full-table placement loss of `(ARP2)` satisfies

```text
sqrt(L(V))
 <= sqrt(2)a/(gamma_p sqrt(theta))
    +2(1+theta^(-1/2))e/sqrt(kappa),                   (AEX2)
```

and therefore

```text
dist_2(V,N(A))
 <= 2a/(gamma_p sqrt(theta))
    +2sqrt(2)(1+theta^(-1/2))e/sqrt(kappa).             (AEX3)
```

Here `theta>=1/2`. With fixed `p`, bounded `|S|`, and a uniform `kappa`,
the estimate uses a constant number of checks independent of `n,m`.
Existence or presentation-level authentication of such actors is not an
assumption to omit: `(AEX1)` and their exact atom covariance are explicit
hypotheses.

The anchor is a placement test, not an assumed group word. A prescribed
ordinary covariance row `VU_(h_0)V^*~=U_h` bounds `a` only when the target
word is already authenticated as the stated element of `A`. Similarly,
the actor normalizer hypothesis must be supplied independently. This
conditional localization lemma does not by itself impose a Leavitt
one-to-two loss or give a nonhyperlinear group.

DERIVATION
abelian-anchor-triple-profile-proof
