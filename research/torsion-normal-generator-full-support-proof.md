---
rg: 2
id: torsion-normal-generator-full-support-proof
kind: route
title: Round the torsion mark and span the finitely many conjugate active ranges
target: torsion-normal-generator-has-full-support-corona-core
requires:
  - matrix-corona-projection-monoid-is-rank-germs
---

Choose unitary lifts `U_n(g)` of `rho(g)`.  Since `a^m=1`, spectral
rounding replaces `U_n(a)` by an `m`-torsion unitary `A_n` with

```text
||A_n-U_n(a)|| -> 0.                                  (TNC1)
```

After passing to the infinite support on which `A_n!=1`, let

```text
E_n=Ran(A_n-1),                    r_n=dim(E_n)>=1.     (TNC2)
```

For every `s in S`, fix an expression

```text
s=product_(j=1)^(ell_s) h_(s,j) a^(eps_(s,j)) h_(s,j)^(-1),
                                    eps_(s,j) in {+1,-1},
```

where `sum_(s in S) ell_s=L`, and use the expression `a=a` for the marked
generator.  At coordinate `n` put

```text
V_n(s)=product_j U_n(h_(s,j)) A_n^(eps_(s,j)) U_n(h_(s,j))^*.
                                                               (TNC3)
```

Asymptotic multiplicativity of the lifts and `(TNC1)` give

```text
||V_n(s)-U_n(s)|| -> 0.                               (TNC4)
```

Each factor in `(TNC3)` is the identity off the conjugate subspace
`U_n(h_(s,j))E_n`.  Let `K_n` be the span of these subspaces over all
occurrences in the chosen expressions.  Then

```text
E_n <= K_n,                         dim(K_n)<=L dim(E_n),
```

Every factor in `(TNC3)` preserves `K_n` and is the identity on `K_n^perp`;
hence so does every `V_n(s)`.
Choose a coordinate unitary identifying

```text
V_n(s)=sigma_n(s) directSum 1_(K_n^perp).              (TNC5)
```

For an arbitrary element of `G`, evaluate a fixed word in `S`.  Equations
`(TNC4)--(TNC5)` show that these evaluations form an operator-norm
asymptotic representation and represent the original corona homomorphism
after adjoining the trivial summand.

The active projection of `A_n` on `K_n` has rank `r_n`, while
`k_n=dim(K_n)<=Lr_n`.  Every nontrivial `m`th root of unity is at distance
at least `eta_m` from `1`, so

```text
||sigma_n(a)-1||_2^2
 >= eta_m^2 r_n/k_n
 >= eta_m^2/L.                                         (TNC6)
```

Finally suppose `a` is a product of `N_g` conjugates of `g^(+1)` or
`g^(-1)`.  Evaluation in `sigma_n`, telescoping, unitary invariance of the
normalized Hilbert--Schmidt norm, and asymptotic multiplicativity give

```text
||sigma_n(a)-1||_2
 <= N_g ||sigma_n(g)-1||_2+o(1).                       (TNC7)
```

Combining `(TNC6)` and `(TNC7)` proves the propagated lower bound.  If every
nonidentity `g` normally generates `a`, all nonidentity elements remain
separated and the induced tracial-ultraproduct map is injective.
