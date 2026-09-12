---
rg: 2
id: stw99-xcix-prime-dimension-drop-defect-modulus
kind: claim
title: Z-stability is the zero set of a sharper finite dimension-drop defect modulus
distinct_from:
  stw99-xcix-global-central-defect-modulus: that uses embeddings of the whole strongly self-absorbing algebra Z and obtains the loss 304 sqrt(gamma)+2 gamma; this uses only finitely generated prime dimension-drop blocks and obtains an asymptotic leading loss 160 sqrt(gamma).
  stw99-xcix-fixed-centrality-windows-collapse-at-zero-distance: that fixes a window in one dense sequence of Z; this defines one scalar over every prime block and every finite ambient tuple, and identifies its zero set exactly.
  stw99-xcix-central-copy-transfer-bound: that invokes the approximately-inner-half-flip transport theorem for Z; this invokes the finite-nuclear-dimension embedding theorem on the possibly proper image quotient of each dimension-drop map.
---

For `k>=2`, let `I_k=I_(k,k+1)` be the prime dimension-drop algebra and
fix a finite selfadjoint contractive generating set `H_k`.  For a unital
C\*-algebra `E`, define

```text
delta_(m,k)^dd(E)
 = sup_(x_1,...,x_m in E_1)
     inf_(unital homomorphisms psi:I_k->E)
       max_(i<=m,h in H_k) ||[x_i,psi(h)]||,

kappa_dd(E)=sup_(m>=1,k>=2) delta_(m,k)^dd(E) in [0,2],       (DD1)
```

where an infimum over no unital homomorphisms is declared to be `2`.  For
every separable unital `E`,

```text
kappa_dd(E)=0  iff  E is Z-stable.                           (DD2)
```

There is a quantitative Kadison--Kastler estimate.  Let `A,B` be unital
C\*-subalgebras of one `B(H)` with the same unit, and suppose

```text
d_KK(A,B)<gamma<1/5670000.
```

Put

```text
eta(gamma)=4(2 gamma+gamma^2)(2+2 gamma+gamma^2),
Lambda(gamma)=40 sqrt(eta(gamma))+2 gamma
             =80 sqrt((2 gamma+gamma^2)(2+2 gamma+gamma^2))+2 gamma.
                                                                    (DD3)
```

If either `A` or `B` admits a unital homomorphism from `I_k` for every
`k>=2`, then so does the other and

```text
|kappa_dd(A)-kappa_dd(B)| <= Lambda(gamma).             (DD4)
```

In particular, if `A` is separable and `Z`-stable, then

```text
kappa_dd(B) <= Lambda(gamma)=160 sqrt(gamma)+o(sqrt(gamma)). (DD5)
```

Thus a vanishing-distance sequence of common-unit XCIX counterexamples has
positive finite-block defects converging to zero at the sharper displayed
rate.  This is an exact reduction, not a proof that the zero set is open.
