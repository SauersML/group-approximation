---
rg: 2
id: free-lamp-double-and-sofic-action-proof
kind: route
title: Rewrite the one-compressor double as a sofic free permutational wreath product
target: one-kun-thom-compressor-is-relatively-embeddable
requires:
  - kt-one-compressor-full-coset-action-is-sofic
  - gkp-free-generalized-wreath-soficity
  - kt-q2-double-hyperlinear-iff-relative-embeddable
---

Put `beta(gamma)=a gamma a^(-1)`.  The one-compressor subgroup has the
ascending-HNN presentation

```text
P_A=<Gamma,t | t gamma t^(-1)=beta(gamma), gamma in Gamma>,    t=a.       (FLD1)
```

Indeed, the projection `G -> SL_d(Z)` maps `t` to the infinite-order
matrix `A` and maps `Gamma` to one.  Its restriction gives an exponent
map `ell:P_A->Z`.  The exponent-zero kernel is the telescope

```text
N_A=union_(j>=0) t^(-j) Gamma t^j,
```

so `P_A=N_A rtimes <t>`; this is also the normal form used in
`kt-one-compressor-full-coset-action-is-sofic`.

## Step 1: an exact Tietze transformation

Let `t_1,t_2` be the stable letters in the two factors of
`D_A=P_A *_Gamma P_A`.  Its presentation is

```text
D_A=<Gamma,t_1,t_2 |
      t_i gamma t_i^(-1)=beta(gamma), gamma in Gamma, i=1,2>.             (FLD2)
```

Set `t=t_2` and `s=t_2^(-1)t_1`, so `t_1=t s`.  Comparing the two
relations gives

```text
s gamma s^(-1)=gamma       for every gamma in Gamma.                     (FLD3)
```

Conversely, (FLD3) and the relation for `t` imply the relation for
`t_1=t s`.  Thus the substitutions are inverse Tietze transformations and

```text
D_A ~= <P_A,s | [s,Gamma]=1>
    ~= P_A *_Gamma (Gamma x <s>).                                        (FLD4)
```

There is no quotient or trace choice in (FLD4).

## Step 2: identify the free-lamp kernel

Fold (FLD4) onto `P_A` by fixing `P_A` and sending `s` to one.  The
kernel is the normal closure of `s`.  Bass--Serre normal form gives

```text
ker(fold) = *_(p Gamma in P_A/Gamma) p<s>p^(-1).                          (FLD5)
```

The indexing is well defined because `s` centralizes `Gamma`; distinct
cosets give distinct free factors by the amalgam normal form.  Conjugation by
`h in P_A` sends the factor indexed by `p Gamma` to the one indexed by
`h p Gamma`.  Consequently

```text
D_A ~= (*_(P_A/Gamma) Z) rtimes P_A
    = Z wr^*_(P_A action P_A/Gamma) P_A.                                 (FLD6)
```

## Step 3: soficity

The Kun--Thom ambient group `G` is residually finite, hence sofic, and its
subgroup `P_A` is sofic.  The established stronger statement
`kt-one-compressor-full-coset-action-is-sofic` says that
`P_A action G/Gamma` is sofic.  Its orbit through `Gamma` is
`P_A/Gamma`, so restriction to that orbit is sofic.

Now apply Gao--Kunnawalkam Elayavalli--Patchell, arXiv:2401.04945v3,
Theorem 3.7, in the free case recorded by
`gkp-free-generalized-wreath-soficity`, with lamp group `Z), acting group
`P_A), and set `P_A/Gamma`.  Equation (FLD6) shows that the output is
exactly `D_A`.  Therefore `D_A` is sofic, hence hyperlinear, and

```text
L(P_A) *_(L(Gamma)) L(P_A) = L(D_A)
```

is Connes embeddable.

## Step 4: Gao relative embeddability

For `M=L(P_A)`, `N=L(Gamma)`, and `u=lambda(t)`, the exponent map gives

```text
E_N(u^k)=0       for every nonzero integer k.                             (FLD7)
```

Gao--Junge--Gao, arXiv:2012.07940v3, Appendix Theorem 7.1, therefore applies:
under (FLD7), Connes embeddability of `M *_N M` is equivalent to relative
embeddability of `N subset M` over the scalars.  The preceding step supplies
the former, proving `L(Gamma) subset L(P_A)` is `RE/C`.

## Exact boundary

The subgroups `P_A` for distinct compressors are not an increasing chain,
and the full vertex group imposes relations among their stable letters.
Neither GKP Theorem 3.7 nor Gao Appendix Theorem 7.1 says that the resulting
coequalizer preserves soficity, Connes embeddability, or `RE/C`.  Hence the
argument proves every one-direction restriction but does not pass to
`L(Gamma) subset L(G)`.  The surviving gate is simultaneous compressor
coherence, not the individual compression inclusion.
