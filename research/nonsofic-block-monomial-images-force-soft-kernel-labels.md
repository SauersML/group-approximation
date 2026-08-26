---
rg: 2
id: nonsofic-block-monomial-images-force-soft-kernel-labels
kind: claim
title: A nonsofic block-monomial tracial image requires positive-density soft kernel labels
distinct_from:
  uniformly-discrete-block-monomial-images-are-sofic: that gives a convenient coordinatewise sufficient hypothesis; this identifies the exact kernel-level failure which any nonsofic finite-label block-monomial model must exhibit when no uniform gap is assumed.
  common-padding-erases-julia-derivation-density: that creates a trace-null active seam by adding a common identity block; this detects positive literal block-label activity which is already HS-null and therefore cannot be removed merely by renormalizing the active summand.
  julia-derivation-rank-controls-fold: that measures the rank of generator commutators in one globally conjugate presentation-double normal form; this is the label-energy obstruction for an arbitrary finite-group block-monomial presentation model.
---

**ESTABLISHED MINIMAL BLOCK-MONOMIAL ESCAPE.** Let `F_0` be a countable
free presentation group and let

```text
rho_n:F_0 -> L_n wr Sym(I_n)                            (SBL1)
```

be exact homomorphisms, represented block-monomially through faithful
`pi_n:L_n->U(r_n)`, with finite `L_n`.  Let

```text
N_2={w:||rho_n(w)-1||_2 ->_omega 0},
H=F_0/N_2.                                              (SBL2)
```

For `A=(ell_i,sigma)` define its literal label activity

```text
h_n(A)=|{i:sigma(i)!=i or ell_i!=1}|/|I_n|.             (SBL3)
```

Then the regular-label permutation extraction is faithful on `H` if and
only if

```text
w in N_2  ==>  h_n(rho_n(w)) ->_omega 0.                (SBL4)
```

In particular, if `H` is nonsofic, there are a fixed `w in N_2` and
`alpha>0` such that, on an ultralarge set,

```text
h_n(rho_n(w))>=alpha.                                   (SBL5)
```

Writing `rho_n(w)=(ell_(n,i),sigma_n)`, `(SBL2)` and the exact identity
`(BLR3)` imply

```text
|{i:sigma_n(i)!=i}|/|I_n| ->_omega 0,                  (SBL6)

(1/|I_n|) sum_(sigma_n(i)=i)
 (1-Re tr_(r_n)(pi_n(ell_(n,i)))) ->_omega 0.           (SBL7)
```

Combining `(SBL5)--(SBL7)`, for every fixed `eta>0` the set

```text
{i:sigma_n(i)=i,
   ell_(n,i)!=1,
   1-Re tr_(r_n)(pi_n(ell_(n,i)))<eta}                 (SBL8)
```

has lower ultralimit density at least `alpha`.  Thus a nonsofic
block-monomial tracial image requires a **fixed kernel word** carried by a
positive density of literally nontrivial labels whose normalized unitary
character gaps tend to zero.

For approximate maps rather than exact free-presentation maps, the same
statement applies to a fixed multiplication-defect word: the regular-label
permutation extraction can fail to descend only when a defect which is HS
null retains positive literal label activity.  This is the minimal soft
observable absent from every signed or uniformly discrete finite-label
model.

This necessity concerns a block-monomial model whose own GNS group image is
nonsofic.  An IR construction instead tries to extract a quotient
representation on an adjoint spectral sector; the present theorem neither
forces nor forbids that sector, because a sofic source can have a nonsofic
quotient.

DERIVATION
soft-kernel-label-necessity-proof
