---
rg: 2
id: regular-reynolds-bad-levels-cannot-be-quarantined
kind: claim
title: Moving Reynolds bad levels cannot be quarantined by the active BS cut
distinct_from:
  regular-short-low-frequency-bs-source-hull-is-sublinear: that constructs an o-dimensional invariant hull from the actual low-frequency cubic source; this shows that a moving bad Green level or a small tangent coefficient space does not satisfy that source hypothesis.
  relative-tangent-spectral-cuts-can-have-full-bs-hull: that gives a rank-two abstract BS packet example; this gives the arithmetic diagonal version inside regular congruence quotients.
  right-displacement-reynolds-scalar-cb-complete: that reduces the exact cb norm to the scalar Green norm; this proves a divergent scalar level cannot be discarded merely because its scalar coefficient space is small.
---

**ESTABLISHED; PACKET-LEVEL ACTIVE/PASSIVE RESCUE IS IMPOSSIBLE.**  Let
`Q` be a finite congruence quotient in the left-regular endpoint, put

```text
B=<R,S>,                 N=<R,X>,
```

and let `chi` be trivial on `<R>` and satisfy `chi(X)=-1`.  The scalar
tangent space is

```text
D_Q=Ind_N^Q chi
    ={f: L_R f=f, L_X f=-f}.                           (RBQ1)
```

There are two separate rank firewalls.

First, a sequence of escaping congruence quotients `Q_n` gives a regular
microstate sequence `lambda_(Q_n)`: every fixed nonidentity group word is
nontrivial in all sufficiently deep quotients, so its normalized regular
trace is zero.  This sequence has **all** of its physical dimension in the
single moving quotient level `Q_n`.  Consequently, if large scalar Green
norms occur along such a sequence, declaring the corresponding deep
conductor or large torus-index levels active deletes relative rank one, not
`o(1)`.

Second, the dimension of the scalar coefficient space does not measure the
physical carrier of its operators.  An element `f in D_Q` is determined by
one scalar on each `N`-coset.  Choosing every scalar nonzero gives

```text
rank(M_f)=|Q|,                                          (RBQ2)
```

even when `dim(D_Q)/|Q|=1/|N|` tends to zero.

There is also an exact small-carrier/full-hull obstruction.  Choose one
point `q_C` in every left `B`-orbit `C=Bq` of `Q`.  Let `Omega` be the union
of the `N`-cosets `Nq_C`, and on each such coset use the sign function
forced by `chi`; put the function equal to zero elsewhere.  Then

```text
f_Omega in D_Q,
|supp(f_Omega)| <= [Q:B]|N|,
Hull_B(supp(f_Omega))=Q.                               (RBQ3)
```

For the prime-field `PSL_2(F_p)` endpoints, `B` is the projective Borel and
`N` the projective split-torus normalizer, so

```text
|supp(f_Omega)|/|Q| <= |N|/|B| = O(1/p),              (RBQ4)
```

while the full `(R,S)`-invariant hull of the spectral carrier of
`M_(f_Omega)` is the whole `l2(Q)`.  Repeated `N`-cosets cause no problem:
retain one copy and choose its sign once.  Every selected coset contains
its chosen `q_C`, so the support still meets every `B`-orbit.

Thus neither moving-level mass, scalar tangent dimension, nor small
high-amplitude rank supplies the `o(d)` **invariant physical hull** needed
by the established active-block surgery.  A scalar Green divergence cannot
be rescued automatically by the active/passive cut.

This does not prove that the arithmetic Green norms diverge.  It gives the
sharp surviving possibility if they do: one would need a new
**mode-specific** theorem saying that every actual near-extremizer for
`C_Q^dagger` has support whose complete `B`-orbit hull is `o(|Q|)`.  Such a
statement does not follow from the uniform `L2` tangent gap (which controls
only Hilbert mass) and is refuted for arbitrary vectors of the same scalar
tangent module by `(RBQ3)--(RBQ4)`.
