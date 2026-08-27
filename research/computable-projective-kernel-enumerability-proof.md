---
rg: 2
id: computable-projective-kernel-enumerability-proof
kind: route
title: Dovetail strict trace inequalities and separate the regular sector from the payload trace
target: computable-projective-kernel-has-reversed-enumerability
requires:
  - non-ce-trace-does-not-promote-to-subgroup-character-gap
  - diagonal-tensor-trace-powers-forget-full-gns-tensor
  - free-label-orthogonalization-erases-payload-trace
---

For each word `w`, compute rational approximations `q_m(w)` to
`|tau(w)|` with certified error at most `2^-m`.  Dovetail over `(w,m)` and
enumerate `w` as soon as

```text
q_m(w)+2^-m < 1.
```

Every enumerated word lies outside `K_tau`.  Conversely, if
`|tau(w)|<1`, the strict gap is eventually larger than `2^(1-m)`, so the test
eventually enumerates `w`.  Hence `F minus K_tau` is c.e. and `K_tau` is
co-c.e.  If `K_tau` were c.e. as well, dovetailing the two enumerations would
decide membership.

The diagonal powers do not alter this equality set:

```text
|tau(w)|^(2n)=1  iff  |tau(w)|=1.
```

Their pointwise limit is the indicator of `K_tau`; equality to one in that
limit is the universal statement that no strict-gap test ever fires.  Thus
the limit does not reverse the enumeration polarity.

Now let `chi=tau|_(K_tau)` and centralize `K_tau` in the free group.  The
`chi`-sector in Thom's central extension theorem is defined from the quotient
group and cocycle, so its canonical coefficient is zero on every nonidentity
quotient element.  In free-word coordinates this is the displayed
`tau_reg^chi`, not the original coefficient `tau(w)`.  The original GNS
representation is only a representation of the corresponding twisted full
group algebra.  Its trace need not be normal with respect to the twisted
regular von Neumann algebra, so non-CE does not pass to the canonical sector.

For the sharp countercheck, take the RACG and non-CE character from the fixed
BCS source.  Since the Connes-embeddable trace locus is closed, its complement
is open, and the convex sum with sufficiently small positive regular weight
remains non-CE.  Equality
in the triangle inequality at a nonidentity `g` would require the regular
coefficient `0` to have modulus one, so its scalar kernel on `G` is trivial.
RACGs have decidable word problem, making the pulled-back free-word kernel
decidable.  Yet their regular group factors are CE.  This proves both that
effectivity and retention are independent and that centralizing a recursive
character kernel does not bypass `effective-nonce-twisted-factor-exists`.
