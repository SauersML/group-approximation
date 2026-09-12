---
rg: 2
id: degree-four-kl-source-face-retraction
kind: claim
title: The degree-four involution-pair KL gadget is not closed by its source face and packet definitions
artifacts:
  - research/degree-four-kl-source-face-retraction-proof.md
distinct_from:
  kl-test-word-conjunction-fence: that rules out coefficient-free test-word compression in arbitrary overgroups; this audits one self-referential degree-four Reidemeister--Schreier orbit.
  leavitt-omega-has-an-explicit-distorted-target: that proves the source and target commutator values in the actual Leavitt group; this shows those values alone do not make the proposed four orbit cells into a coefficient-killing picture.
  kl-violating-equation-over-leavitt-unit-group: that needs injectivity failure for a full Leavitt coefficient copy; this countermodel is deliberately only for the displayed packet relations and is not a homomorphism from a full coefficient copy.
---

Put

```text
b=r^2 a r^(-2),       d=p^2 c p^(-2),
[a,b]=1,              [c,d]=x_15(s_0^2) != 1.
```

For the degree-four sign pattern `++-++-++` with slots

```text
(r,e,a,c,1,b,d,p),
```

the four cyclic-cover relators, the definitions of `b,d,r=qp`, the source
face `[a,b]=1`, all packet torsion, and even the complete root-orbit
commutation pattern do **not** force `[c_0,d_0]=1`.

There is an explicit retraction of that abstract packet presentation onto a
right-angled Coxeter-by-cycle group in which `[c_0,d_0]` is a reduced
nonidentity graph-product word.  Consequently no four-cell certificate whose
only internal coefficient face is `[a_i,b_i]=1` can prove the desired target
collapse.  A successful use of this candidate must invoke further Leavitt
relations coupling the nominal generators inside a full coefficient copy.

This is not an embedding or retraction for the actual Leavitt relative
quotient: the packet assignments need not extend to homomorphisms from
`EL_20(L_(F_2)(1,2))`.  It is an exact fence around the proposed
source-law-only mechanism.
