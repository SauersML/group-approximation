---
rg: 2
id: jacobson-two-braid-infimum-is-zero
kind: claim
title: The Jacobson two-braid group has an amenable seven-ray quotient retaining its full packet and its matrix infimum is zero
invalidates:
  - property-t-free-existence-via-jacobson-two-braid-gap
distinct_from:
  jacobson-two-braid-mixed-packet-gap: that asks whether the all-dimensional infimum is positive; this constructs an explicit amenable marked quotient and proves that the infimum is zero.
  binary-jacobson-joint-shortest-cells-have-a-finite-marked-model: that asks for an exact finite marked image; this supplies a marked norm-corona image and makes no finite-image claim.
  ptfree-sep7-jacobson-packet-escapes-finitary-shift: that invalidates a finitary-shift inclusion for the literal three-ray packet; this changes the tail representation to its permutation action on seven rays and constructs an amenable quotient of the two-braid presentation.
  jacobson-tail-braid-exactification-and-standard-carrier: that compares the two-braid infimum with the infimum having the tail braid exact; this proves both numbers are zero.
artifacts:
  - research/artifacts/jacobson-two-braid-seven-ray-countermodel-2026-09-08.md
---

**ESTABLISHED.** Let `G=GL_3(F_2)`, `F=G_Q x G_P`, and let `K` be
the head copy of `GL(<e_1,e_3>)` fixing `e_2`. Put

```text
b=(w_23,w_23),         d_P=(1,w_13),
w=(I+E_13,1),
Gamma=<F,h | h^2=1, [h,K]=1, (hb)^3=1, (hd_P)^3=1>.
```

There is an explicit countable amenable group `A_7` and a surjective
homomorphism `Gamma -> A_7` whose restriction to the entire finite packet
`F` is injective. In particular the head mark `w` survives.

Consequently the infimum from
`jacobson-two-braid-gap-characterizes-mark-collapse` satisfies

```text
gamma=0.
```

The exact-tail comparison further gives `gamma_tail=0`. Thus first-braid
defects tend to zero on marked exact finite packets even when the tail
braid and overlap commutation are imposed exactly.

The quotient acts linearly over `F_2` on seven rays indexed by the
nonzero vectors in `F_2^3`. The tail uses the seven-point permutation
action of `G`, and the head uses its natural action on three boundary
vectors. An explicit involution gives both braids. Every generator is
eventually a ray permutation with integer shifts, so `A_7` has a locally
finite kernel and a virtually abelian image. It is therefore amenable,
and the established amenable-group theorem makes it operator-MF.

The same quotient also satisfies the literal additional relation

```text
[h (I+E_13)_P h,(I+E_23)_P]=1.
```

Thus this first nonpermutation-tail same-root commutation does not yield
marked collapse either.

This refutes the positive two-braid gap, not the independent non-MF
existence goal or the full Jacobson head-collapse claim. It does not assert
that `Gamma` itself is MF or that the infimum is attained by an exact
finite-dimensional representation. A successful Jacobson obstruction must
use additional mixed relations involving nonpermutation tail coefficients.

DERIVATION
jacobson-two-braid-seven-ray-countermodel-proof
