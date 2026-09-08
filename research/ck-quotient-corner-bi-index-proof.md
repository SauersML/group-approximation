---
rg: 2
id: ck-quotient-corner-bi-index-proof
kind: route
title: Preserve an infinite root image at every proper level and separate its simple-core double cosets
target: ck-quotient-corner-has-infinite-bi-index
requires: [elementary-root-kernel-equals-level, ck-envelope-level-ideal-screen]
artifacts:
  - research/artifacts/ck-quotient-and-cover-bi-index-obstruction-2026-09-08.md
---

Let `q:Gamma->Q` be the quotient map. By
`elementary-root-kernel-equals-level`, each root image is `(U/I,+)`.
By `ck-envelope-level-ideal-screen`, `S` embeds in `(U/I)^x`, so `U/I`
is infinite and no `1-s`, `s!=1`, belongs to `I`.

If `q(diag(s,1,...,1))=1`, the identity

```text
[e_12(1),diag(s,1,...,1)]=e_12(1-s)
```

puts `1-s` in the kernel of that root, hence in `I`. Therefore `s=1`.
Thus `D_N=q(D)` is an infinite simple group and has trivial center.

Put `A=q({e_23(a):a in U})`. It centralizes `D_N`, since the original
root group commutes with the original corner. Hence
`A intersect D_N <= Z(D_N)=1`. If `a,b in A` and
`D_N a D_N=D_N b D_N`, write `b=d_1 a d_2`. Commutation gives
`a^-1 b=d_1d_2 in A intersect D_N`, so `a=b`. This embeds
`A ~= (U/I,+)` as the asserted family of distinct double cosets.

Embedding `Q` in an overgroup cannot identify two of these double cosets:
the multipliers still belong to the same `D_N`. For a surjection
`pi:P->Q` with `pi(T)=D_N`, the map `T p T -> D_N pi(p) D_N` is a
well-defined surjection of double-coset sets. Thus the upstairs set is
infinite as well, without any assumption on `ker(pi)` or on lifts of `A`.

Finally, if `T<=H<=P` with `[H:T]=m<infinity`, each `H p H` is a union
of at most `m^2` double cosets of `T`: use representatives for `T\H`
on the left and `H/T` on the right. Finitely many `H` double cosets would
therefore imply finitely many `T` double cosets, a contradiction. QED
