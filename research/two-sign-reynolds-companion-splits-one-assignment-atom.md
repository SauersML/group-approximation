---
rg: 2
id: two-sign-reynolds-companion-splits-one-assignment-atom
kind: claim
title: A second central sign gives every assignment atom a balanced Reynolds companion
distinct_from:
  central-sign-assignment-atom-is-index-two-reynolds-surplus: That uses the payload sign itself for the index-two extension, so its source lies in the positive payload sector; this keeps the payload assignment fixed on both the source and exit and uses a second sign only for the companion split.
  schur-child-center-sign-flip-is-group-automorphism: That balances the two corrected Schur child types; this balances the two Reynolds companion signs while fixing the complete assignment atom.
---

**ESTABLISHED.**  Let `K,J` be commuting central involutions, let the
commuting Boolean variables be `x_1,...,x_k`, and fix an assignment `a`. Put

```text
H_a=<x_i K^(a_i):1<=i<=k>,       C_a=<H_a,J>,
A_a=e_(H_a)(1-K)/2.                                      (TRC1)
```

Adjoin an involution `s` which fixes `K,H_a` and satisfies

```text
s J s^(-1)=KJ.                                           (TRC2)
```

Then, in every finite tracial representation,

```text
p=e_(C_a)(1-K)/2=A_a(1+J)/2,
q=e_(H_a)(1-K)/2=A_a,                                   (TRC3)
```

and conjugation by `s` exchanges `p` with `q-p`. Hence

```text
tau(p)=tau(q-p)=tau(A_a)/2.                              (TRC4)
```

Now adjoin an HNN letter `t` for an injection `H_a->C_a` and require `t` to
commute with `K`. The cut-down Reynolds section

```text
v=t p
```

has `v^*v=p`, `vv^*<=q`, and its unused range complement

```text
E_a=q-vv^*                                               (TRC5)
```

satisfies

```text
tau(E_a)=tau(A_a)/2.                                     (TRC6)
```

Thus both the source and the paid exit retain the same payload assignment
and the same negative payload sign `K=-1`; only the auxiliary companion sign
`J` changes. This removes the source-sector mismatch in the one-sign
Reynolds section.

All groups in the construction are fixed and finite before the one HNN
edge. Fixed-table normalized-HS exactification, followed by the subgroup
Hecke estimate and polar correction, preserves `(TRC3)--(TRC6)` up to
`C sqrt(E)` for a dimension-independent constant.

