---
rg: 2
id: schur-toeplitz-envelope-has-proper-self-embedding
kind: claim
title: The packet-headed Toeplitz envelope has an explicit proper unital self-embedding
distinct_from:
  toeplitz-head-tail-unital-self-embedding: that treats the bare Toeplitz ring with scalar augmentation; this proves the same compressor remains injective after its head defect is identified with the nonlinear Schur idempotent.
  schur-idempotent-is-an-injective-toeplitz-defect: that embeds the packet algebra and identifies its forbidden idempotent with the head; this constructs the recursive tail endomorphism of the resulting ring.
---

Let `R_f` be the packet-headed ring of
`schur-idempotent-is-an-injective-toeplitz-defect`. The trivial packet
character, together with `x,y->1`, defines an augmentation

```text
epsilon:R_f->k,                 epsilon(P_f)=0.              (SSE1)
```

The formula

```text
sigma(a)=xay+epsilon(a)P_f                                  (SSE2)
```

is an injective proper unital ring endomorphism. It has the left inverse
`a |-> yax` on its image and shifts the defect tower:

```text
sigma^n(P_f)=x^nP_fy^n=e_n.                                (SSE3)
```

Indeed `P_fx=0`, `yP_f=0`, `yx=1`, and `xy+P_f=1`; these identities make
`(SSE2)` multiplicative and unital. Moreover `y sigma(a) x=a`, so it is
injective. Its image cannot contain `P_f`: if `sigma(a)=P_f`, applying the
left inverse gives `a=yP_fx=0`, contradicting `P_f!=0`.

Entrywise application gives a proper injective endomorphism of
`EL_5(R_f)`. Hence its ascending HNN extension is finitely generated,
recursively presented, and contains the base group by Britton normal form.
No finite presentation of `EL_5(R_f)` is asserted here: the pinned
Krstic--McCool theorem in Cairn concerns the Steinberg cover, while passing
to the elementary quotient may introduce a kernel not known to be finitely
normally generated.
