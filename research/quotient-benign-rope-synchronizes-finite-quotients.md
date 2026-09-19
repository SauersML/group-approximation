---
rg: 2
id: quotient-benign-rope-synchronizes-finite-quotients
kind: claim
title: A quotient-compatible benign witness synchronizes all finite rope quotients
artifacts:
  - research/artifacts/quotient-benign-rope-synchronization-2026-08-25.md
distinct_from:
  positive-rope-profinite-edge-synchronization: that asks for an effective positive-branch witness with all the required residual-finiteness properties; this is the algebraic theorem converting such a witness into the synchronized quotient family.
  coordinate-swap-rope-does-not-compress-kernel: that replaces the asymmetric rope relation by a symmetric one and loses the quotient; here the coordinate swap is used only inside auxiliary finite quotients of the unchanged asymmetric rope.
---

Let `N` be normal in the finite-rank free group `F`, put `Q=F/N`, and let
`(K,e,L)` be a benign witness:

```text
K finitely presented,       e:F->K injective,
L<=K finitely generated,    e(F) intersect L=e(N).            (QBR1)
```

Assume in addition that there is a homomorphism `sigma:K->Q` satisfying

```text
sigma(e(f))=q(f) for every f in F,      L <= ker(sigma).       (QBR2)
```

Form the first rope group

```text
Gamma=<K,v | [v,l]=1, l in L>,
S=<e(F),v^-1 e(F)v><=Gamma,
tau:S->Q,   tau(e(f))=q(f),   tau(v^-1 e(f)v)=1.              (QBR3)
```

If `Gamma` and `Q` have effective cofinal finite quotient sequences, then
`A=Gamma times Q` has an effective cofinal finite quotient sequence `p_n`
such that the two graph-edge maps

```text
theta_0(s)=(s,1),              theta_1(s)=(s,tau(s))
```

have equal kernels after every `p_n`.  Thus the unchanged asymmetric Higman
rope satisfies the profinite synchronization condition `(PSH2)`.

The finite synchronization assertion needs no retraction of `Gamma` onto
`S`.  However, `(QBR2)` has a separate algebraic consequence: it makes `Q`
a retract of the finitely presented group `K/normalClosure(L)`, and therefore
forces `Q` to be finitely presented.  Thus this theorem is correct but cannot
apply to the non-finitely-presented positive FIN/INF scaffold; see
`quotient-benign-witness-forces-finite-presentation`.
