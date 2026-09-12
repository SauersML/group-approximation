---
rg: 2
id: kt-double-is-nielsen-semidirect-product
kind: claim
title: The binary Kun--Thom double is the explicit affine Nielsen semidirect product
distinct_from:
  free-lamp-radical-is-free: that computes the sofic radical of the larger free-lamp amalgam G *_Gamma (Gamma x K); this computes the fold kernel and the exact actor action for the symmetric double itself.
  finite-dimensional-nielsen-cocycle-models-kill-mark: that proves an obstruction for exact finite-dimensional covariant models after the Nielsen action is given; this supplies the group and reduced-crossed-product identification on which that obstruction acts.
artifacts:
  - notes/UNIQUE_TRACE_KUN_THOM_DOUBLE.md
  - research/artifacts/kt-double-mf-trace-literature-audit-2026-08-30.md
---

For the binary Kun--Thom pair put

```text
X=G/Gamma,              o=Gamma,              D=G *_Gamma G.
```

Let

```text
N=F({b_x:x in X-{o}}),                         b_o=1,
alpha_g(b_x)=b_(g x)b_(g o)^(-1).              (KNS1)
```

Then the fold retraction `D->G` splits and gives a canonical isomorphism,
after choosing the first vertex copy as the splitting,

```text
D ~= N semidirect_alpha G.                     (KNS2)
```

Consequently there is a trace-preserving C-star isomorphism

```text
C*_r(D) ~= C*_r(N) crossed_(alpha,r) G.         (KNS3)
```

Thus reduced MF of the Kun--Thom double is a strong-convergence problem for
one completely explicit action on a free group.  The obstruction is not in
the radical: `N` is a free group of countably infinite rank.  It is in the
affine basepoint correction `b_(g o)^(-1)` in `(KNS1)`.

DERIVATION
kt-double-nielsen-semidirect-proof
