---
rg: 2
id: bs14-character-split-leaves-only-the-regular-microstate-face
kind: claim
title: Character rigidity removes moving finite levels but leaves exactly the regular BS14 microstate face
distinct_from:
  bs14-global-atoms-are-moving-congruence-restrictions: that classifies exact finite-dimensional atoms; this decomposes an arbitrary tracial ultraproduct character without naming their levels.
  bs14-bounded-moments-cannot-extract-congruence-level: that rules out finite scalar level fingerprints; this explains why no level fingerprint is needed on the hyperfinite character face.
  iwahori-local-global-defect-question: that is the full flexible stability endpoint; this records the exact central-face reduction and identifies the sole surviving face.
---

Put `A=PSL_2(Z[1/2])`.  Let a sequence of finite-dimensional approximate
representations define a homomorphism

```text
pi:A -> U(prod_U M_(d_n))                              (CSR1)
```

and let `tau` be its induced character.  Peterson--Thom character rigidity
says every extremal character of `A` is either finite-quotient or the
regular character `delta_e`.  Consequently the central decomposition of
`N=pi(A)''` has a central projection `z_fin` such that

```text
N z_fin       has hyperfinite GNS fibers,
tau|_(1-z_fin)N, after normalization, is delta_e.      (CSR2)
```

The first assertion permits arbitrary moving levels and arbitrary mixtures:
a direct integral of finite-dimensional factors is hyperfinite.  The second
holds because every non-finite extremal component is the same regular
character (the group is center-free).

Lift `z_fin` to matrix projections `p_n`.  Centrality gives

```text
||[p_n,pi_n(g)]||_2 ->0                               (CSR3)
```

for every fixed generator.  Polar compression therefore splits the
microstate, up to vanishing normalized-HS error, into its finite-character
and regular-character corners.  Known hyperfinite HS stability, obtained
from the same character-rigidity theorem, corrects the finite corner to
exact congruence representations.  It does so without extracting a minimal
level or a finite moment fingerprint.

Thus the only uncorrected corner is

```text
tau(pi(g))=delta_e(g),                                (CSR4)
```

the regular-character microstate face.  Its GNS algebra is the nonamenable
group factor `L(A)`, so hyperfinite HS stability does not apply.  On this
corner the exact BS core plus the involution and two cubic residuals are
simply the original presentation microstate problem.  A theorem saying that
their residual polar ledger produces a congruence-atom completion would be
the missing regular-microstate correction theorem, hence the unresolved
content of flexible HS stability rather than a consequence of character
rigidity.

This identifies the precise unavailable statement:

> Every regular-character microstate sequence of
> `PSL_2(Z[1/2])` is flexibly close to exact congruence representations,
> with boundary rank controlled by the two cubic energy.

No extra character classification or permanence theorem is missing.
Character rigidity has already exhausted the entire hyperfinite face.  A
counterexample, if one exists, may be canonicalized by deep regular
congruence tensors as in
`residual-finite-tensor-camouflages-iwahori-transfer-failures`, so imposing
the regular character does not make the remaining analytic geometry
artificially restrictive.

