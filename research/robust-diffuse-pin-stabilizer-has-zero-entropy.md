---
rg: 2
id: robust-diffuse-pin-stabilizer-has-zero-entropy
kind: claim
title: Vanishing-HS approximate stabilizers of a diffuse pin have zero quadratic covering entropy
artifacts:
  - research/artifacts/flexible-packet-anchoring-2026-08-22.md
distinct_from:
  diffuse-pin-centralizer-has-zero-quadratic-covering: that treats exact commutation with the pinned matrix; this is the robust tubular version needed after flexible Hilbert--Schmidt exactification, where the aligning unitary only approximately fixes the pin.
---

Let `D_n in M_(d_n)(C)_sa` be uniformly bounded and suppose its empirical
spectral measures converge weakly to an atomless probability measure.  For
any sequence `eta_n -> 0`, put

```text
Z_n(eta_n)={U in U(d_n): ||U D_n U^* - D_n||_2 <= eta_n}.
```

Then for every fixed `epsilon>0`, in normalized Hilbert--Schmidt metric,

```text
limsup_(n->infinity) d_n^(-2)
  log K_epsilon(Z_n(eta_n),||.||_2)=0.                    (RDP1)
```

Consequently, for every fixed finite coordinate set `F` and every uniformly
operator-norm-bounded tuple `X_n in M_(d_n)(C)^F`,

```text
limsup_n d_n^(-2) log K_epsilon(
  {U^* X_n U:U in Z_n(eta_n)},||.||_2)=0.                (RDP2)
```

The conclusion is uniform over the reference tuples once `|F|` and their
operator-norm cutoff are fixed.
