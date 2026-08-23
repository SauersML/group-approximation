---
rg: 2
id: native-bs-square-root-counterpacket-proof
kind: route
title: Put compressed Weil packets at the Fermat one-power level
target: native-bs-level-has-strict-square-root-counterpackets
requires:
  - exact-torsion-frame-has-rank-one-strict-counterpackets
  - bs14-one-power-level-is-a-native-short-commutator
  - sl2-half-explicit-strict-flexible-separation
---

Take the compressed even-Weil packet over a prime `p=1 mod 4` from
`sl2-half-explicit-strict-flexible-separation`.  In square-free Iwahori
coordinates it has dimension `(p-1)/2`; its BS covariance, involution and
inversion rows are exact, its two cubic rows have normalized-HS defect at
most `C_0/sqrt(p)`, and it stays a fixed distance `c>0` from every exact
same-dimensional Iwahori tuple.  Equivalently one may use the exact
`C_2*C_3*C_3` normalization in
`exact-torsion-frame-has-rank-one-strict-counterpackets`; the fixed word
coordinate changes preserve all estimates up to universal constants.

Put

```text
K=p-1.                                                (NSP1)
```

The unipotent core generator has order `p`.  Fermat's theorem gives

```text
p | 4^(p-1)-1=4^K-1,                                 (NSP2)
```

so

```text
S_K^(4^K-1)=1.                                       (NSP3)
```

The BS covariance is exact.  Therefore
`bs14-one-power-level-is-a-native-short-commutator` turns `(NSP3)` into the
exact native row

```text
[R_K^K,S_K]=1.                                       (NSP4)
```

Since `p=K+1`, the cubic estimate is at most `C/sqrt(K)` after changing one
universal constant.  Strict separation gives `(NSQ3)`.  If a strict basin
had `delta_K sqrt(K)->infinity`, then `(NSQ2)` would eventually place this
tuple inside that basin, contradicting `(NSQ3)`.  This proves `(NSQ4)`.

Finally the uncompressed even-Weil representation restores one deleted
line and is an exact endpoint in dimension `(p+1)/2`; its generalized
distance from the compressed packet is `O(p^(-1/2))=O(K^(-1/2))`.  Thus the
same example is compatible with flexible repair and proves no more than the
claimed strict firewall.
