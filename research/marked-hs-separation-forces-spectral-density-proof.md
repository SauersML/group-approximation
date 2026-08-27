---
rg: 2
id: marked-hs-separation-forces-spectral-density-proof
kind: route
title: Split the spectral second moment at a fixed marked threshold
target: marked-hs-separation-forces-spectral-density
requires: []
---

Put `p=tau_d(Q_theta)`.  Since `W` is unitary, every spectral value satisfies

```text
|lambda-1|^2 <= 4.
```

On the complement of `Q_theta` we have
`|lambda-1|^2 <= theta^2 alpha^2`.  Splitting the normalized trace of
`|W-1|^2` across the two spectral pieces gives

```text
alpha^2
 <= ||W-1||_2^2
 <= 4p + theta^2 alpha^2 (1-p).
```

Therefore

```text
alpha^2(1-theta^2)
 <= p(4-theta^2 alpha^2),
```

which is `(MSD)`.  The denominator is positive because a unitary has
`||W-1||_2<=2`.  Substituting `theta=1/2` yields

```text
p >= (3 alpha^2/4)/(4-alpha^2/4)
  = 3 alpha^2/(16-alpha^2).
```

Since `tau_d(Q)=rank(Q)/d`, this is a dimension-independent positive-density
spectral carrier.
