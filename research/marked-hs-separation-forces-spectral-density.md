---
rg: 2
id: marked-hs-separation-forces-spectral-density
kind: claim
title: Hilbert-Schmidt separation of a unitary word forces a positive-density spectral carrier
distinct_from:
  index-density-is-amplification-stable: that observes how an already-defined extensive index scales; this produces a positive-density projection directly from marked Hilbert-Schmidt separation before any index has been constructed
  extensive-cosystolic-index-defect: that must turn marked separation into local syndromes which pay relator energy; this isolates the carrier-density part as automatic
---

Let `W in U(d)` and use normalized trace `tau_d` and normalized
Hilbert--Schmidt norm.  Suppose

```text
||W-1||_2 >= alpha > 0.
```

For any `0<theta<1`, let

```text
Q_theta = 1_{|W-1| >= theta alpha}
```

be the spectral projection of the normal operator `W`.  Then

```text
tau_d(Q_theta)
 >= alpha^2(1-theta^2)/(4-theta^2 alpha^2).             (MSD)
```

In particular, at `theta=1/2`,

```text
tau_d(Q_1/2) >= 3 alpha^2/(16-alpha^2) > 0.            (MSD1)
```

Thus a marked word separated in normalized Hilbert--Schmidt metric already
supplies `Theta(d)` spectral dimension uniformly in `d`.  A cosystolic or
qLDPC route does **not** need expansion to manufacture extensive carrier
mass; its genuinely missing step is to convert a fixed fraction of this
spectral carrier into bounded-overlap local syndromes whose mass is charged to
relator energy.
