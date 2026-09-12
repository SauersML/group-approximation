---
rg: 2
id: low-gap-transport-not-geometric-integralization
kind: claim
title: Low mixed-energy transport mass does not force near-identity block integralization
distinct_from:
  mixed-intertwiner-energy-transport-localization: that established theorem correctly localizes Hilbert-Schmidt mass on low-energy rectangular blocks; this claim shows why that scalar localization alone cannot be upgraded to geometric block matching.
  iwahori-fractional-transport-integralization: that target has extra opposite-modular-extension structure available in its intended application; this no-go only rules out deriving such an integralization from low mixed energy and overlap marginals alone.
---

There are sequences of pairs of exact finite-dimensional unitary
representations, with comparison unitary equal to the identity, for which

- the intertwining defect tends to zero;
- every block pair in the exact overlap transportation plan has bottom mixed
  intertwiner energy tending to zero; and
- every one of the four block-pair overlap masses is exactly `1/4`;

but any block-respecting unitary matching which retains `1-o(1)` of the
physical dimension stays a fixed normalized Hilbert--Schmidt distance from
the identity.  More precisely its squared distance is at least

```text
(2-sqrt(2))(1-o(1)).
```

Thus scalar low-energy transport, even with no bad transport mass at all,
does not by itself supply the near-identity physical integralization required
by the Iwahori repair program.  Any positive Iwahori theorem must use the
opposite modular extension geometry (or another singular-value/alignment
input) before or during integralization.