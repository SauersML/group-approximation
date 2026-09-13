---
rg: 2
id: kk-tensor-power-norm-functor-to-kk-zp-proof
kind: route
title: Shift-averaged Kasparov partitions, the cylinder filtration and localization give the norm functor
target: kk-tensor-power-norm-functor-to-kk-zp
requires: [zp-detection-equals-meyer-nadareishvili-sufficiency]
artifacts: [research/artifacts/uct-kk-norm-functor-2026-09-13-part1.md, research/artifacts/uct-kk-norm-functor-2026-09-13-part2.md]
---

Derivation in the two artifacts.  Unreviewed.

- **Item 1** is part 1, Theorem A, from Propositions 1–3 of part 1:
  - the equivariant cycle `(E^(⊗̂p), φ^(⊗̂p), Σ_i M_i^(1/2) F_i)`;
  - the averaging lemma for Kasparov partitions;
  - independence of the partition, homotopies restricted to the diagonal of
    `[0,1]^p`, and the zero and identity cycles.
- **Item 2** is part 2, Theorem B, which uses item 1 on the cone `C_f`.
- **Item 3** is part 2, Theorem C.  It uses item 2 and the localization
  universal property of `KK`.
- **Item 4** is part 2, §7 item 2.  It uses the description of `B^G` recorded
  in `zp-detection-equals-meyer-nadareishvili-sufficiency`.
- **Item 5** is part 2, §7 item 4.

Standard inputs not re-read from the sources:
- Kasparov's technical theorem for `p` slots, by induction from two;
- exactness of `⊗_min` on c.p.-split extensions;
- exact triangles in `KK^G` from equivariantly c.p.-split extensions;
- the localization description of `KK` (Meyer 2000; Meyer--Nest 2006, §2);
- Rosenberg--Schochet commutative models for bootstrap algebras.
