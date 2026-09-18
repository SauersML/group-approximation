---
rg: 2
id: labbe-crossed-product-fp-via-v-full-group-fp
kind: route
title: Finite presentation of the V-times-Labbé full group, as P2 asserts, would make Labbé's crossed-product algebra finitely presented over every field
target: labbe-wang-shift-crossed-product-is-finitely-presented
requires:
  - v-times-minimal-free-sft-alternating-full-groups-are-fp
  - fp-v-times-subshift-full-groups-force-quantum-rigidity
  - sft-crossed-product-fp-iff-quantum-rigid
  - minimal-aperiodic-wang-shift-exists
---

1. **The shift.** `Ω_U` is a nearest-neighbour SFT on which `Z^2` acts freely and minimally
   (`minimal-aperiodic-wang-shift-exists`). `Z^2` is infinite and finitely presented.
2. **P2 at `Ω_U`.** The first requirement makes `A(T)` finitely presented for
   `T = G_V × (Z^2 ⋉ Ω_U)`.
3. **Rigidity.** The corollary of `fp-v-times-subshift-full-groups-force-quantum-rigidity` then makes
   `Ω_U` `D`-quantum rigid over every field for all large `D`. By that node's route, Section 4, this
   holds for the metric of `sft-crossed-product-fp-iff-quantum-rigid` and some `D >= 1`.
4. **The algebra.** `sft-crossed-product-fp-iff-quantum-rigid` makes `LC(Ω_U, k) ⋊ Z^2` finitely
   presented for every field `k`, and in particular over every `F_q`.

**Compared with `labbe-crossed-product-fp-via-group-fp`.** That route starts from the derived full
group of Labbé's shift without `V`, and gets the target only for `q` prime to `15`. This one starts
from the full group with the `V` factor, which is the P2 instance, and gets every field.

**No false establishment.** P2 is OPEN, so this route does not fire.

**Read in reverse.** A refutation of the target, over any single finite field, refutes P2. For example,
`labbe-tiles-admit-periodic-quantum-tilings-at-every-scale` together with
`periodic-quantum-tilings-refute-quantum-rigidity` would do it. So P2 is at least as hard as the
Labbé crossed-product problem. Through `free-minimal-rigid-sft-via-labbe-shift`, it is also at least
as hard as `free-minimal-z2-sft-is-quantum-rigid`.
