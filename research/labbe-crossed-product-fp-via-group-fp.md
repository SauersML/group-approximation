---
rg: 2
id: labbe-crossed-product-fp-via-group-fp
kind: route
title: Finite presentation of Labbé's derived full group would make its crossed-product algebra finitely presented
target: labbe-wang-shift-crossed-product-is-finitely-presented
requires:
  - labbe-shift-derived-full-group-is-finitely-presented
  - zd-derived-full-group-fp-forces-quantum-rigidity
  - sft-crossed-product-fp-iff-quantum-rigid
  - minimal-aperiodic-wang-shift-exists
artifacts:
  - research/artifacts/labbe-group-fp-forces-quantum-rigidity-2026-09-13.md
---

1. **The shift.** `Omega_U` is a free minimal nearest-neighbour SFT (`minimal-aperiodic-wang-shift-exists`).
2. **Rigidity.** If `D([[Omega_U]])` is finitely presented (first requirement), then
   `zd-derived-full-group-fp-forces-quantum-rigidity` makes `Omega_U` `D`-quantum rigid over `F_q`, for
   large `D` and every prime power `q` prime to `15`.
3. **The algebra.** `sft-crossed-product-fp-iff-quantum-rigid` then makes `LC(Omega_U, F_q) ⋊ Z^2`
   finitely presented.

**Scope.** This gives the target for those `q` only. The certificate behind step 2 has denominators
divisible only by `3` and `5`.

**No false establishment.** The first requirement is OPEN, so this route does not fire. Read in
reverse, it says that refuting the target for such a `q` refutes finite presentation of the group.
