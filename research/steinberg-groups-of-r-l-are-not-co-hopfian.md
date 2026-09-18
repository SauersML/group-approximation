---
rg: 2
id: steinberg-groups-of-r-l-are-not-co-hopfian
kind: claim
title: St_N(R_L) is not co-Hopfian, since the isometric twist of the last coordinate is injective and not surjective; its twist endomorphisms fix the central K_2(N,R_L) = Q^x, so their iterated cores are nontrivial
distinct_from:
  leavitt-resolvent-k2-stability-holds: that proves injective K_2-stability; this uses it to make the twist endomorphisms injective.
  leavitt-stabilization-kernels-are-one-step: that identifies the kernel of the twist with the stabilization kernel; this records the endomorphism-theoretic consequence for the shell window gate.
---

**ESTABLISHED** through `steinberg-groups-of-r-l-are-not-co-hopfian-proof`. Lane proof, not independently reviewed.
Elementary given the cited nodes. No priority is claimed.

**Statement.** Let `N >= 3`, `(e, f) = (s_1, s_2)`, and let `Σ^(e)` be the isometric twist of the last coordinate
(`leavitt-stabilization-kernels-are-one-step`).
1. **Not co-Hopfian.** `Σ^(e)` is an injective endomorphism of `St_N(R_L)` that is not surjective.
2. **All coordinates.** `Φ = St_N(c_e)`, induced by the corner embedding `c_e(r) = e r e*`, twists every coordinate. It
   is also injective and not surjective.
3. **Nontrivial iterated core.** `Σ^(e)` and `Φ` restrict to the identity on `K_2(N, R_L) ≅ Q^x`. So
   `∩_k Σ^(e)^k(St_N(R_L))` and `∩_k Φ^k(St_N(R_L))` both contain the central subgroup `K_2(N, R_L)`. `∩_k Σ^(e)^k`
   also contains the copy of `St_(N-1)` on the first `N - 1` coordinates.

## For the shell window gate

- Window-zero exclusions for co-Hopfian FW inputs (bh-free-33 47becd6b0, bh-kazhdan-inputs 7a95cf6d5) do not apply to
  `P = St_N(R_L)` as stated, since `P` is not co-Hopfian. `P` is FW, being Kazhdan.
- The exception recorded by bh-free-33 requires an injective endomorphism with **trivial** iterated core. The twist
  endomorphisms here have iterated core containing `K_2(N, R_L)`. So they do not supply the exception.
- Whether some other injective endomorphism of `St_N(R_L)` has trivial iterated core is open.
