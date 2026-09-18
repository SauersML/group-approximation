---
rg: 2
id: minimal-z2-sfts-have-no-uniform-language-time-bound-proof
kind: route
title: Diagonalize a hard Sturmian slope, then simulate its shift by a minimal Z^2-SFT
target: minimal-z2-sfts-have-no-uniform-language-time-bound
requires: []
artifacts:
  - research/artifacts/cantor-crossed-host-boundary-products-2026-09-17.md
---

Complete proof in Section 3 of the artifact.

1. **Sturmian shift.**
   - For computable irrational `α`, the Sturmian shift `Y_α` is minimal and has a decidable
     language.
   - Every length-`n` factor has `⌊nα⌋` or `⌊nα⌋ + 1` ones.
   - So a decider for `L_n(Y_α)` in time `T_Y(n)` approximates `α` within `1/n` in time
     `2^n (T_Y(n) + O(n))`.
2. **Diagonalization.**
   - Put `S(n) = 2^(n^3) · n · (max_(m <= n^2) T(m) + n^2)`.
   - Build nested rational intervals. Each machine index is attacked infinitely often, at
     increasing inputs `n_s`, and the `s`-th rational is avoided.
   - The limit `α` is computable and irrational. No machine approximates `α` within `1/n` in time
     `S(n)` for all large `n`.
3. **Import.** Durand–Romashchenko, arXiv:1802.01461, Theorem thm-main-min(a), verbatim: "For
   every effective minimal $\mathbb{Z}^d$-shift $\cal A$ there exists a minimal SFT $\cal B$ in
   $\mathbb{Z}^{d+1}$ such that $\cal A$ is simulated by $\cal B$ in the sense of
   Definition~\ref{def:subdynamics}."
   - In that definition the projection "takes a constant value along each column", and every
     configuration of $\cal A$ is represented.
4. **Transfer.**
   - With `d = 1`, `w ∈ L_n(Y_α)` if and only if some admissible `n × n` square of `X` has a
     bottom row `p` with `π(p) = w`.
   - So `T_Y(n) <= |Σ_B|^(n^2) (T_X(n) + O(n^2))`.
   - If `T_X(n) <= C·T(Cn) + Cn^2 + C`, the approximation time is eventually `<= S(n)`. This
     contradicts step 2.
   - The alphabet `Σ_B` depends on `α`, which is why `S` dominates every `c^(n^2)`.
