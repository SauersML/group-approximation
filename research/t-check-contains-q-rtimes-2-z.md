---
rg: 2
id: t-check-contains-q-rtimes-2-z
kind: claim
title: The finitely presented group T-check = <T-bar, x -> 2x> contains a subgroup isomorphic to Q x|_2 Z
distinct_from:
  q-x2-z-in-t-check-has-a-doubling-semiconjugacy: that is the structure theorem every copy must satisfy; this asks whether a copy exists.
  fg-pl-quasi-similarity-groups-contain-no-gl-2-q: that excludes Aff(Q) and GL_n(Q) from T-check; Q x|_2 Z is the stepping stone it leaves open.
  gl-n-q-embeds-in-fp-simple-group: that is the root problem; Q x|_2 Z <= Aff(Q) <= GL_2(Q) is a necessary sub-case for any host.
artifacts:
  - research/artifacts/gq-gq-obstruction-miner-invariant.md
---

**OPEN.** `T-check = <T-bar, δ>`, `δ(x) = 2x`, the finitely presented ascending HNN
extension of the lifts `T-bar` of Thompson's `T`, contains a subgroup isomorphic to
`D_2 = Q x|_2 Z = <Q, t | t q t^-1 = 2q>`.

**Why it matters.** `T-check` is the natural "Belk--Hyde--Matucci plus dilation" host.
It contains the divisible `(Q,+)` and the distorted `BS(1,2)`, so it passes the root's
obstructions O1--O4 (see `pl-quasi-similarity-groups-scale-rational-lines-by-ratio`).
It cannot contain `Aff(Q)` or `GL_n(Q)` (`fg-pl-quasi-similarity-groups-contain-no-gl-2-q`).
`D_2` is the largest piece of `Aff(Q)` its similarity-ratio lemma still allows. A
negative answer closes this host family for every stepping stone containing `D_2`.

Source: spark (1) of lane gq-obstruction-miner, 2026-09-17; not a printed question.

## Attempts

1. **Structure theorem (lane gq-deep-va-1, 2026-09-17).**
   `q-x2-z-in-t-check-has-a-doubling-semiconjugacy`. Any copy has `D` free with
   `ρ : D ≅ Q`, and doubling element `t = gδ`. There is a monotone semiconjugacy
   `h = lim δ^-m t^m` to the affine action. `h` is nowhere affine, and `t` is never
   conjugate to `δ`.
   - In the minimal case the question is equivalent to this dynamical problem:
     *find a PL-dyadic degree-2 circle map `u` with `u(θ+1/2) = u(θ)`, and a circle
     homeomorphism `η` with `η u η^-1 = (θ ↦ 2θ)` and `η^-1 R_s η in T` for every
     rational rotation `R_s`.*
   - The rotations alone are realizable, by Belk--Hyde--Matucci's `Q <= T-bar`. What
     is new is the compatibility with a PL degree-2 map.
2. **Multiplier rigidity, partial (same lane).** In the minimal case, let `p` be the
   fixed point of `u`, with one-sided slopes `2^a`, `2^a'`.
   - Conjugating by the PL maps `η^-1 R_s η` shows that every periodic orbit of `u`
     of period `k` has one-sided multipliers exactly `2^(ka)` and `2^(ka')`. The
     periodic points of `u` are exactly the `η^-1(s)` with `s` of odd denominator.
   - `u` has topological entropy `log 2`.
   - Two steps would kill the minimal case:
     - An entropy/Ledrappier argument giving `a = a' = 1`.
     - A PL Livšic step making the conjugacy `η` affine on some interval, which
       item 4 of the structure theorem forbids.
   - Neither step is proved yet: `u` need not be uniformly expanding, and the transfer
     function may have infinitely many breakpoints.
