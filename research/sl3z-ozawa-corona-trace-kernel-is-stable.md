---
rg: 2
id: sl3z-ozawa-corona-trace-kernel-is-stable
kind: claim
title: The trace kernel of the corona of Ozawa's SL(3,Z) block algebra is a stable C*-algebra
distinct_from:
  sl3z-ozawa-block-corona-has-unique-trace: that computes the traces of the corona A and shows the trace kernel K is nonzero and traceless; this asks the finer structural question of whether K is stable (K ≅ K ⊗ 𝒦), which would make K quasitrace-invisible.
artifacts:
  - research/artifacts/quasitrace-corona-kernel-stability-2026-09-12.md
  - research/artifacts/quasitrace-kazhdan-block-corona-2026-09-12.md
---

**Statement (OPEN).** With `B`, `I`, `A = B/I`, the unique trace `τ_0`, and
`K = N_{τ_0} = ker(A → C*_r(SL(3,Z)))` as in `sl3z-ozawa-block-corona-has-unique-trace`,
the ideal `K` is a stable C*-algebra, `K ≅ K ⊗ 𝒦`.

**Why it matters.** If `K` is stable, then every bounded 2-quasitrace on `A` vanishes
on `K` (restriction of a quasitrace to the stable ideal is zero, by
`stw01-stable-algebras-are-bounded-quasitrace-invisible`), so
`sl3z-ozawa-block-algebra-quasitraces-are-traces` holds through the route
`sl3z-ozawa-block-qt-via-stable-kernel`. Stability is a third sufficient condition
for the invisibility of `K`, independent of exactness of `K` and of Cuntz
infinitesimality of `K_+`, and reduces the host case of STW Problem I to one
standard Hjelmborg–Rørdam stability question.

## Attempts

- **Growing-block halving (Hjelmborg–Rørdam).** For `a ∈ K_+`, `d_{τ_0}(a) = 0`, so
  the block compressions `a_k` are trace-thin (rank `o(n_k)`) while
  `n_k = p_k²+p_k → ∞`. There is asymptotically unbounded room to place an
  approximately orthogonal `b_k` with `a ≾ b`. This is the same room that powers the
  displacement estimate `approximately-orthogonal-unitary-translates-kill-quasitraces`.
  Dies at the same wall as the infinitesimality route: the halving witness `b` must
  lie in `K` (be a genuine element of `A` mapping to 0 in `C*_r(SL(3,Z))`), not just
  in the ambient corona `∏M/⊕M`, where the room manifestly exists. No mechanism was
  found here that lands `b` inside `K`.
- **Projection obstruction to stability.** A nonzero finite full projection in `K`
  would refute stability. The constant-function ghost projection is absent (`σ_k`
  acts on `ℓ²(X_k) ⊖ C1`). Whether a bounded-rank second-eigenspace ghost survives
  into `A` and lies in `K` is not determined here; if one does and is finite and
  full, `K` is not stable and this route dies.
- **Ghost/parabolic identification.** `K` carries the parabolic quasi-regular
  representations `λ_{Γ/P}` (`P = Stab` of a rational point) that are not weakly
  contained in `λ_Γ`. Whether the ghost ideal of an expander-box uniform Roe corona
  is stable is a plausibly known or approachable question in coarse geometry;
  not resolved here.
