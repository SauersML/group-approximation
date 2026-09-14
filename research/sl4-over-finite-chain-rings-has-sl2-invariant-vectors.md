---
rg: 2
id: sl4-over-finite-chain-rings-has-sl2-invariant-vectors
kind: claim
title: Every unitary representation of SL_4(A), A a finite commutative principal ideal ring, has a nonzero vector fixed by the upper-left SL_2(A)
distinct_from:
  sl4z-representations-have-sl2-invariant-vectors: that is the published theorem for SL_4(Z), through congruence quotients SL_4(Z/N); this is the same statement for SL_4 over every finite commutative principal ideal ring, in any characteristic, which the ring models of subshift algebras need (quotients of F_q[t]).
  mdls-obstruction-is-affine-mechanism-plus-level-matching: that isolates which part of the SL_4 proof survives inside the affine group Z^3 x| SL_3; this transfers the whole SL_4 proof from Z/p^r to finite chain rings.
---

**ESTABLISHED (unreviewed).** Let `A` be a finite commutative principal ideal ring, e.g. `F_q[t]/(m(t))`, and
`SL_2(A) ≤ SL_4(A)` the upper-left block. Then every finite-dimensional unitary representation of `SL_4(A)` has
a nonzero `SL_2(A)`-invariant vector.

**Source.** Magee–de la Salle, arXiv:2312.03220v2, Proposition 2.1, verbatim: "For all N∈N, every non-trivial
finite dimensional representation φ of SL_4(Z/NZ) has a non-zero SL_2(Z/NZ)-invariant vector." Their proof
passes to prime powers by the Chinese remainder theorem and then runs Steps 1–3 over `Z/p^r`.

**What changes.** Nothing but the ring. `Z/p^r` becomes a finite chain ring `(A, πA)` with `(πA)^e = 0`, and
`exp(2πi ξ·u/p^r)` becomes `ψ(ξ·u)` for a generating character `ψ` of `(A,+)`; finite principal ideal rings are
Frobenius, so `ψ` exists. The step-by-step transfer is in the route and in
`research/artifacts/sk-cstar-mf-firewall-2026-09-13.md` §2.

**Use.** It supplies the invariant vectors in `periodic-word-model-representations-never-converge-strongly`.
There the rings are `F_q[Q]` for permutation matrices `Q`, i.e. quotients of `F_q[t]`.

Proof: route `sl4-over-finite-chain-rings-has-sl2-invariant-vectors-proof`.

**Review (sk-verify-5, 2026-09-13): PASS. Steps 0–3 were re-derived directly over a finite chain ring: layer G′ ≅ sl_4, the E_21-conjugation contradiction, the Heisenberg character, and induction with distinct characters ψ(dy+cz).** See `research/artifacts/sk-review-5-2026-09-13-part2.md` §3.
