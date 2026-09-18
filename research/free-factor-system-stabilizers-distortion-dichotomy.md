---
rg: 2
id: free-factor-system-stabilizers-distortion-dichotomy
kind: claim
title: The stabilizer in Out(F_n) of a free factor system is a Lipschitz retract when its coindex is one and distorted when its coindex is at least two
distinct_from:
  once-punctured-mcg-is-lipschitz-retract-of-out-free: that is the Hamenstädt--Hensel retraction onto a surface mapping class group; this classifies distortion of stabilizers of free factor systems.
---

**ESTABLISHED (literature import).**

> **Theorem 8 (Handel--Mosher, arXiv:1009.5018v3).** Given a free factor system F of F_n,
> (1) If coindex(F) = 1 then Stab(F) is a Lipschitz retract of Out(F_n), and therefore is
> undistorted in Out(F_n).
> (2) If coindex(F) ≥ 2 then Stab(F) is distorted in Out(F_n).

**Definitions (their Section 1).**
- A free factor system is a set `F = {[A_1], …, [A_K]}` of conjugacy classes of nontrivial subgroups
  such that `F_n = A_1 * ⋯ * A_K * B` for some (possibly trivial) `B`.
- `Stab(F) = {φ ∈ Out(F_n) : φ(F) = F}`, so the components may be permuted.
- `coindex(F) = (n−1) − Σ_k (rank(A_k) − 1)`.

**Other results imported with it.**
- Theorem 1 is the connected case. `Stab[A]` is a Lipschitz retract if `rank(A) = n−1`, and distorted
  if `rank(A) <= n−2`.
- Theorem 3: `Aut(F_{n−1})` is a Lipschitz retract of `Aut(F_n)`.
- Theorem 7: stabilizers of free splittings are Lipschitz retracts of `Out(F_n)`.

**Mechanism of distortion (their outline, p. 6).** An exponentially growing `θ` acts on a larger free
factor, and the conjugates `θ^k φ_0 θ^{-k}` stay in `Stab[A]` with linear `Out(F_n)`-length. Their
`Stab[A]`-length is bounded below by an exponentially growing letter count.

Nothing is reproved here, and there is no Lean counterpart.
