---
rg: 2
id: baumslag-gersten-equicontinuity-smallest-prime-proof
kind: route
title: The closure K of <a> is procyclic profinite and t-conjugate to the closure of <b>; b forces 2 to be prime to the order of K and then maps the closure of <b> onto a cyclic group of order ord_p(2) for the smallest prime p of K, whose prime factors are smaller than p
target: baumslag-gersten-equicontinuous-generator-acts-trivially
requires: []
artifacts:
  - research/artifacts/bh-bg-similarity-hosts-2026-09-12.md
---

The full proof is §5 of the artifact.

**Item 1 (profinite closures).**
- `Homeo(X)` with the uniform topology is a topological group.
- Since `X` is zero-dimensional, the stabilizers of finite clopen partitions
  are open subgroups, and they form a neighbourhood basis at `1`. So compact
  subgroups of `Homeo(X)` are profinite.
- By Arzelà--Ascoli, applied to `{a^m : m ∈ Z}`, the closure `K` of `<a>` is
  compact. So `K` is a procyclic profinite group.
- Conjugation by `t` carries `K` onto `K_b`, the closure of `<b>`.
- Let `P` be the set of primes `p` for which `K` has a continuous quotient
  `Z/p`. Write `U_m` for the closure of `<a^m>`.

**Item 2 (`2 ∉ P`).**
- Suppose `2 ∈ P`. Then `U_2` has index 2.
- Choose an open `O ∋ 1` in `Homeo(X)` with `O ∩ K ⊆ U_2`.
- `k ↦ k a k^-1 a^-1` is continuous, and `K_b` is a compact group. So some
  `j ≥ 1` has `b^j a b^-j a^-1 ∈ O`.
- That element is `a^{2^j - 1} ∈ K`, so it lies in `U_2`. This is impossible,
  since `2^j - 1` is odd.

**Item 3 (`b` normalizes).**
- `2 ∉ P`, so doubling is an automorphism of every Sylow factor of `K`. Hence
  `U_{2m} = U_m` for all `m ≥ 1`.
- So `b U_m b^-1 = U_{2m} = U_m`.
- Normalizers of closed subgroups are closed. So `K_b` normalizes `K` and
  every `U_m`.

**Item 4 (smallest prime).**
- Suppose `K ≠ 1`, and let `p = min P`. Then `p` is odd, and `U_p` has index
  `p`.
- Conjugation gives `ψ : K_b → Aut(K/U_p) = (Z/p)^×`. Its kernel is open by
  Item 3, so `ψ` is continuous.
- `ψ(b) = 2`, and `<b>` is dense. So `ψ(K_b) = <2 mod p>`, of order
  `o = ord_p(2) ≥ 2`.
- `K ≅ K_b`, so `K` has a continuous quotient `Z/q` for each prime `q | o`.
  Each such `q` lies in `P`.
- But `q | p - 1`, so `q < p`, a contradiction. Hence `K = 1`, and `a` acts
  trivially.

**Scope.** The proof needs `X` compact, zero-dimensional and metrizable, and
it needs the whole group `<a>` to be equicontinuous. It does not treat minimal
pieces on connected spaces; `baumslag-gersten-odometer-pieces-force-fixed-points`
does.
