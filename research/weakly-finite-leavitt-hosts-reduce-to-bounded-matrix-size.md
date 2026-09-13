---
rg: 2
id: weakly-finite-leavitt-hosts-reduce-to-bounded-matrix-size
kind: claim
title: A weakly finite Leavitt unit host exists iff n-weakly finite hosts exist for every n, and algebraic ultraproduct hosts descend to their factors
distinct_from:
  weakly-finite-reflection-ideal-detects-weakly-finite-images: that gives, for one fixed ring, a finite certificate for 1 in J_omega in finitely many stages; this is compactness over all host rings at once, giving one matrix size n_0 that every host violates, through an ultraproduct of hosts.
artifacts:
  - research/artifacts/weakly-finite-hosts-construction-census-2026-09-12.md
---

**ESTABLISHED** (on paper, lane `w6-wf-construct`, 2026-09-12). Verification is requested from `w4-vf-linear-b`.

**Hosts.** A host is a nonzero ring `W` with `p·1 = 0` and a homomorphism `ρ : G -> W^x` such that:
- for `p = 2` and `G = L_(F_2)(1,2)^x`, `ρ` is nontrivial;
- for `p = 3` and `G = G_3 = L_(F_3)(1,2)^x`, `ρ(z) = -1`.

`W` is `n`-weakly finite when `AB = I_k` implies `BA = I_k` for all `k <= n`.

1. **Upward.** If for every `n` there is an `n`-weakly finite host, there is a weakly finite host. Equivalently,
   if no weakly finite host exists, there is one `n_0` such that every host has `AB = I_k ≠ BA` for some
   `k <= n_0`. So a proof that no host exists may work at one matrix size, uniform over all hosts.
2. **Downward.** Suppose an algebraic ultraproduct `∏_U A_j` of rings with `p·1 = 0` is a host.
   - Then `U`-almost every `A_j` has an injective homomorphism `V -> A_j^x`.
   - For `p = 2`, `U`-almost every `A_j` also has a nontrivial homomorphism `G -> A_j^x`.
   - So algebraic ultraproducts of finite rings, the level algebras `M_(2^j)(F_2)` included, are not hosts.
   - Realizing the compressors exactly in larger algebras helps only when those algebras already host `V`
     faithfully.

**Why.**
- **Part 1.** Take a nonprincipal ultraproduct of the hosts. Weak finiteness in size `k` is a first-order sentence
  that holds in the `n`-th host for `n >= k`, so Łoś carries it to the ultraproduct.
  - Binary: each `ρ_n` is injective, so the coordinatewise map is nontrivial.
  - Ternary: `ρ(z) = -1` coordinatewise.
- **Part 2.**
  - `ρ|V` is injective, because `ρ(V) = 1` would force `ker ρ = G`.
  - `V`, and for `p = 2` the group `G` itself, is finitely presented. So the relator equations and one inequality
    pass to `U`-many factors.
