---
rg: 2
id: sp21-pro-p-finite-rank-iff-finite-pro-p-congruence-kernel
kind: claim
title: A pro-p completion of a cocompact arithmetic Sp(n,1) lattice has finite rank iff its pro-p congruence kernel is finite
distinct_from:
  sp21-lattice-has-congruence-subgroup-property: that is the open assertion that the whole congruence kernel is finite; this is the established equivalence, at one prime p, between finite rank of a pro-p completion and finiteness of the p-part of that kernel, and it decides neither side
  sp21-bounded-rank-simple-quotients-almost-all-congruence: that classifies bounded-rank finite simple images through ultraproducts; this classifies p-adic analytic pro-p completions through the adjoint representation, with the same superrigidity input
  normal-subgroups-of-arithmetic-lattices-are-congruence-open: that controls congruence quotients of proper quotients; this identifies which pro-p completions can be larger than the congruence completion
artifacts:
  - research/artifacts/hyperbolic-rf-pro-p-2026-09-12.md
---

**ESTABLISHED.** Setting:
- `k` is a number field with ring of integers `O`;
- `G` is a simply connected, absolutely almost simple, `k`-anisotropic `k`-group;
- `G(k_v)` is `Sp(n,1)` (`n >= 2`) or `F_4^(-20)` at one archimedean place and
  compact at the others;
- `Γ <= G(O)` has finite index;
- `p` is a prime, and `Γ(p) = Γ ∩ G(O, pO)`.

For every finite-index `Δ <= Γ(p)`, write `Δ̄_p` for the closure of `Δ` in
`∏_(v|p) G(O_v)`, a pro-p group. Let `π_Δ: Δ̂_p ->> Δ̄_p` be the natural map from
the pro-p completion. Then

```text
rank(Δ̂_p) < ∞   iff   ker(π_Δ) is finite.
```

**Consequences.**
- The necessary condition recorded in
  `sp21-lattice-few-alternating-and-large-rank-quotients` for the transvection
  mechanism (infinite rank of a pro-p completion) is exactly an infinite pro-p
  congruence kernel. That is failure of the congruence subgroup property at `p`.
- The congruence subgroup property makes every such completion finite rank.

**Proof outline** (full proof in the artifact).
1. **Finite rank ⟹ perfect Lie algebra.** Finite rank gives an open uniform
   subgroup with `Q_p`-Lie algebra `𝔭`. (T) makes `𝔭` perfect.
2. **Semisimple.** Superrigidity and first-cohomology vanishing kill the unipotent
   radical of the Zariski closure of the adjoint image, so `𝔭` is semisimple.
3. **The kernel is finite.** Superrigidity makes the adjoint action on the ideal
   `𝔫 = Lie(ker π_Δ)` continuous in the congruence topology. So `ker π_Δ` acts
   trivially on `𝔫`, which forces `𝔫 = 0`.

The route `sp21-pro-p-finite-rank-congruence-kernel-proof` gives the proof. Trust
surfaces: Margulis-form superrigidity (Corlette, Gromov–Schoen, Margulis) and
Raghunathan's vanishing theorem. Novelty was not checked; the method is
Lubotzky's (Annals 1983).
