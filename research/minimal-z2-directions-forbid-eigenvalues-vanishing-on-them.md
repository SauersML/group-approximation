---
rg: 2
id: minimal-z2-directions-forbid-eigenvalues-vanishing-on-them
kind: claim
title: A direction acting minimally on a Z^2 system kills no continuous eigenvalue, so square-hierarchical and quadratic-toral aperiodic tilings have no minimal rational direction
distinct_from:
  commuting-subshift-automorphisms-die-when-space-time-is-rf: that reduces the commuting-automorphism survivor to Z^2 subshifts with an expansive and minimal rational direction; this is the eigenvalue obstruction deciding which aperiodic Z^2 subshifts can have a minimal rational direction at all.
  aperiodic-sft-minimal-subsystem-with-expansive-minimal-direction: that is the open existence question; this kills its standard candidates and says where the remaining ones must come from.
---

**ESTABLISHED** (proof: `minimal-z2-directions-eigenvalue-proof`), as a lemma with two corollaries.  The
applications to named tilings rest on recalled literature and are marked as such.

**Lemma.**
- Let `Z^2` act minimally on a compact metric space `Y`, and let `v ∈ Z^2` act minimally.
- Let `θ ∈ Hom(Z^2, R/Z)` be a continuous eigenvalue: `f(g·y) = e^(2πiθ(g)) f(y)` for some continuous `f ≠ 0`.
- If `θ(v) = 0`, then `θ = 0`.

**Corollary A (finite factors).**
- If `Y` factors onto the translation action on a finite quotient `Z^2/Λ`, then the image of `v` generates
  `Z^2/Λ`.
- So a system with a non-cyclic finite factor, e.g. `Z^2/NZ^2` with `N ≥ 2`, has no minimal direction at all.

**Corollary B (toral factors).**
- Suppose `Y` factors onto `R^2/Γ` with `g` acting by translation by `g`.
- Suppose `Γ ⊆ F^2` for a real quadratic field `F`, and the dual lattice satisfies `Γ* ∩ Q^2 = 0`.
- Then no nonzero `v ∈ Z^2` acts minimally on `Y`.

**Invariant.**  The kernel of `θ ↦ θ(v)` on the group of continuous eigenvalues.

**Applications (literature recalled, not re-verified).**
- *Robinson's tiling.*  Its minimal subsystem factors onto `Z^2/2^k Z^2` for every `k`, through the positions
  of level-`k` supertiles.  So by Corollary A it has no minimal rational direction.
- *Square substitutions.*  The same holds for recognizable primitive substitution tilings with square expansion
  `N·Id`, `N ≥ 2`, and hence for their Mozes SFT covers.
- *Jeandel–Rao.*  Labbé proved that the Jeandel–Rao minimal subshift factors onto `R^2/Γ_0`, with
  `Γ_0 = ⟨(φ,0), (1,φ+3)⟩`.
  - Here `Γ_0 ⊆ Q(√5)^2`.
  - A rational `χ ∈ Γ_0*` has `χ_1 φ ∈ Z` and `χ_2(φ+3) ∈ Z`, so `χ = 0`.
  - Corollary B applies.

**What survives.**  A non-residually-finite `Y_ψ` inside an aperiodic SFT must avoid every non-cyclic finite
factor, and every quadratic toral factor of the kind in Corollary B.  The unexcluded candidate families are:
- rectangular hierarchies with coprime expansions, such as `2 × 3` product substitutions, where
  `Z/2^k × Z/3^k` is cyclic;
- codings of toral `Z^2` rotations with cubic or higher-degree parameters.

This is recorded in `aperiodic-sft-minimal-subsystem-with-expansive-minimal-direction`.
