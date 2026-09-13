---
rg: 2
id: kun-thom-relation-hosts-contain-sl-d-z-and-root-groups
kind: claim
title: Any free action hosting a Kun--Thom generalized Bernoulli relation receives a morphism from the Kun--Thom group that is injective on SL_d(Z) and on every root subgroup, so no linear group in any characteristic is a host
distinct_from:
  kun-thom-actions-have-no-host-without-p-torsion: that excludes hosts with no infinite elementary abelian p-subgroup through a torsion argument; this gives a root-injective morphism into every host, which also excludes hosts with p-torsion such as SL_3(F_p[t]) and every group linear over a field of characteristic p
  rigid-bernoulli-seed-relations-embed-their-group-in-the-host: that treats Bernoulli seeds, where mixing makes the kernel finite; this treats the non-mixing generalized Bernoulli actions over G/Γ ⊔ G, where the kernel is controlled through root subgroups instead
---

**ESTABLISHED (unreviewed).** Let `q` be a power of the prime `p`, `r,d >= 3`, and let
`Γ = EL_r(R_+) < G = EL_r(R) ⋊ SL_d(Z)` be the Theorem E pair of `kun-thom-nonsofic-wreath`, with
`R = F_q[x_1^(±1),...,x_d^(±1)]` and `R_+ = F_q[x_1,...,x_d]`. Let `(Y,ν)` be a nontrivial standard probability
space, and `σ_Y` the generalized Bernoulli action of `G` on `(Y,ν)^K` over the `G`-set `K = G/Γ ⊔ G`.

Let `G' ↷ (X,μ)` be an essentially free p.m.p. action of a countable group, `A ⊆ X` measurable with `μ(A) > 0`,
and `θ : (Y,ν)^K → (A,μ_A)` a measure-space isomorphism carrying the orbit relation of `σ_Y` into `R_(G')|_A`.
Then there is a morphism `ρ : G → G'` that is injective on `SL_d(Z)` and on every root subgroup
`U_ij = {e_ij(f) : f ∈ R}`, `i ≠ j`.

## Consequences

1. **The host contains `SL_d(Z)` and an infinite elementary abelian `p`-group.** `ρ(SL_d(Z)) ≅ SL_d(Z)`, and
   `ρ(U_12) ≅ (R,+)`.
2. **No linear host in any characteristic.** `G'` is isomorphic to no subgroup of `GL_n(k)`, for any field `k` and
   any `n`.
   * If `char k ≠ p`, an elementary abelian `p`-subgroup of `GL_n(k)` has order at most `p^n`.
   * If `char k = p`, the integer Heisenberg group `⟨u_12(1), u_23(1)⟩ <= SL_3(Z) <= SL_d(Z)` has no faithful image
     in `GL_n(k)`. The proof is a distortion argument: `u_13(1)^(m²)` is a commutator of words of length `m`, while an
     element of infinite order in characteristic `p` has an eigenvalue of absolute value `> 1` for some absolute value
     (route, Step 7).

   In particular `SL_3(F_p[t])`, every `S`-arithmetic group over a global function field, every lattice of a simple
   algebraic group over a local field of any characteristic, and every finitely generated linear group are excluded.
3. **Virtually torsion-free hosts are excluded too.** A torsion subgroup of a virtually torsion-free group is
   finite. This recovers the hosts covered by `kun-thom-actions-have-no-host-without-p-torsion`.

## Use

`SL_3(F_p[t])` is a lattice of `SL_3(F_p((t^(-1))))`, a characteristic-`p` group with the Howe--Moore property
(standard facts, not re-read here). It has infinite elementary abelian `p`-subgroups, so the earlier torsion no-go
said nothing about it. By Consequence 2, Kun--Thom relations do not give it a nonsofic action by containment, and
they give no containment seed to `sl3z-admits-nonsofic-action` or to any linear lattice for
`mixing-free-nonsofic-action-of-sofic-group`.

The hosts left are non-linear groups that contain both `SL_d(Z)` and an infinite elementary abelian `p`-subgroup.
The Kun--Thom group `G` itself is one.

**Trust surface.**
* Popa's Theorem 0.1 and his weak-mixing criterion for generalized Bernoulli actions, as quoted on main.
* Theorem E from the unrefereed Kun--Thom preprint.
* Two standard extension facts for absolute values (Gauss norm, finite extensions and completions), used in Step 7
  of the route and not re-read here.

No novelty is claimed.

Proof: `kun-thom-relation-host-root-injectivity-proof`.
