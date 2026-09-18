---
rg: 2
id: zero-set-confinement-unifies-host-obstructions
kind: claim
title: Kazhdan subgroups and Baumslag–Solitar root groups lie in the zero set of every stable length, so a host whose natural stable lengths have confined zero sets excludes both
distinct_from:
  homogeneous-conjugation-invariants-vanish-on-bs-bases: that is the one-line lemma for a single BS base; this adds the Kazhdan/FW half via stable lengths of cocycles and commensurated sets, the whole root group, and the confinement corollary that turns every such invariant into a host exclusion.
  almost-v-fw-subgroups-act-through-finitely-many-germs: that is the germ-localization instance for finite germ extensions of V; this is the abstract mechanism of which it, the FW shell theorems and the Haagerup exclusions are instances.
artifacts:
  - research/artifacts/gq-bh-synth-obstructions.md
---
**ESTABLISHED** (lane proof, bh-synth-obstructions, elementary; the only import is Delorme–Guichardet,
(T) ⇒ (FH), already used on main. Not independently reviewed. No novelty is claimed for the parts; the point is
the uniform statement, which organizes the host obstructions landed on 09-17/18.)

## Setting
A **length** on a group `H` is a function `ℓ : H → [0,∞)` with `ℓ(1) = 0`, `ℓ(g⁻¹) = ℓ(g)` and
`ℓ(gh) ≤ ℓ(g) + ℓ(h)`. Its **stable length** is `ν_ℓ(g) = lim_m ℓ(g^m)/m`; the limit exists and equals
`inf_m ℓ(g^m)/m` by Fekete's lemma. Write `Z(ν) = {g : ν(g) = 0}` for the **zero set**. A zero set is
**𝒞-confining**, for a class `𝒞` of groups closed under subgroups, if every subgroup of `H` contained in it as a
set lies in `𝒞`.

Standard lengths:
- (L1) `ℓ(g) = d(x₀, g x₀)` for an isometric action on a metric space, giving the asymptotic translation length;
- (L2) `ℓ(g) = ‖b(g)‖` for a 1-cocycle `b` of an orthogonal representation, i.e. `√ψ` for a conditionally negative
  definite `ψ` (subadditive because `b(gh) = b(g) + π(g)b(h)`);
- (L3) `ℓ(g) = |gM △ M|` for a commensurated subset `M` of an `H`-set (subadditive because
  `ghM △ M ⊆ (ghM △ gM) ∪ (gM △ M)` and `|ghM △ gM| = |hM △ M|`); this covers wall counts and near-action
  indices;
- (L4) word length in any finitely generated overgroup, giving stable word length (distortion).

## Theorem
Let `ℓ` be a length on `H` and `ν = ν_ℓ`.
1. **Homogeneity and invariance.** `ν(g^k) = |k| ν(g)` and `ν(hgh⁻¹) = ν(g)`.
2. **Root groups.** If `s u s⁻¹ = u^n` with `|n| ≥ 2`, the root group `R(s,u) = ⋃_{k≥0} s^{-k}⟨u⟩s^k` (a quotient
   of `Z[1/n]`) lies in `Z(ν)`.
3. **Rigid subgroups.** If `K ≤ H` has (FH) and `ℓ` is of type (L2), or `K` has FW and `ℓ` is of type (L3), then
   `ℓ` is bounded on `K`, so `K ⊆ Z(ν)`. Property (T) gives both, since (T) ⇒ (FH) ⇒ FW.
4. **Confinement.** If `Z(ν)` is `𝒞`-confining, every such root group and every such rigid subgroup lies in `𝒞`.
   In particular a host with a length of type (L2) or (L3) whose zero set is confining to finite groups (or to
   residually finite, or locally finite groups) contains no infinite Kazhdan group outside that class, and contains
   no BS pair with infinite-order base outside it.

## Proof
1. `ν(g^k) = lim_m ℓ(g^{km})/m = |k| lim_m ℓ(g^{|k|m})/(|k|m)`, using `ℓ(g⁻¹) = ℓ(g)` for `k < 0`. And
   `|ℓ(hg^mh⁻¹) − ℓ(g^m)| ≤ 2ℓ(h)`; divide by `m`.
2. By (1), `ν(u) = ν(s u s⁻¹) = ν(u^n) = |n| ν(u)`, and `ν(u) < ∞`, so `ν(u) = 0`. Every element of `R(s,u)` is
   `s^{-k}u^j s^k`, which by (1) has `ν = |j| ν(u) = 0`.
3. (FH): `b|_K` is a cocycle of `K`, hence bounded (Delorme–Guichardet), so `ℓ(K)` is bounded and
   `ν(g) ≤ lim sup_m (sup ℓ(K))/m = 0` for `g ∈ K`. FW: `M` is `K`-commensurated, so some `K`-invariant `M'` has
   `|M △ M'| = c < ∞`, and `|gM △ M| ≤ |gM △ gM'| + |M' △ M| = 2c` for `g ∈ K`.
4. Immediate from 2 and 3. ∎

## Instances on main
Each exclusion below is this theorem for a named `(ℓ, 𝒞)`. The node listed does the confinement step (proving
that the zero set is small), which is where the host-specific work lies.
- **V is Haagerup (Farley):** (L2) proper, `Z(ν) ∩ K` bounded ⇒ Kazhdan subgroups finite
  (`thompson-v-has-haagerup-property`).
- **Germ localization:** (L3) for the commensurated set of V-regular germs. FW subgroups of finite germ extensions
  of V live in finitely many singular germ groups (`almost-v-fw-subgroups-act-through-finitely-many-germs`,
  `simple-kazhdan-in-germ-extension-of-v-sits-in-one-germ-group`).
- **FW shell windows:** (L3) for the graph of the shift. The near index vanishes on FW inputs, so window-zero shells
  are exactly self-similar actions (`fw-window-zero-shells-are-self-similar-actions`).
- **Proper cocompact CAT(0):** (L1). The zero set is torsion, so no H4 or BG
  (`homogeneous-conjugation-invariants-vanish-on-bs-bases`).
- **Movement and entropy in nV:** homogeneous, conjugation-invariant. The zero set is the periodic part, giving
  logarithmic movement (`brin-thompson-aperiodic-elements-have-logarithmic-movement`) and zero-entropy BS
  conjugators.
- **Slopes at periodic points (PL, Stein):** zero set = no hyperbolic periodic point. Confining in V, not in Stein
  groups (Boshernitzan), which is exactly why Stein hosts survive
  (`stein-elements-with-hyperbolic-periodic-points-bound-roots`).
- **Central elements of Kazhdan subgroups of 2V:** forced into the slope-free zero set
  (`kazhdan-central-elements-of-2v-have-slope-free-periodic-points`).

## Lesson for general BH
Every "rigid or distorted input excluded" theorem of the swarm is one mechanism: the hard feature (property (T),
FW, a Baumslag–Solitar root group) is forced into the zero set of every natural stable length of the host, and
the host dies exactly when that zero set is small. A host for the reduced input class
(`boone-higman-iff-simple-kazhdan-decidable-inputs`) must therefore have *non-confined* zero sets. It needs:
- infinite Kazhdan subgroups with bounded wall and cocycle lengths that still act genuinely, not through finitely
  many germs;
- infinite-order renormalizable elements with zero entropy, zero drift and no hyperbolic periodic points.

Every success of 09-18 is such a zero-set element or subgroup:
- the 2V_τ odometer (`odometer-2v-is-fp-simple-and-contains-bs12`);
- SMART_m in 3V (`bs-1-m-embeds-in-brin-thompson-3v-for-odd-m`);
- Ã₂ lattices in rank-two k-graph full groups (`a2-lattices-embed-in-fp-simple-groups`).
The systematic reading is in `research/artifacts/gq-bh-synth-obstructions.md`.
