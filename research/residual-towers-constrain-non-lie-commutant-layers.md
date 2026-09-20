---
rg: 2
id: residual-towers-constrain-non-lie-commutant-layers
kind: claim
title: For a residually finite group lifted through a product of compact Lie groups built from its finite quotients, the commutator squeeze is replaced by a tower law — the projected singular set at level N must have measure at least the minimal pattern frequency at radius (generator radius × systole of the level-N kernel) — which is consistent with a null singular set (an explicit set meeting it: loop-labels-reduce-t2-to-two-sided-locality, item 1 as repaired), so the non-Lie layer (target T2, and T1 run through a product) is the escape the squeeze constrains least
distinct_from:
  commutator-squeeze-bounds-lifted-lie-translations: that kills free lifted groups of Lie translations under polynomial repetitivity and tame singular sets; this shows the mechanism does not reach product layers, and derives the constraint that remains there, stated through the finite-quotient tower of the lifted group.
---

## Proposed dependency record (not an accepted route)

The following rejected claim-level metadata is preserved verbatim as a
proposed dependency record. It is not a compiled route, does not establish
this claim, and requires individual mathematical review before any route
is accepted. The historical mathematical prose below is unchanged.

```yaml
requires:
  - commutator-squeeze-bounds-lifted-lie-translations
  - profinite-skew-layers-collapse-into-the-equicontinuous-factor
  - decidable-residually-finite-non-exact-group-exists
```

**ESTABLISHED** (lane bh-invent-16, 2026-09-19; lane proof, elementary; referee bh-ref-d 6e0fb29940 PASS with repairs, applied; no priority
claimed). This is a design law, not an obstruction. **T1 and T2 are not built.**

## Which escape, and why

Target T1 and the commutator squeeze leave three escapes. This lane takes the **non-Lie layer**.
- **Rare patterns and codimension-0 singular sets are what the squeeze forces, in quantified form.** Along
  iterated commutators it demands `ψ(A 2^j) ≤ ν(Z_1 · B(ρ^j))` for every small `ρ`. So those two escapes
  are the squeeze's own conclusions: the pattern frequencies, or the thickness of the singular set, must
  beat every power.
- **In a product `K = ∏_i K_i` the squeeze does not start.** Iterated commutators of two elements
  concentrated in the tail `K_(>N) = ∏_(i>N) K_i` stay in that tail, and they do not shrink there. The
  contraction `d([u, v], 1) ≤ C d(u, 1) d(v, 1)` has no uniform constant across infinitely many factors.
- **Relevance.** A non-exact commutant forces an infinite-dimensional layer anyway
  (`profinite-skew-layers-collapse-into-the-equicontinuous-factor`, item 3). So the non-Lie route is the
  one that also serves T2 and (RA′), and T1 can be run through it, with `F_2` embedded in a product of
  `SU(n)`s.

## Setting

- The notation `Y`, `μ`, `ψ`, `ρ : Y → Z`, `Z_1` and `ν` is as in
  `commutator-squeeze-bounds-lifted-lie-translations`.
- `G` is finitely generated, non-amenable and residually finite: Osajda's group, or `F_2`.
- `S` is a finite symmetric generating set, and `h > 0` is the exponential growth rate of `G`.
- `π_i : G → Q_i ↪ K_i` are finite quotients with `⋂_i ker π_i = 1`, and each `K_i` is a compact
  connected Lie group, for example `SU(|Q_i| + 1)`.
- `K = ∏_i K_i`, `κ = (π_i)_i`, and `K_(>N) = ∏_(i>N) K_i`.
- `Z_N = Z / K_(>N)` is the level-`N` Lie quotient, and `ν_N` is the image of `ν` there.
- `N_N = ⋂_(i≤N) ker π_i`, of index `I_N`, and `sys(N_N)` is its shortest nontrivial word length.
- `G ≤ Aut(Y)` covers the right translations `R_(κ(g))`, `K` acts freely on `Z`, and `R_S` bounds the
  radii of the generators and their inverses.

## Statement

1. **Tower law.** For every `N`,

   `ψ(R_S · sys(N_N)) ≤ ν_N( image of Z_1 in Z_N ) = ν(Z_1 · K_(>N))`.

2. **Systoles are logarithmic.** `sys(N_N) ≤ (2/h) log I_N + O(1)`. So for a polynomially repetitive row
   (`ψ(R) ≥ c R^(-a)`),

   `ν(Z_1 · K_(>N)) ≥ c′ (log I_N)^(-a)` for all `N`.

   The singular set must project, at every finite level, onto a set of measure at least a power of
   `1/log I_N`. This is compatible with `ν(Z_1) = 0`, and with each image of `Z_1` in a Lie quotient
   being thick. The images are projections along infinite-dimensional fibres, and such projections are
   typically large.
3. **Every finite-level image of the singular set is thick.** By item 1,
   `ν_N(image of Z_1 in Z_N) ≥ ψ(R_S · sys(N_N)) > 0` for every `N`. So T2 must keep every finite-level
   image of the singular set of positive measure (codimension 0), while `ν(Z_1) = 0` is allowed.
   This is forced rather than chosen.
   - The earlier reason, that the squeeze applies inside each `Z_N`, was wrong: the lifted image
     `κ_N(G) ⊆ ∏_(i≤N) Q_i` is **finite**, so the squeeze is vacuous there.
   - Repair (§2) of bh-ref-d, 6e0fb29940, applied by bh-ra-t2 as the (RA_free) owner.
   - Compatibility with `ν(Z_1) = 0` is automatic: `Z_1` is compact, so `ν(Z_1 · K_(>N)) ↓ ν(Z_1)` as
     `K_(>N) ↓ 1`, while the lower bound `ψ(R_S · sys(N_N))` tends to 0.

## Proof

**1.**
- Take `g ∈ N_N ∖ {1}` of word length `sys(N_N)`. Then `R(g) ≤ R_S · sys(N_N)`.
- `κ(g)` lies in `K_(>N)`, since the first `N` coordinates are trivial. It is nontrivial, because `κ` is
  injective and the action is free.
- Repeat the proof of item 1 of the squeeze node, with the path from `1` to `κ(g)` taken inside the
  connected group `K_(>N)`. The cylinder `W` of changed symbols projects into `Z_1 · K_(>N)`, so
  `ψ(R(g)) ≤ μ(W) ≤ ν(Z_1 · K_(>N))`.
- Finally, `Z_1 · K_(>N)` is the preimage of the image of `Z_1` in `Z_N`.

**2.**
- `|B_S(r)| ≥ e^(hr)` for large `r`, since `G` is non-amenable and so has exponential growth.
- Once `|B_S(r)| > I_N`, two distinct elements of `B_S(r)` lie in one coset of `N_N`. Their quotient is a
  nontrivial element of length `≤ 2r`.
- Substitute into 1. ∎

## Lesson for general BH

**Infinite-dimensional layers trade the commutator squeeze for a tower law.**
- A lifted residually finite group must have short elements deep in its residual chain, with length
  `≲ log(index)`. Their displacement lies in the tail of the layer.
- So the coding's singular set must stay thick in every finite-level image. It must have codimension 0 at
  every Lie level while remaining null overall.
- Nothing forbids this, so the non-Lie route stays open for both T1 (a product of `SU(n)`s carrying `F_2`)
  and T2 (Osajda's group).

The quantitative target for a construction is precise: `ν(Z_1 · K_(>N)) ≳ (log I_N)^(-a)` for a
repetitivity exponent `a`. A hierarchical data layer can aim for it by letting level `N` of the hierarchy
resolve factor `N` of the layer.
