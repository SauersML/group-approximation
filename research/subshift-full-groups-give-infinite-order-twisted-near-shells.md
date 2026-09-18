---
rg: 2
id: subshift-full-groups-give-infinite-order-twisted-near-shells
kind: claim
title: The topological full group of a minimal subshift acts on a forward orbit ray with the shift as an element, giving infinite-order twisted near actions of the index kernel
distinct_from:
  twisted-genuine-shell-actions-pass-both-germ-gates: that assumes a genuine twisted action and derives the germ gates; this produces natural infinite-order twists at the level of near actions and locates the obstruction in finite presentation of the full group.
  eventually-periodic-genuine-shell-actions-give-fp-envelopes: that covers finite-order twists (virtually abelian inputs); this gives twists of infinite order for inputs containing infinite simple groups.
artifacts:
  - research/artifacts/gq-bh-shell-universal-genuine-actions.md
---

**ESTABLISHED** for items 1–3 (lane proof below; elementary; not independently reviewed; no novelty
claimed). Item 4 rests on cited theorems not read at source.

**Setting.** `(X, σ)` is a minimal subshift, `x ∈ X`, and the forward orbit ray `σ^n x (n >= 0)` is
identified with `N`. An element `g` of the topological full group `[[σ]]` acts by
`g(y) = σ^(c_g(y)) y` with `c_g: X -> Z` continuous. Let `I: [[σ]] -> Z` be the index map,
`I(g) = #{n < 0 : n + c_g(σ^n x) >= 0} - #{n >= 0 : n + c_g(σ^n x) < 0}`, and put `P = ker I`.

1. **Near action.** Restricting the action on the orbit `σ^Z x ≅ Z` to `N` gives a homomorphism
   `nu: [[σ]] -> NearSym(N)` with `nu(σ) = s` and `index(nu(g)) = I(g)`. It is injective.
2. **Twist.** `s^-1 nu(g) s = nu(σ^-1 g σ)` for every `g`. So `nu(P)` is normalized by `s`, and the twist
   `φ = Ad(σ^-1)` has infinite order on `P` whenever `P` is not centralized by a power of `σ`.
3. **Near group.** `<nu(P), s> = nu([[σ]]) ≅ [[σ]] = P ⋊ <σ>`.
4. **Gate failure (cited).** If `nu|P` is realized by a genuine action `rho` with infinite supports, the
   shell envelope `E_rho` is not finitely presented, because its germ gate needs `R_rho ≅ [[σ]]` to be
   finitely presented. `[[σ]]` is locally embeddable into finite groups (Grigorchuk–Medynets), and its
   commutator subgroup is infinite and simple (Matui). A finitely presented LEF group is residually
   finite, which fails here. Neither source has been read by this lane.

**Proof of 1–3.** `g` moves `σ^n x` to `σ^(n + c_g(σ^n x)) x`. Since `c_g` is bounded, only finitely many
points cross between `N` and its complement, so `g|N` is a near permutation and `index(g|N) = I(g)`
(net inflow into `N`). The cocycle identity `c_(gh) = c_g ∘ h + c_h` gives a homomorphism. If `nu(g)` is
near trivial, `c_g(σ^n x) = 0` for all large `n`; forward orbits of a minimal homeomorphism are dense,
so `c_g = 0` and `g = 1`. For (2), `s^-1 nu(g) s (n) = n + c_g(σ^(n+1) x) = n + (c_g ∘ σ)(σ^n x)`, and
`c_g ∘ σ = c_(σ^-1 g σ)`. Item 3 follows from (1), (2) and `I(σ) = 1`.

**Scope.** Realizability of `nu|P` by a genuine action is not addressed. The example shows that
infinite-order twists are natural at the level of near actions for non-virtually-abelian inputs. The
open target is the finitely presented analogue, `fp-ray-near-actions-with-the-shift-exist`.
