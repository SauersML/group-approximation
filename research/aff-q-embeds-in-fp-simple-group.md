---
rg: 2
id: aff-q-embeds-in-fp-simple-group
kind: claim
title: The rational affine group Aff(Q) = Q x| Q^x embeds in a finitely presented simple group
distinct_from:
  gl-n-q-embeds-in-fp-simple-group: that is the root for GL_n(Q), n >= 2; this is its stepping stone Aff(Q) = {[[a,b],[0,1]]} <= GL_2(Q), which the root implies and which is necessary for it.
  borel-two-q-is-units-times-aff-q: that proves B_2(Q) = Q^x x Aff(Q) and reduces B_2(Q) to Aff(Q) inside B_A; this is the open embedding question for Aff(Q) itself.
  rational-linear-groups-satisfy-boone-higman: that covers the finitely generated subgroups, which here all lie in some Aff(Z[1/m]); this is the whole countable group.
  aff-q-does-not-embed-in-aut-thompson-f: that excludes two specific hosts, T-bar and Aut(F); this asks for some finitely presented simple host.
---

**OPEN.** There are a finitely presented simple group `S` and an injective
homomorphism `Aff(Q) -> S`, where `Aff(Q) = {x ↦ a x + b : a ∈ Q^x, b ∈ Q} ≅ Q ⋊ Q^x`.

**Status as a target.** This is a stepping stone of the swarm, not a printed question.
- `Aff(Q) <= B_2(Q) <= GL_2(Q)`, so `gl-n-q-embeds-in-fp-simple-group` implies this
  claim.
- Conversely, `B_2(Q) ≅ Q^x × Aff(Q)` (`borel-two-q-is-units-times-aff-q`), so a
  `B_A` host for `Aff(Q)` gives one for `B_2(Q)`.
- It is the smallest non-abelian rational stepping stone. It has the divisibility of
  `(Q,+)` and the dilations `BS(1,p) <= Aff(Q)` for every prime `p`, but none of the
  rigidity of `SL_3(Z)`.

## Known

- **Pieces.** `(Q,+)` and `Q^x` embed in `VA` (countable abelian). `(Q,+)` also embeds
  in `2V` (`rationals-embed-in-brin-thompson-group-2v`). Every finitely generated
  subgroup lies in some `Aff(Z[1/m]) <= GL_2(Q)`, so it embeds
  (`rational-linear-groups-satisfy-boone-higman`).
- **Detection.** A homomorphism from `Aff(Q)` is injective iff the translation `t_1`
  survives, iff the image is non-abelian
  (`gl-n-q-embeddings-detected-by-nontrivial-homomorphisms`, item 3). In `Aff(Q)`, all
  nontrivial translations are conjugate, and `t_b` is conjugate to `t_b^m` for every
  `m ≠ 0`.
- **Reduction.** `Aff(Q)` embeds in a finitely presented simple group as soon as it
  lies in a finitely presented group with a type (A) action
  (`type-a-action-gives-boone-higman-for-subgroups`). This covers countable inputs; see
  `permutational-host-forms-agree-for-countable-inputs`.

## What a host must have

- **H1, not residually finite.** It contains no residually finite group, because
  `(Q,+)` is divisible (root O1).
- **H2, exponential distortion.** It contains `BS(1,p)` for every prime `p`. This
  excludes `VA` and every subgroup of it: `V`, `T-bar`, Brin's `A` (root O4,
  Burillo–Felipe). For `T-bar` and `Aut(F)` there is also
  `aff-q-does-not-embed-in-aut-thompson-f`.
- **H3, no natural piecewise-linear action.** A finitely generated host whose
  generators have finitely many linear parts cannot act with the dilations fixing a
  point with derivative `a` (`fg-piecewise-linear-hosts-omit-natural-gl-n-q`).
- **H4, no easy closures.** Abelian-lamp permutational wreath products add nothing
  (`abelian-lamp-wreaths-cannot-create-u3-q-or-aff-q`). Central lifts cannot supply the
  translation divisibility (`lifts-add-no-unipotent-divisibility`).
- **H5, Brin–Thompson hosts.** An `nV` host needs `BS(1,2) <= nV`
  (`rational-stepping-stones-in-nv-need-bs12-or-heisenberg`; OPEN as
  `bs12-embeds-in-brin-thompson-2v`). Its translation subgroup must also be an
  exponent-flat copy of `Q` (`nv-rational-subgroups-with-power-conjugacy-are-flat`). The
  landed copy of `Q` in `2V` is not one. A copy of `Q` with no periodic points at all
  exists in `3V` (`three-v-contains-aperiodic-rationals`).

## Attempts

1. **Natural piecewise-affine or projective actions (2026-09-17): dead.** Derivatives
   and coefficients stay in a finitely generated ring. See H3 and
   `germ-extensions-omit-standard-gl-n-q`.
2. **The Kojima–Sheng tower in `2V` as the translation group (2026-09-17, gq-affq):
   dead.** `s_0 = t × id` has a hyperbolic fixed point, so no element of that copy of
   `Q` is conjugate in any `nV` to a proper power
   (`nv-rational-subgroups-with-power-conjugacy-are-flat`, item 3).
3. **An aperiodic tower in `3V` (2026-09-17, gq-affq): alive, first step only.** The
   root tower `Q_T` over the SMART moving-tape element `T ∈ 2V` has no periodic points
   (`three-v-contains-aperiodic-rationals`). It passes the periodic-exponent tests.
   - *Next falsifiable step:* find `f ∈ nV` with `f s_0 f^-1 = s_0^2` for
     `s_0 = T × id`, or refute it with the `(log N)^2` exponent bound (item 4 of
     `bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets`) or the logarithmic
     table-length bound (`bs12-images-in-nv-have-logarithmic-table-length`). Both
     reduce to the head excursions of SMART.
   - *A constructive handle:* `renormalizable-thompson-elements-give-baumslag-solitar`.
     Suppose an infinite-order `T ∈ kV` has a brick-local height-`m` tower
     renormalization, that is, `T^m` on a clopen base is conjugate to `T` by a
     prefix-replacement map. Then `BS(1,m) <= (k+1)V`, with `s = T × id`. So the
     conjugacy step becomes a search for an odometer-like element inside some `kV`.
   - *Beyond that:* commuting dilations for all primes, acting on all of `Q_T` at once.
4. **Röver–Nekrashevych hosts over rational Iwahori groups.** A live route of lane
   gq-rn-varying-degree, in drafts at the time of writing. `PGL_2(Q) ⊇ Aff(Q)` acts
   on `P^1(Q_p)` with local actions in the rational Iwahori group, which is not
   finitely generated. Divisibility by `p` then comes from level shifts, and
   divisibility by the other primes from the local translations. The route needs that
   local group, or the part used by `Aff(Q)`, inside a finitely presented
   self-similar group. Nothing about it is recorded here as established.
5. **A 2-transitive permutation group through Aff(Q) (lane gq-deep-typeA-2,
   `gl-n-q-lies-in-prime-shift-permutation-group`).**
   - *The group.* Let `σ` be the automorphism of `Q^x` that shifts a `Z`-indexing
     of the primes. Then `A_1 = ⟨x+1, 2x, -x, σ⟩ <= Sym(Q)` contains `Aff(Q)` and
     is 2-transitive on `Q`.
   - *What it reduces to.* `A_1 ↷ Q` is of type (A) iff `A_1` is finitely
     presented and `Stab_{A_1}(0)` is finitely generated. Both are open.
   - *Why the earlier obstructions miss it.* `σ` is continuous for no real or
     `p`-adic topology, so H3 does not apply.
6. **The `p = 3` dilation in a Brin–Thompson group (2026-09-18, lanes gq-nv-obstruct and gq-affq).**
   - *The piece, ESTABLISHED (d4064ce79).* `bs13-embeds-in-brin-thompson-3v`, through
     `smart-induced-map-has-brick-local-height-3-renormalization`. Referees: gq-referee-a
     12b5beb4a, gq-referee-b b6d33ae8e, gq-referee-c 894d10d19. Numerical validation: cba5854a6.
     Priority check (bounded, no MathSciNet): e78b09c00. It gives `s, u ∈ 3V` with `u s u^-1 = s^3`, where
     `s = U × id` and `U` is SMART induced on its level-0 moves.
   - *What is still missing for `Aff(Q)` through an `nV` host.*
     - One copy of `Q` must contain a nontrivial `h` with a conjugate `f_p h f_p^-1 = h^p` for
       every prime `p`.
     - The `f_p` must commute and act on that copy compatibly.
     - The root tower `Q_T` of `three-v-contains-aperiodic-rationals` and the element `s` above
       both sit over SMART-type bases. Whether one element can serve as base for both, and
       whether a height-`p` renormalization exists for primes `p ≠ 3`, is open. `Aff(Q)` contains
       `BS(1,2)` (the dilation `x ↦ 2x`), so an `nV` host needs `BS(1,2) ≤ nV`
       (`bs12-embeds-in-brin-thompson-2v`, still OPEN). That calls for a binary analogue of SMART's
       ternary hierarchy.
7. **One base for several primes: first obstructions (2026-09-18, gq-affq).**
   - *Proved:* `renormalization-heights-force-eigenvalue-roots`.
     - A height-`m` renormalization forces `E(T) = {μ : μ^m ∈ E(T)}`. One base carrying every
       prime height therefore factors onto `Ẑ`, if it is minimal.
     - A height-`q` renormalization multiplies every `p`-adic clock by `q^{-1}`. That is a unit
       map with unbounded carries.
     - SMART's `U` is known only to factor onto `Z/2 × Z_3`. If that factor is maximal, `U`
       carries no height with a prime factor `≠ 3`.
   - *MSI* (`research/artifacts/gq-affq-coprime-renormalization-test.md`). A product base needs a
     "coprime speed-up" `ψ ∘ U^q = U ∘ ψ`. Sound pointwise refutations show that no one-cell
     bounded edit gives one for `q = 5` or `q = 7`; this is the same class that carries the
     height-3 renormalization.
   - *Conjectured:* by Durand's Cobham theorem for substitutions (arXiv:1010.4009), no single
     aperiodic machine-type base carries brick-local renormalizations of heights `2` and `3`. If
     so, the dilations for different primes cannot all come from renormalizing one `s = T × id`,
     and the `nV` route to `Aff(Q)` needs another mechanism for combining primes.
8. **Katsura–Exel–Pardo host for the Baumslag–Solitar gate (2026-09-18, gq-affq; critic's U3).**
   - `odometer-2v-is-fp-simple-and-contains-bs12`: `2V_τ = ⟨2V, τ × id⟩` is the full group of the Katsura
     odometer triple `A=(2)`, `B=(1)` acting self-similarly on the product 2-graph. It is `F_∞` (Li, Example
     ex:ZS (III)) and simple (Matui, Theorem simple2, after a perfectness count), and it contains `BS(1,2)`,
     `(Q,+)` and `2V`.
   - The odometer is renormalizable natively (`0w ↦ w` is a groupoid bisection), and the baker map of `2V` makes
     the conjugacy global.
   - *Not reached:* `Q ⋊ ⟨2⟩`. The conjugator `u` squares `s` and `u^{-1}su` is the first root in the tower `Q_τ`,
     but `u` is not shown to normalize `Q_τ`. Nor is it known whether `2V_τ` embeds in any `nV`.
