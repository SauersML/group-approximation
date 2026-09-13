# Co-amenable subgroups of wreath products over Kazhdan actors

Lane `ex-rokhlin-lower`, 2026-09-12. The proofs are handwritten, and nothing was computed.

**Supports:**
- `kun-thom-wreath-actor-subgroups-are-not-co-amenable`, with its route
  `kun-thom-wreath-actor-not-co-amenable-proof`;
- the Attempts entry on `kun-thom-wreath-bernoulli-rokhlin-maximal`.

**Why this is needed.** `rokhlin-maximality-ascends-co-amenable-subgroups` (Theorem A of
`research/artifacts/rokhlin-co-amenable-ascent-and-thompson-v-2026-09-12.md`) is the only landed ascent
theorem for Rokhlin maximality that uses no finite models.
- Over simple Kazhdan hosts it is vacuous (`simple-kazhdan-groups-have-no-proper-co-amenable-subgroups`).
- The Kun–Thom wreath `W` is neither simple nor Kazhdan: it has the infinite amenable normal subgroup of
  lamps. So that obstruction does not apply to `W`, and the question is which subgroups of `W` are
  co-amenable.

## 1. Setting

- `G` is a countable group with property (T).
- `X` is a `G`-set whose orbits are all infinite.
- `B` is a nontrivial finite abelian group, `N = B^(X)` (finitely supported functions), and
  `W = N ⋊ G`, with `g.n = n ∘ g^-1`.
- `π : W -> G` is the projection.

A subgroup `H <= W` is **co-amenable** when the left `W`-set `W/H` carries a `W`-invariant mean.

**(K0) Kazhdan groups have no invariant mean on a G-set all of whose orbits are infinite.**
- **Almost invariant vectors.** Let `Ω` be a countable `G`-set with all orbits infinite, carrying a
  `G`-invariant mean. Day's trick gives finitely supported probability densities `f_i` on `Ω` with
  `||g.f_i - f_i||_1 -> 0` for every `g`. Since `|√a - √b|^2 <= |a - b|`, the unit vectors `ξ_i = √f_i`
  are almost invariant in `ℓ^2(Ω)`.
- **An invariant vector.** Property (T) gives a nonzero invariant `ξ` in `ℓ^2(Ω)`.
- **Contradiction.** `ξ` is constant on each orbit, and it is nonzero on some orbit. Square-summability
  forces that orbit to be finite.

This is the argument of `no-invariant-mean-on-coset-space`, run on a countable `G`-set that need not be
transitive.

## 2. The proposition

**Proposition K.** Let `M <= N` be a `G`-invariant subgroup with `M != N`, and put `V = N/M`. Suppose every
nonzero element of `V` has an infinite `G`-orbit. Then `H = M ⋊ G` is not co-amenable in `W`.

*Proof.*
- **The coset space.** `W = N H` and `N ∩ H = M`. So `n ↦ nH` induces a bijection `V -> W/H`.
  Under it `(n', 1)` acts by translation `v ↦ n' + v` and `(0, g)` acts by `v ↦ g.v`.
- **Equivariance.** `(n', g)(n, 1)H = (n' + g.n, g)H = (n' + g.n, 1)(0, g)H = (n' + g.n, 1)H`, since
  `(0, g)` lies in `H`. So the action is `v ↦ n' + g.v`.
- **Setup for a contradiction.** Suppose `m` is a `W`-invariant mean on `V`.
- **`V` is infinite.** It contains a nonzero element, and that element has infinitely many translates.
- **`m({0}) = 0`.** `m` is translation invariant, so every singleton has the same mass. A mean gives
  finitely many disjoint sets total mass at most `1`.
- **An invariant mean on `V \ {0}`.** Restricting and normalising `m` gives a `G`-invariant mean on
  `V \ {0}`, a countable `G`-set whose orbits are all infinite by hypothesis. This contradicts (K0). QED

**Corollary K1 (the actor).** `G` itself is not co-amenable in `W`.

*Proof.* Take `M = 0`. Let `v != 0` in `N` with support `S`, finite and nonempty.
- If the orbit `G.v` were finite, the stabilizer `G_v` would have finite index.
- `G_v` preserves `supp(v) = S` setwise, so every point of `S` would have a finite `G_v`-orbit.
- Then it would have a finite `G`-orbit, since `[G : G_v] < ∞`. That contradicts the hypothesis on `X`.

So Proposition K applies. QED

**Corollary K2 (the preimage of the actor modulo the radical).** Let `W` be the Kun–Thom wreath for a
Theorem E pair `Γ < G`. Put `Γ̂ = EL_r(R)` and let `N_0 = Rad_sof(W)` be the fibre-even lamp subgroup
(`kun-thom-wreath-sofic-radical-is-fibre-parity-kernel`). Then `N_0 ⋊ G` is not co-amenable in `W`.

*Proof.*
- **The quotient.** Summing lamps over the fibres of `G/Γ -> G/Γ̂` is a `G`-equivariant surjection
  `N -> (Z/2)^(G/Γ̂)` with kernel `N_0`. So `V = N/N_0 ≅ (Z/2)^(G/Γ̂)` as `G`-modules.
- **Infinite orbits.** `G/Γ̂ ≅ SL_d(Z)` as a `G`-set with `EL_r(R)` acting trivially. It is transitive and
  infinite, so all its orbits are infinite.
- **Conclusion.** The argument of Corollary K1, with `X` replaced by `G/Γ̂`, shows that every nonzero
  element of `V` has an infinite orbit. `G` has (T) by Theorem E (`kun-thom-nonsofic-wreath`), and
  Proposition K applies. QED

**Corollary K3 (the actor image of a co-amenable subgroup).** If `H <= W` is co-amenable, then `π(H)` has
finite index in `G`.

*Proof.*
- **Push to the quotient.** Pushing an invariant mean forward along `W/H -> W/(HN) = G/π(H)` gives a
  `G`-invariant mean on `G/π(H)`.
- **Apply (T).** By `no-invariant-mean-on-coset-space`, `π(H)` has finite index. QED

## 3. Reading for the Rokhlin question

- **Ascent from subgroups containing the actor is dead.** Theorem A of the co-amenable ascent reaches
  `W` from a maximal co-amenable `H`.
  - By Corollary K3, such an `H` maps onto a finite-index subgroup of `G`.
  - By Corollaries K1 and K2, `H` cannot be `G`, or `N_0 ⋊ G`, or any `M ⋊ G` whose quotient module has
    only infinite orbits.
  - What remains are subgroups whose lamp part `M` has a quotient module `N/M` with nonzero vectors of
    finite orbit. Those `M` are close to the kernels of fibre sums over finite quotients `G/ΓΔ`, and
    `N/M` is then finite, which is the finite-index case. The general case is not classified here.
- **Consistency with Remark 3 of the ascent artifact.** There a maximal co-amenable subgroup known today
  would be sofic and would make `W` sofic. Proposition K is the structural statement behind that remark
  for `W`, and it does not depend on the current list of maximal groups.
- **Mechanism conclusion.** Together with the Alpeev–Seward vanishing
  (`factors-fixed-by-large-finite-subgroups-have-zero-outer-entropy`) and the witness localization, a
  lower bound over `W` has three constraints:
  - it cannot be induced from any subgroup containing the actor;
  - it cannot come from information the sofic radical fixes;
  - it must count along configurations that fold on invisible lamps.
