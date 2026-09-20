---
rg: 2
id: distorted-z2-free-locus-proof
kind: route
title: Proof that a hyperbolically normalized Z^2 in nV has clopen fixed sets and a nonempty closed free locus
target: distorted-z2-with-hyperbolic-normalizer-in-nv-has-a-free-locus
requires:
  - heisenberg-in-nv-forces-drift-free-central-element
---

Notation is as in the target. `s_g(z) ∈ Z^n` is the offset (level) cocycle of `g ∈ nV`. It is
locally constant and bounded, and it satisfies `s_{gh}(z) = s_g(hz) + s_h(z)`
(`heisenberg-in-nv-forces-drift-free-central-element`, and item 1 of
`brin-thompson-torsion-has-clopen-fixed-sets-proof`).

**Step 0 (hyperbolic matrices).** Let `A ∈ GL_2(Z)` be hyperbolic, i.e. it has a real eigenvalue
`|λ| > 1`. Then no power `A^p`, `p ≠ 0`, has a rational eigenvector. Indeed `A^p` is again
hyperbolic, with characteristic polynomial `x^2 - τx + δ`, `δ = ±1`. A rational eigenvalue would
be an integer dividing `δ`, so it would be `±1`, which is not hyperbolic. Hence `A^p` preserves no
rational line, and `A` has no finite orbit on the set `P^1(Q)` of rational lines. Also `A^2` is
hyperbolic with `det A^2 = 1`.

**Step 1 (F1: distortion).** Let `g ∈ N` have hyperbolic twisting matrix `A`, and put `B = A^2`,
realized by `g^2`, with `det B = 1`. By Cayley–Hamilton, `B + B^{-1} = tr(B)·I`. Hence
`B^k + B^{-k} = τ_k I` with `τ_k = tr(B^k) = μ^k + μ^{-k}`, where `μ = λ^2 > 1`. So `|τ_k| -> ∞`
exponentially. Therefore
`x^{τ_k v} = x^{B^k v} x^{B^{-k} v} = g^{2k} x^v g^{-2k} · g^{-2k} x^v g^{2k}`,
and in the finite generating set `S = {x_1, x_2, g}` of `⟨H, g⟩` this has word length at most
`8k + 2|v|_1`.

Suppose `x^v`, `v ≠ 0`, had an `x^v`-invariant probability measure with nonzero drift `ρ`. Item 1
of `heisenberg-in-nv-forces-drift-free-central-element` gives `|x^{Nv}|_S >= N|ρ|_∞/K` for all
`N >= 1`. Take `N = |τ_k|`, using `x^{-τ_k v}` if `τ_k < 0`. Then `|τ_k|·|ρ|_∞/K <= 8k + 2|v|_1`
for all `k`. This is false for large `k`, since `|τ_k|` grows exponentially. So `x^v` is drift-free.

**Step 2 (F2: clopen fixed sets).** Let `h = x^v` be drift-free and let `z` have period `p >= 1`
under `h`. The orbit measure `μ = (1/p) Σ_{j<p} δ_{h^j z}` is `h`-invariant. By the cocycle
identity its drift is `ρ_μ(h) = (1/p) Σ_{j<p} s_h(h^j z) = (1/p) s_{h^p}(z)`. Drift-freeness gives
`s_{h^p}(z) = 0`: the periodic point has zero offset.

Now let `h = x^v` fix `z`, so `p = 1` and `s_h(z) = 0`. Take a box `u_1C × ⋯ × u_nC ∋ z` of a
representing partition of `h`, on which `h` is `(u_i w_i) ↦ (u'_i w_i)`. Zero offset means
`|u'_i| = |u_i|` for all `i`. Write `z = (u_i w_i)`. Then `hz = z` gives `u'_i w_i = u_i w_i`, and
prefixes of equal length of the same sequence agree, so `u'_i = u_i`. So `h` is the identity on
that box, and `Fix(h)` is open. It is closed as the fixed set of a homeomorphism. For `v = 0` it is
`X`. This is the argument of item 2 of `brin-thompson-torsion-has-clopen-fixed-sets-proof`, with
drift-freeness in place of finite order.

**Lower semicontinuity.** `S(z)` is a subgroup of `Z^2`. Choose generators `w_1, …, w_r` of it,
with `r <= 2`. Then `U = ⋂_j Fix(x^{w_j})` is an open neighbourhood of `z`, and every `z' ∈ U` has
`S(z') ⊇ ⟨w_1, …, w_r⟩ = S(z)`.

**Equivariance.** For `g ∈ N` and `u ∈ Z^2`:
- `x^w(gz) = g x^{M_g^{-1} w} z`, so `S(gz) = M_g S(z)`;
- `x^u` commutes with every `x^w`, so `S(x^u z) = S(z)`.

So `E` permutes stabilizers through the linear action of `Γ`, and preserves their index and rank.

**Step 3 (F3: free locus).** Assume `Γ` contains a hyperbolic matrix `A = M_g`. By Step 1, every
`x^v` is drift-free, so Step 2 applies.

- *Rank and orbits.* The `H`-orbit of `z` is in bijection with `Z^2 / S(z)`. So `z ∈ K` iff
  `rank S(z) <= 1`, and `z ∉ K` iff `S(z)` has finite index.
- *`K` is closed.* If `S(z)` has finite index, then by lower semicontinuity every `z'` in a
  neighbourhood `U_z` has `S(z') ⊇ S(z)`, which is again of finite index. So `X \ K` is open.
- *`K` is nonempty.* Suppose `K = ∅`. Cover the compact `X` by finitely many `U_{z_1}, …, U_{z_m}`,
  and put `L = ⋂_i S(z_i)`, a finite-index subgroup of `Z^2`. Every `z' ∈ X` lies in some
  `U_{z_i}`, so `S(z') ⊇ S(z_i) ⊇ L`. Then `x^v = id` for all `v ∈ L`, and `L ≠ 0`, which
  contradicts `H ≅ Z^2`.
- *Invariance.* By equivariance, `S(ez)` is `M_e S(z)` (for `e ∈ N`) or `S(z)` (for `e ∈ H`). This
  has the same rank as `S(z)`, and it is `0` iff `S(z)` is. So `K` and `W = {z : S(z) = 0}` are
  `E`-invariant.
- *`W` is closed and `W ⊆ K`.* `W = X \ ⋃_{v≠0} Fix(x^v)` is the complement of a union of open sets
  (Step 2), and every point of `W` has `S(z) = 0`, of rank `0`.
- *Line map.* On `K \ W`, `S(z)` has rank exactly `1`, and `ℓ(z) = Q·S(z) ∈ P^1(Q)`. For
  `z ∈ K \ W` and `z' ∈ U_z ∩ K`, the group `S(z')` has rank `<= 1` and contains the rank-one
  group `S(z)`. So `ℓ(z') = ℓ(z)`, and `ℓ` is locally constant on `K \ W`, which is open in `K`.
  Also `ℓ(gz) = M_g ℓ(z)` for `g ∈ N`.
- *`W ≠ ∅`.* Suppose `W = ∅`. Then `ℓ` is a locally constant map on the nonempty compact space `K`,
  so its image `F ⊆ P^1(Q)` is finite and nonempty. `F` is `A`-invariant: `z ∈ K` implies `gz ∈ K`
  and `ℓ(gz) = Aℓ(z)`. So `A` permutes the finite set `F`, and some power `A^p`, `p >= 1`, fixes a
  rational line. This contradicts Step 0. Hence `W ≠ ∅`.

This proves (F3). On `W`, no `x^v` with `v ≠ 0` has a fixed point. A periodic point of `x^v` would
be a fixed point of `x^{pv}`, so `x^v` is aperiodic on `W`.

**Step 4 (F4: measures).**
- *The stabilizer map is Borel.* For each `v`, the set `{z : v ∈ S(z)} = Fix(x^v)` is clopen.
  `Sub(Z^2)` is countable, and each fibre `S^{-1}(Λ)` is a countable Boolean combination of these
  sets, so `S : X -> Sub(Z^2)` is Borel.
- *Pushforward.* Let `μ` be an `E`-invariant Borel probability measure, and `ν = S_*μ`. For
  `g ∈ N`, `S ∘ g = M_g ∘ S`, so `ν` is `M_g`-invariant. In particular it is `A`-invariant.
- *Infinite orbits are null.* If `Λ` has an infinite `A`-orbit, then all its points carry the same
  mass `ν({Λ})`. Their total mass is at most `1`, so `ν({Λ}) = 0`.
- *Rank one is null.* A rank-one `Λ` spans a rational line `Q·Λ`. Its `A`-orbit is infinite by
  Step 0, and hence so is the `A`-orbit of `Λ`.
- *Conclusion.* `μ(S has rank one) = 0`. `μ` is carried by `W` (where `S = 0`) together with the
  points whose stabilizer is a finite-index lattice with a finite `A`-orbit.
- *An invariant measure on `W`.* If `E` is amenable, then it has an invariant Borel probability
  measure on the nonempty compact `E`-invariant space `W` (Step 3). The Sol lattice
  `⟨H, g⟩ ≅ Z^2 ⋊_A Z` is solvable, hence amenable.

This proves (F4).

**Consequences.**
- *Hyperbolic twisting in each gate.* A non-amenable `Γ ≤ GL_2(Z)` contains a non-abelian free
  subgroup, so it contains a hyperbolic element. This is the standard fact that a discrete subgroup
  of `PSL_2(R)` with only elliptic and parabolic elements is elementary, hence virtually abelian.
  It is applied to the image of `Γ ∩ SL_2(Z)`, which has index at most 2 in `Γ`. In `SL_3(Z)`, the matrices `[[B, v], [0, 1]]` with `B ∈ SL_2(Z)` and `v ∈ Z^2` form
  `Z^2 ⋊ SL_2(Z)`. Conjugation acts on the root subgroup `{[[I, v],[0,1]]} = ⟨e_13, e_23⟩` through
  `B`, and `B = [[2,1],[1,1]]` is hyperbolic.
- *Locally non-free bases.* `X = ⋃_{v≠0} Fix(x^v)` says exactly that `W = ∅`, which (F3) forbids
  once `Γ` has a hyperbolic element.
  - *Disjoint supports.* If `x, y` have disjoint supports, then every `z` is fixed by `x` or by
    `y`, so `W = ∅`.
  - *Finite unions.* If `⋃_j Fix(x^{v_j}) = X` for some nonzero `v_j`, then `W = ∅` as well.
