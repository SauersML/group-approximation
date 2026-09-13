# Nonexistence side of Zaremsky Problem 1.10, part 3: circle rotation codings are never of finite type

Lane `z1-10-simple-amen-block`, 2026-09-13. **Unreviewed.** Uses Theorem G of part 2
(`fp-alternating-full-groups-of-free-subshifts-force-sft`).

## 0. Outcome

**Proposition R.** Let `d >= 1` and let `Z^d` act freely on the circle by rotations. Code it by any partition into
finitely many half-open arcs, and let `X` be the closure of the codings. Then `X` is a free minimal subshift that is
not of finite type. Hence `D([[Z^d ~ X]])` and `A([[Z^d ~ X]])` are not finitely presented.

- For `d = 2` this covers the free rank-2 case of the interval exchange groups. JMMdlS proved those amenable, and ChJN
  (arXiv:1602.04255, line 88, as quoted in `research/artifacts/fp-simple-amenable-z2-sft-2026-09-12.md`) realize them
  as full groups of minimal `Z^2`-actions.
- The root `fp-infinite-simple-amenable-group` recorded, under Contrasts, that it was not checked whether those
  systems have periodic approximations. Proposition R does not decide that. It answers what matters for the derived
  and alternating full groups directly, through finite type.
- **Contrast with Labbé.** Labbé's `Omega_U` is a coding of a `Z^2` rotation of the 2-torus by a polygon partition,
  and it is of finite type. The proof below uses that on the circle the combinatorics of the relevant finitely many
  points is only a cyclic order. That survives a rational perturbation. Arrangements of lines in the 2-torus can be
  rigid.

## 1. Setting

- `θ = (θ_1, ..., θ_d)` with `1, θ_1, ..., θ_d` linearly independent over `Q`. `Z^d` acts on `T = R/Z` by
  `m·z = z + m·θ`, freely by independence.
- `E ⊆ T` is a finite set of endpoints. Each arc `[e, e')` between consecutive endpoints carries a letter, and
  `f : T -> A` is the right-continuous coding function. Assume `f` is not constant.
- `c_z(n) = f(z + n·θ)`. The shift is `(m·c)(n) = c(n + m)`, so `m·c_z = c_(z + m·θ)`.
- `X` is the closure of `{c_z : z ∈ T}` in `A^(Z^d)`.
- For finite `K ⊆ Z^d`, `P_K = {(f(z + k·θ))_(k ∈ K) : z ∈ T}`. Patterns of configurations in `X` on translates of `K`
  lie in `P_K`, because `c -> c|K` takes finitely many values and is continuous.

## 2. Proof of Proposition R

**Step 1: `X` has no periodic point, so the action on `X` is free.**
1. Suppose `c ∈ X` and `c(n + u) = c(n)` for all `n`, with `u ≠ 0`. Put `t = u·θ`, which is not in `Z`.
2. `E_t = {z : f(z) ≠ f(z + t)}` is a finite union of half-open arcs. If it had length zero, `f` would be invariant
   under rotation by `t` off a finite set. By right-continuity and density of `Zt`, `f` would then be constant.
3. So `E_t` contains an arc `J` of positive length. Choose `M` with `{n·θ : |n| <= M}` meeting every arc of length
   `|J|/2`. This is possible since `Zθ_1` alone is dense.
4. Take `z` with `c_z = c` on `B(M + |u|)`. Then `c_z(n) = c_z(n + u)` for `|n| <= M`, so `z + n·θ ∉ E_t` for
   `|n| <= M`.
5. Some `n` with `|n| <= M` has `z + n·θ ∈ J`, a contradiction.
6. **Minimality.** Minimality of `X` follows from minimality of the rotation and continuity of `z -> c_z` off the
   countable set of discontinuities. It is not used below.

**Step 2: patterns depend only on a cyclic order.**
1. For `K = B(r)`, put `Σ = {e − k·θ : e ∈ E, k ∈ K}`, a finite labelled set of points of `T` with labels `(e, k)`.
2. The pattern `(f(z + k·θ))_k` is constant on each half-open arc between cyclically consecutive distinct points of `Σ`.
3. Its value on such an arc is determined by where the arc sits among the points `e − k·θ` for each fixed `k`, together
   with the letters of the partition arcs.
4. So `P_K` depends only on the *type*: the cyclic order of the labelled points of `Σ` with coincidences, and the letters.

**Step 3: a rational perturbation with the same type.**
1. **Classes.** Call `e ∼ e'` if `e − e' ∈ Z^d·θ + Z`. Within a class `e = e_0 + v_e·θ (mod 1)` for a unique
   `v_e ∈ Z^d`, by independence.
2. **Coincidences.** A coincidence `e − k·θ = e' − k'·θ` in `Σ` happens exactly when `e ∼ e'` and `v_e − v_(e') = k − k'`.
3. **The perturbation.** For `θ'` near `θ`, put `e' = e_0 + v_e·θ'` in each class, keeping the representative `e_0`.
   Put `Σ' = {e' − k·θ'}` and let `f'` carry the same letters on the corresponding arcs.
   - Every coincidence of `Σ` persists in `Σ'` by construction.
   - Distinct points of `Σ` are at positive distance, so for `θ'` close enough they stay distinct in the same cyclic
     order, and no new coincidence appears.
   - The endpoints `E'` stay in the order of `E`.
4. **Conclusion.** Choose `θ' ∈ Q^d` that close. Then `P_K(θ', f') = P_K(θ, f)`.

**Step 4: a periodic configuration with legal windows.**
1. Let `y(n) = f'(n·θ')`. If `q` is a common denominator of `θ'`, then `y` is invariant under `qZ^d`, so it has a
   finite orbit.
2. The `B(r)`-pattern of `y` at the site `n` is `(f'(n·θ' + k·θ'))_(k ∈ B(r)) ∈ P_(B(r))(θ', f') = P_(B(r))(θ, f)`.
   So every window is legal.
3. By Step 1, `y ∉ X`.

**Step 5: not of finite type.**
1. If `X` were of finite type, then for some `r`, `X` would equal the set of configurations whose `B(r)`-windows all
   lie in `P_(B(r))`.
2. Step 4 gives a configuration outside `X` with that property, for every `r`. ∎

## 3. Consequence

**Corollary R1** (`circle-rotation-zd-derived-full-groups-are-not-fp`).
- `X` is a free subshift over `Z^d` that is not of finite type.
- By Theorem G, `D([[Z^d ~ X]])` and `A([[Z^d ~ X]])` are not finitely presented. More generally, no finitely
  presented subgroup of `[[Z^d ~ X]]` contains the rule 3-cycles of any radius.
- For minimal faithful `Z^d`-subshifts, `D([[Z^d ~ X]])` is finitely generated, infinite and simple (ChJN, Matui, as
  in `minimal-z2-subshift-derived-full-groups-are-fg-simple`). So these are finitely generated infinite simple groups,
  amenable in the rank-2 interval exchange cases, that are never finitely presented.

**Scope.**
- Only free rotation actions of the circle are covered. Rational relations among `1, θ_i` give torsion in the image
  and non-free actions, which are outside Theorem G.
- A fixed partition `E` is needed. The interval exchange group of all discontinuity sets is a directed union over `E`,
  and only its subgroups living in one `[[Z^d ~ X_E]]` and containing the rule 3-cycles are covered.
- Periodic approximations in the sense of `periodic-approximable-subshifts-host-no-fp-simple-group` would kill all
  finitely generated subgroups. Step 4 produces periodic configurations with legal windows, but the stabilizer
  clause of (PA) was not checked here.
