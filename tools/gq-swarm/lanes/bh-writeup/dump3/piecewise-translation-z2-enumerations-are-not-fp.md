---
rg: 2
id: piecewise-translation-z2-enumerations-are-not-fp
kind: claim
title: If the successor map of an enumeration of Z^2 is a piecewise translation over finitely many polyhedral pieces, then the near shift group is not finitely presented, so no Mallery-Zaremsky or Houghton-like envelope of that enumeration is
requires:
  - fp-groups-without-free-subgroups-split-ascendingly-over-kernels
  - houghton-like-envelopes-have-fp-germs-iff-fp-near-shift-group
  - mz-envelope-germ-group-is-an-antitwisted-fiber-product
  - shell-germ-fp-is-an-ascending-hnn-gate
distinct_from:
  square-spiral-z2-near-shift-group-is-not-finitely-presented: that is one enumeration, proved through a metabelian structure and a machine check of the line-shift pattern; this covers every piecewise-translation enumeration, with no metabelian or computational input.
  free-shift-houghton-like-envelopes-are-not-fp: that kills the generic enumerations (R_nu = P * Z finitely presented, but not pinned); this kills the opposite, locally rigid class at the germ level (R_nu not finitely presented).
  finite-ray-shift-envelopes-require-virtually-cyclic-input: that excludes finite-ray (eventually periodic) realizations for non-virtually-cyclic inputs; this excludes two-dimensional polyhedral realizations of Z^2 that use translations only.
---

**ESTABLISHED** (lane proof, written inline, not independently reviewed, no priority claimed). It proves the
prediction in `boone-higman-mz-antitwisted-germ-gate-2026-09-17.md` §6 that every piecewise-translation
enumeration of `Z^2` dies at the near shift group.

**Setting.**
- A *polyhedral set* is `Z^2 ∩ C`, where `C ⊂ R^2` is a convex polygon with rational edge directions. `C` may be
  unbounded or degenerate, and its edges may be open or closed.
- For a bijection `nu : Z^2 -> N`, the successor map is `sigma(p) = nu^-1(nu(p) + 1)`. Call `nu` a
  *piecewise-translation enumeration* if there are a finite partition `Z^2 = A_1 ⊔ ... ⊔ A_r` into polyhedral
  sets and vectors `t_i ∈ Z^2` such that `sigma(p) = p + t_i` for all but finitely many `p ∈ A_i`.
- Transported to `Z^2` by `nu`, `R_nu = <L_h, sigma>`. It lives in `NearSym(Z^2)`, permutations modulo finitary
  ones, and `L_h` is translation by `h`. The near index `eta` has `eta(sigma) = 1` and `eta(L_h) = 0`.

Examples include the square spiral, the 45-degree diamond spiral, and every spiral or shell enumeration whose
turns lie on finitely many rational rays.

**Statement.** Let `nu` be a piecewise-translation enumeration of `Z^2`.
1. `R_nu` is (abelian-by-locally-finite)-by-abelian, so it contains no free subgroup of rank 2.
2. `R_nu` is not finitely presented.
3. Therefore none of the following is finitely presented:
   - `E_nu(Z^2)`, by `mz-envelope-germ-group-is-an-antitwisted-fiber-product`;
   - `H_n(E_nu(Z^2))` for any `n >= 1`, by item 4 of `houghton-like-envelopes-have-fp-germs-iff-fp-near-shift-group`;
   - the shell germ group, by `shell-germ-fp-is-an-ascending-hnn-gate`.

## Proof

Maps compose right to left, and equalities hold off finite sets.

**Step 0. Critical directions.**
- The classes that are piecewise translations over finite polyhedral partitions form a subgroup `PT` of
  `NearSym(Z^2)`. The pieces of `gh` are `A_i(h) ∩ (A_j(g) - t_i(h))`, and the pieces of `g^-1` are
  `A_i + t_i`. Every `L_h` and `sigma` lies in `PT`, so `R := R_nu ≤ PT`.
- A direction `θ` is *regular* for `g` if some open cone around `θ`, minus a bounded set, lies in one piece.
  The non-regular directions are recession directions of edges, so they are finite and rational.
- Translations fix directions. So `crit(gh) ⊆ crit(g) ∪ crit(h)`, and `crit(L_h) = ∅`. Hence
  `Θ := crit(sigma)` contains `crit(g)` for every `g ∈ R`.
- Let `I_1, ..., I_m` be the arcs of `S^1 \ Θ`. On cones over compact subarcs of `I_j`, each `g ∈ R` is far out
  one translation `tau_j(g)`. The maps `tau_j : R -> Z^2` are homomorphisms with `tau_j(L_h) = h`.

**Step 1. Half-line germs.**
- Fix `θ ∈ Θ`. Let `d` be a primitive vector in direction `θ` and `n ⊥ d` a primitive vector.
- For `c ∈ Z`, let `ℓ_c = {x ∈ Z^2 : <n,x> = c}` and consider its far part in direction `θ`. That far part lies
  in a single piece of `g`, because each piece meets it in an interval.
- So `g` translates the far part of `ℓ_c` by one vector `v_c(g)` onto the far part of `ℓ_(π(c))`, where
  `π(c) = c + <n, v_c(g)>`.
- Since `g` is a near bijection and translations preserve direction, `π = π_θ(g)` is a permutation of `Z`:
  - For surjectivity, a tail of `ℓ_c'` has infinitely many preimages under one piece translation `v`. These lie
    on the tail of `ℓ_(c' - <n,v>)`.
  - Two half-lines landing on one tail would give infinitely many collisions.
- Let `τ_-(g)` and `τ_+(g)` be the translations of the arcs adjacent to `θ` on the `-n` and `+n` sides.
  - The pieces' edges parallel to `θ` have finitely many offsets `b_1 < ... < b_q`.
  - For `c < b_1`, all far parts of the `ℓ_c` lie in one convex piece. Its entry thresholds grow linearly in `|c|`,
    so its recession cone contains an open arc of directions on the `-n` side.
  - Hence `v_c(g) = τ_-(g)` for `c ≪ 0`, and likewise `v_c(g) = τ_+(g)` for `c ≫ 0`.
- The cocycle rule is `v_c(gh) = v_(π_θ(h)(c))(g) + v_c(h)`.

**Step 2. Zero flux.**
- `π_θ(g)` is translation by `<n, τ_-(g)>` for `c ≪ 0` and by `<n, τ_+(g)>` for `c ≫ 0`.
- For a permutation `π` of `Z`, the flux `|π(A_K) \ A_K| - |A_K \ π(A_K)|` with `A_K = (-∞, K]` does not depend
  on `K`. At `K ≪ 0` it equals the first translation amount, and at `K ≫ 0` the second. So the two amounts are
  equal.
- Hence `χ_θ(g) := <n, τ_-(g)> = <n, τ_+(g)>`. This is a homomorphism `R -> Z` with `χ_θ(L_h) = <n,h>`, so it is
  onto.
- *This is the only step that needs translations.* A rotation or reflection could move half-lines between
  different critical directions.

**Step 3. No free subgroups (item 1).**
- Put `T = (τ_j)_j : R -> (Z^2)^m`. For `g ∈ ker T`, each `π_θ(g)` is finitary and each `v(g)` is finitely
  supported. So Step 1 gives homomorphisms `γ_θ : ker T -> (Z^2)^(Z) ⋊ FSym(Z)`.
- The joint map `(γ_θ)_θ` is injective. Every unbounded piece of `g` either contains a far half-line in a regular
  direction, so its translation is some `τ_j(g) = 0`, or contains the far part of some `ℓ_c` at some `θ ∈ Θ`, so
  its translation is `v_c(g) = 0`. So `g` is finitary.
- Hence `ker T` is abelian-by-locally-finite and `R/ker T` is abelian.
- Such groups contain no `F_2`. A free subgroup would meet the abelian normal subgroup in a normal free subgroup of
  rank at most 1, hence trivially. It would then embed in a locally finite-by-abelian quotient.

**Step 4. An active direction.**
- Call `θ` *active* for `g` if the `v_c(g)`, for `c ∈ Z`, are not all equal.
- Some `θ ∈ Θ` is active for `sigma`. Otherwise `τ_- = τ_+` at every `θ`, so all `τ_j(sigma)` equal one vector
  `v`, and every half-line germ is translation by `v`. (If `Θ = ∅`, `sigma` is one translation far out.) Then
  `sigma L_(-v)` is finitary by Step 3, contradicting `eta(sigma L_(-v)) = 1`.
- Fix such a `θ`, put `χ = χ_θ`, and let `g_0 = sigma L_h` with `<n,h> = -χ(sigma)`. Then:
  - `g_0 ∈ ker χ`;
  - `v_c(g_0) = v_(c + <n,h>)(sigma) + h`, so these values are not all equal;
  - so there are offsets `c_±` with `v_(c_±)(g_0) ≠ τ_±(g_0)`.
- For `<n,h'> = ±1`, the conjugate `L_(k h') g_0 L_(-k h')` lies in `ker χ` and has the same `τ_±`. Its value
  `v_c` equals `v_(c ∓ k)(g_0)`. So it disagrees with `τ_+` at the offset `c_+ ± k`, and with `τ_-` at `c_- ± k`.

**Step 5. No ascending splitting (item 2).**
- Suppose `R` is finitely presented. By Step 3 and `fp-groups-without-free-subgroups-split-ascendingly-over-kernels`,
  there are a finitely generated `H ≤ ker χ` and `w` with `χ(w) = ε = ±1` and
  `ker χ = ∪_(k≥0) w^k H w^-k`. Take `ε = -1`; the case `ε = +1` is symmetric, using `c ≤ -M` and `τ_-`.
- Choose `M` with the following properties:
  - each generator of `H`, and its inverse, fixes every offset `c ≥ M` and has `v_c = τ_+` there;
  - `π_θ(w)(c) = c - 1` for `c ≥ M`, by Step 2.
- Using the cocycle and `χ = 0` on `H`, every `h ∈ H` has these two properties for `c ≥ M`.
- `π_θ(w^-k)` maps `[M, ∞)` into itself. For `c ≥ M` and `c' = π_θ(w^-k)(c)`:

      v_c(w^k h w^-k) = v_c'(w^k) + τ_+(h) + v_c(w^-k) = τ_+(h) = τ_+(w^k h w^-k).

- So every element of `ker χ` agrees with its `τ_+` on every `ℓ_c` with `c ≥ M`. This contradicts Step 4, for `k`
  large. ∎

## Scope and leads

- **Recovers** `square-spiral-z2-near-shift-group-is-not-finitely-presented` without its machine check. Its
  character `chi_1` is `χ_θ` at the NE diagonal.
- **What survives: piecewise isometries.** If `sigma` also uses finitely many rotations or reflections, half-lines
  can pass between the slices `θ` and `Aθ`. Step 2 then fails, and the two end characters at a slice can differ,
  like the ray characters of Houghton's `H_n`: finitely presented for `n >= 3`, with non-antipodal `Σ^c`. The 1-D
  zigzag, whose `E_nu(Z)` is finitely presented (`zigzag-cyclic-shift-envelope-is-finitely-presented`), is of this
  reflecting kind. Two-dimensional reflecting or rotating polyhedral enumerations of `Z^2` are the natural
  remaining candidates for a finitely presented `R_nu` together with local rigidity
  (`fsym-containing-fp-groups-are-pinned-by-finitely-many-equations`). Not decided here.
- **Not checked:** pieces refined by congruence classes (polyhedral sets intersected with cosets of a finite-index
  sublattice). Replacing each half-line by its residue half-lines should carry Steps 1–5 over, but this is not
  checked.
