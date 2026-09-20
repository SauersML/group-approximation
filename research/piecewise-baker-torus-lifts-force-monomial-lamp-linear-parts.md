---
rg: 2
id: piecewise-baker-torus-lifts-force-monomial-lamp-linear-parts
kind: claim
title: "Local side splitting kills the char-p lamp route: if some nV-lift of the torus element h = diag(t,t^-1) has a power that is nV-conjugate to a piecewise local baker map, then every affine map lifted through the same phi has monomial linear part, so EL_2(F_p[t,t^-1]) is never reached; monomial is sharp, since a two-box baker in 2V lifts both h and w"
distinct_from:
  char-p-burger-lamp-realizations-refute-haagerup: that is the positive criterion (relative (T) plus a lifting problem) and Proposition B builds one global baker lift of h; this proves that every realization whose torus lift is piecewise baker fails the criterion, and gives a two-box realization of h and w that no single baker power gives
  injective-char-p-lamp-realizations-miss-fixed-points: that kills injective (conjugacy-type) realizations for p >= 3 by counting fixed points; this kills a different class, non-injective and any p, by a tail-reading (side) invariant, and the two-box example here is a homeomorphism V_0 -> M^ with p = 2, outside that kill
  coordinate-shadows-rigidify-abelian-normalizers-in-nv: that rigidifies normalizers of Z^2 subgroups of nV; here the rigidity is of the linear part of affine lifts to a compact module M^, read through which digit coordinate each lamp entry depends on deep down
  lamp-realized-burger-modules-have-positive-characteristic: that forces the characteristic of the module to be positive; this works inside positive characteristic and restricts the lifted linear group to the monomial group
artifacts:
  - experiments/lamp-monomial-2026-09-17/check_two_box_baker.py
  - experiments/lamp-monomial-2026-09-17/check_two_box_baker.out.txt
---

**ESTABLISHED** by `piecewise-baker-torus-lifts-monomial-lamp-proof` (a direct
proof, with no imports beyond definitions).
- Lane proof by swarm-0917-w22-w22-z-follow. Not independently reviewed. No priority claimed.
- It follows up wave 21 (w21-z-break), whose Theorem D / S lives on the swarm branch only (commit
  2f3311cc29, `baker-lifted-torus-generators-force-diagonal-lamp-shears`). That result covers one
  **global** baker power: the reading is then globally side-split, so every lift is diagonal.
  Theorem S'' below is the local version. It covers finitely many boxes with independent side
  assignments and signs, passive coordinates (`n ≥ 3`), powers, and conjugation by any element of
  `nV`. Its conclusion is weaker (monomial, not
  diagonal), and the example shows the weaker conclusion is the true one.

## Setting and conventions

- Notation as in `char-p-burger-lamp-realizations-refute-haagerup`:
  - `R = F_p[t,t^-1]`, `M = R^2`, and `M^ = (F_p^2)^Z` with coordinates `ξ = (α, β)`;
  - `(σα)_m = α_(m+1)`;
  - `γ ∈ GL_2(R)` acts by `A_γ = (γ^-1)^T(σ)`, so `h` acts by `(σ^-1 α, σ β)` and `w` by
    `(β, −α)`.
- For `ε ∈ {α, β}`, write `ξ_(ε,m) : C^n → F_p` for the entry `m` of the component `ε` of `φ`.
- `C = {0,1}^N`. A **box** is a product `u_1C × ... × u_nC` of cylinders.
- Every element of `nV` is a finite box partition, with each box mapped to a box by a
  **coordinate-preserving** prefix replacement `(u_1 v_1, ..., u_n v_n) ↦ (u'_1 v_1, ..., u'_n v_n)`.
  This is Brin's `nV`. The remark at the end handles coordinate permutations.
- The **depth** of a digit of coordinate `i` is its index in `C`, counting from 0.

## Definition (local side split at +∞)

A continuous `φ : C^n → M^` is **locally side-split** if there are:
- a finite box partition `V_1, ..., V_r` of `C^n`;
- for each `b`, two **distinct** sides `S_b(α) ≠ S_b(β)` in `{1, ..., n}`;
- an integer `L` and a function `D : N → N` with `D(m) → ∞`;

such that for all `b`, all `ε` and all `m ≥ 0`, the restriction `ξ_(ε,m)|V_b` depends only on:
- the digits of coordinate `S_b(ε)` at depth `≥ D(m)`, and
- the digits of all coordinates at depth `< L`.

The sides may vary with `b`. The case `r = 1` is w21's global side split.

## Theorem S'' (monomial rigidity)

Let `φ` be locally side-split. Assume (ND−): for each `ε` there is a point `p_ε` such that on every
box neighbourhood `O` of `p_ε`, the span `span{ξ_(ε,m)|O : m ≥ 0}` is infinite-dimensional.

Let `s ∈ nV` and let `a(ξ) = γ·ξ + v` be an affine map with `φ∘s = a∘φ`. Then `γ` is **monomial**:
it is `diag(u_1, u_2)` or `[[0, u_1], [u_2, 0]]` with `u_i ∈ R^× = F_p^× t^Z`.

So the linear parts of all lifts through `φ` lie in the monomial group `(R^×)^2 ⋊ Z/2`, which is
virtually abelian and does not contain `e_12(1)`. Hence the hypothesis
`⟨γ_1, ..., γ_k⟩ ⊇ EL_2(R)` of Theorem R fails for **every** finite or countable family of lifts.

## Lemma W' (piecewise-baker torus lifts are locally side-split)

For coordinates `i ≠ i'`, let `B_(i,i')` be the baker map of `C^n`. It removes the first digit of
coordinate `i` and puts it in front of coordinate `i'`, leaving the other coordinates alone. It
lies in `nV`.

A **piecewise local baker map** is an `f ∈ nV` with the following data:
- `f` preserves each box of a finite box partition `V_1, ..., V_r`;
- on each `V_b`, after stripping the prefixes of `V_b` (identifying `V_b` with `C^n`), `f` is
  `B_(i_b,i'_b)^(k_b)` for some `i_b ≠ i'_b` and `k_b ≠ 0`.

Let `φ` be continuous and affinely spanning, and let `g ∈ nV` satisfy `φ∘g = a_0∘φ` with
`a_0(ξ) = h·ξ + v_0`, which is **any** affine map with linear part `h`. Suppose some power
`c^-1 g^N c` (with `N ≥ 1` and `c ∈ nV`) is a piecewise local baker map. Then:

1. `ψ = φ∘c` is locally side-split. On `V_b`:
   - if `k_b > 0`, then `S_b(α) = i'_b` and `S_b(β) = i_b`;
   - if `k_b < 0`, then `S_b(α) = i_b` and `S_b(β) = i'_b`.
2. `ψ` satisfies (ND−).
3. The lifts through `ψ` are the conjugates `c^-1 s c` of the lifts `s` through `φ`, with the same
   affine maps.

By Theorem S'', every affine map lifted through `φ` has monomial linear part.

## Main corollary (the class kill)

Consider any realization as in Theorem R of `char-p-burger-lamp-realizations-refute-haagerup`, in
any `nV` and for any prime `p`, with `R = F_p[t,t^-1]`. The group generated by the linear parts
contains `h`, so some word `g` in the lifts `g_i` lifts an affine map with linear part `h`.

**No** such word `g` has a power that is `nV`-conjugate to a piecewise local baker map. In
particular, Proposition B's baker lift of `h`, and every piecewise variant of it, can never be
completed to a lift of `EL_2(R)`, whatever the choice of `φ`.

The same holds for any countable family of lifts, as long as the lifted linear group contains `h`.
The one-sided variant below contains no `h`, so this kill says nothing about it.

## Sharpness: a two-box baker lifts h and w (p = 2, n = 2)

The objects:
- Boxes: `V_0 = {x_0 = 0}` and `V_1 = {x_0 = 1}` in `C^2 ∋ (x, y)`, with local coordinates
  `(x', y)` where `x = x_0 x'`.
- Interleaving: `z = Θ(x', y) ∈ F_2^Z`, with `z_d = x'_d` and `z_(−d−1) = y_d` for `d ≥ 0`.
- `φ` on `V_0`: `α_m = z_(1−2m)` and `β_m = z_(2m)`. This is a homeomorphism `V_0 → M^`.
- `φ` on `V_1`: `φ = swap∘φ_0`, that is, `α_m = z_(2m)` and `β_m = z_(1−2m)`.
- `g` = the local `B^2` on `V_0` and the local `B^-2` on `V_1`. The local baker shifts `z` by one
  place, so `g` shifts it by `±2`.
- `s` = flip `x_0`.

Direct computation gives `φ∘g = h∘φ` and `φ∘s = w∘φ`, where `w = swap` in characteristic 2.
The script `experiments/lamp-monomial-2026-09-17/check_two_box_baker.py` checks both identities on
windows `|m| ≤ 10` at 2000 random points, with 0 mismatches.

As a negative control, the global `B^2` fails to lift `h` at 100 of 200 random points, consistent
with failure on `V_1`, where the local sign is wrong.
The script also prints the sides: `V_0` has `(S(α), S(β)) = (y, x)` and `V_1` has `(x, y)`.

Consequences:
- **Monomial cannot be improved to diagonal.** `w` lifts, and so do `h` and `hw`.
- By w21's Theorem D (swarm branch), a global baker power forces every lift to be diagonal. So
  this `g` is not 2V-conjugate to any global baker power. This is a statement about the dynamics
  of `g` in 2V that Theorem D alone does not see.
- The lifted linear group already contains `⟨h, w⟩`, an infinite non-diagonal monomial group. So
  the class kill is exactly at the boundary. Conjugation by `w` turns `e_12(r)` into `e_21(±r)`, so
  `⟨h, w, e_12(1), e_12(t)⟩ ⊇ EL_2(R)`, and what is missing is only the two shears `e_12(1)` and
  `e_12(t)`. The theorem says no `φ` with a piecewise-baker torus lift can ever supply even one
  shear.

## What survives (the open part of the lamp route)

1. **Torus lifts that are not piecewise baker.** A lift `g` of `h` (up to translation) with no power
   `nV`-conjugate to a piecewise local baker map. Elements of 2V can have very complicated dynamics
   (Belk–Bleak: 2V simulates Turing machines, and its torsion problem is undecidable). So a
   classification of lifts of `h` is not expected. A kill of this class needs an invariant of `g`
   that does not pass through a normal form.
2. **The torus-free one-sided variant.** Take `R_+ = F_p[t]` and `M^_+ = (F_p^2)^N`, with `σ` the
   one-sided shift (not invertible). Only the shears `e_12(r)` and `e_21(r)`, `r ∈ F_p[t]`, need to
   lift; no torus element is required. The side-split argument needs `h`, so it says nothing here.
   But `SL_2(F_p[t]) = EL_2(F_p[t])` is not finitely generated (Nagao), so countably many lifts are
   needed. Relative (T) itself is available: `elementary-linear-semidir-pair-relative-t` covers the
   finitely generated ring `F_p[t]`. The gap is that Theorem R is stated for finitely many lifts.
   Whether its proof (lamp lemma plus Lemma T for a countable group) goes through for a countable
   family is **not** checked here. This is recorded as a spark, not a claim.

## Remark (coordinate permutations)

Suppose pieces of `s` may also permute coordinates by `π`, as in the variant of `nV` with
permutations. Then the proof goes through with `S_(b')(ε)` replaced by `π^-1(S_(b')(ε))` in the
column rule. The conclusion (monomial) is unchanged.
