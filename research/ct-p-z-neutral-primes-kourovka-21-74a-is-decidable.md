---
rg: 2
id: ct-p-z-neutral-primes-kourovka-21-74a-is-decidable
kind: claim
title: "Kourovka 21.74(a) is decidable for every g in CT_P(Z) (P finite) whose slopes lie in γ^Z for an integer γ ≥ 2, neutral primes allowed: over each flow component either two hyperbolic holonomies have distinct fixed points (bounded fibre depth), or every holonomy fixes one rational center, and then any permuted partition can be truncated to bounded radial depth around that center"
distinct_from:
  ct-p-z-positive-ray-kourovka-21-74a-is-decidable: that proves the positive-ray case only when every prime of S divides γ (no neutral primes) and records the neutral-prime case as open; this settles the neutral-prime case, so the positive-ray case holds with no divisibility hypothesis.
  ct-empty-z-kourovka-21-74a-is-decidable: that is the case P = ∅; its Lemma C needs a_Q ≠ r_Q, which is exactly what fails here.
  ct-z-21-74a-reductions-must-move-coarse-components: that says a reduction must use neutral primes, mixed-sign or rank-two slopes; this removes neutral primes from that list.
---

**ESTABLISHED** (lane proof, bh-2174-rank2, 2026-09-19; not reviewed). No priority claimed.
- **The problem.** Kourovka 21.74(a) (S. Kohl): is it decidable whether a given `g ∈ CT(Z)`
  permutes a nontrivial partition of `Z` into residue classes? (Verbatim check: bh-ref-q11 in
  `ct-empty-z-kourovka-21-74a-is-decidable`.)
- **What this settles.** (a) for every `g ∈ CT_P(Z)` whose slopes lie in `γ^Z`, `γ ≥ 2` an
  integer, with no condition relating `γ` to the primes of the moduli. The neutral primes
  (`p ∈ S`, `p ∤ γ`) left open by `ct-p-z-positive-ray-kourovka-21-74a-is-decidable` are handled.
- **What stays open.** (a) for mixed-sign and rank-two slopes. See "Rank two" at the end: the fibre
  side of the argument is base-independent, so what remains there is base dynamics only.
- **Credit.** The whole frame (forest reduction, skew product, Lemmas A–C, finite search) is
  bh-free-58's V and positive-ray proofs, refereed by bh-ref-q11. The referee's report 782528f690
  located the gap and proposed the three repair routes; this node carries them out. Revealing
  pairs and the decomposition: Brin, Salazar-Díaz, Bleak et al. (arXiv:1107.0672), Gilabert Vio
  (arXiv:2412.08784), Goffer–Lederle. `CT(Z)`: Kohl.

## Setting (from the positive-ray node)

- `S = P ∪ {2}`; `S_0 = {p ∈ S : p ∤ γ}` are the neutral primes. After refining along the ray, `g`
  is a Higman–Thompson element of a forest `F` with `∂F = ∏_{S_+} Z_p × ∏_{S_0} Z/p^(b_p)`, and
  `ĝ` is a skew product over `∂F` with fibre `Φ = ∏_{p∈S_0} Z_p^deep × ∏_{ℓ∉S} Z_ℓ`.
- **Fibre maps are coordinatewise rational affine.** On every `Z_ℓ`, `ℓ ∉ S`, the block at `x` is
  the piece's own formula `y ↦ αy + β` (`α ∈ γ^Z`, `β ∈ Z[1/S]`), the same map for all `ℓ`. On a
  neutral deep coordinate (`y = r + p^b z`) it is `z ↦ αz + t` with `t = (αr + β − s)/p^b ∈ Q`.
  All slopes are units at every fibre coordinate. Compositions and inverses stay of this form, so
  every holonomy below is a tuple of rational affine maps, one per *coordinate type*: the type `S′`
  (one map, acting diagonally on all `Z_ℓ`, `ℓ ∉ S`) and one type per neutral prime.
- **Flow components** `R_1, …, R_s` (clopen, computable, `g^M`-invariant, indecomposable: Lemma
  A), permuted by `g` via `σ`. Each contains an attractor `a` and a repeller `r`, with `g^M`
  formulas `C` (slope `γ^(Mκ_a)`, `κ_a ≥ 1`) and `R` (slope `γ^(Mκ_r)`, `κ_r ≤ −1`).
- **Holonomies.** Let `𝒫` be a permuted box partition. By Lemma B.1 every part meeting `R_j × Φ`
  has base `⊇ R_j`; by Lemma B.3 every map `(β^(N)_(x′))^(−1) β^(N)_x`, `x, x′ ∈ R_j`, fixes every
  fibre box of such a part. Let `H_j` be the group these maps generate. It contains
  `ψ_j = C^(−1)R` (`x = r`, `x′ = a`, `N = M`), with slope `λ_j = γ^(M(κ_r − κ_a)) ≠ 1`.

Fix one coordinate type `c`. The analysis below is per type; for type `S′` the prime `ℓ` ranges
over all `ℓ ∉ S`, for a neutral type it is `ℓ = p`. Write `μ_ℓ = v_ℓ(λ_j − 1)`.

**Basic estimate.** If `h(y) = p + λ(y − p)` fixes the ball `c + ℓ^e Z_ℓ`, then
`v_ℓ(λ − 1) + v_ℓ(c − p) ≥ e`, since `h(c) − c = (λ − 1)(c − p)`.

## Step 1. The dichotomy, decided by a finite test

Call `R_j` *degenerate at `c`* if all of `H_j` (type-`c` components) fixes one point `q_j ∈ Q`, its
*center*. Since `ψ_j` is hyperbolic, the center is unique.

**Lemma 1.**
1. Degeneracy is a property of the `σ`-cycle, and centers are carried: `q_(σj) = β_x(q_j)` for
   every `x ∈ R_j`.
2. Take one attractor `a_i` per component and let `q_i` be the fixed point of its `g^M` formula.
   The cycle is degenerate iff, for every `i` in it, every piece of `g` (refined by neutral base
   classes) meeting `R_i` maps `q_i` to `q_(σi)`. This is a finite test in exact rational
   arithmetic.
3. If `R_j` is not degenerate, a holonomy `h ∈ H_j` with `h(p_j) ≠ p_j` (`p_j` the fixed point of
   `ψ_j`) is found by enumerating `N` and the finitely many formulas of `g^N` on `R_j`.

*Proof.*
- **1.** `(β^(N)_(gx′))^(−1) β^(N)_(gx) = β_(x′) h β_x^(−1)`, with `h` an `(N+1)`-holonomy over
  `R_j`, from `β^(N+1)_x = β^(N)_(gx) β_x`. The `N = 1` holonomies fixing `q_j` say that
  `β_x(q_j)` is independent of `x ∈ R_j`; the displayed identity then shows that this point is
  fixed by all of `H_(σj)`, whose generators all have this form since `R_(σj) = g(R_j)`. Apply the
  same to `σ^(−1)` with `ĝ^(−1)`.
- **2, ⇐.** By induction `β^(N)_x(q_j) = q_(σ^N j)` for all `x ∈ R_j`, since `g^k x ∈ R_(σ^k j)`.
  So every holonomy over `R_j` fixes `q_j`.
- **2, ⇒.** By 1, `β^(M)_(a_i)` maps the center of `R_i` to the center of `R_(σ^M i) = R_i`.
  It is the hyperbolic formula `C`, whose only fixed point is `q_i`; so the center is `q_i`. By 1
  again every piece meeting `R_i` maps `q_i` to the center `q_(σi)`.
- **3.** If every generator fixed `p_j`, then `H_j` would, so `R_j` would be degenerate. Each
  candidate is checked exactly, and the search stops because a moving generator exists. ∎

## Step 2. Depth bounds

**Nondegenerate components.** With `h` from Lemma 1.3, `ψ_j` and `hψ_j h^(−1)` lie in `H_j`,
both have slope `λ_j`, and their fixed points `p_j ≠ h(p_j)` are distinct rationals. By the basic
estimate, every `ℓ`-ball of a fibre box over `R_j` has depth
`e ≤ v_ℓ(p_j − h(p_j)) + μ_ℓ`. This is `≥ 1` for only finitely many `ℓ`. (This is Lemma C with
`h` in place of the second attractor–repeller pair; it covers the referee's route 1, and route 2,
the transit holonomies `C^(−(m+n_0)) T R^m`, is one way to produce `h`.)

**Degenerate components** (center `q = q_j`). For `ℓ` of type `c`:
- **(D1)** `q ∈ Z_ℓ` and `ℓ ∤ λ_j − 1`. Then every part over `R_j` has `ℓ`-component `Z_ℓ`.
  *Proof.* By the estimate, each such ball contains `q`. If some part `A` had `ℓ`-component
  `q + ℓ^e Z_ℓ` with `e ≥ 1` and other components `B′`, pick `b ∈ R_j`, `y′ ∈ B′` and
  `y_ℓ = q + 1`. The part containing `(b, y_ℓ, y′)` lies over `R_j` (Lemma B.1), so its `ℓ`-ball
  contains `q` and `y_ℓ`, hence is `Z_ℓ`, and it contains `(b, q, y′) ∈ A`. Contradiction.
- **(D2)** `q ∉ Z_ℓ`. Then `v_ℓ(c − q) = v_ℓ(q)` for every `c ∈ Z_ℓ`, so `e ≤ μ_ℓ + v_ℓ(q)`.
- **(D3)** `q ∈ Z_ℓ` and `ℓ | λ_j − 1` (the *radial primes*; finitely many). Every `ℓ`-ball
  either contains `q` (a *core ball* `q + ℓ^e Z_ℓ`, any `e`), or satisfies
  `e ≤ v_ℓ(c − q) + μ_ℓ`: it lies in the shell `v_ℓ(y − q) = k` and fixes the unit part modulo
  `ℓ^m`, `m ≤ μ_ℓ`.
- **Parts over several components.** They satisfy every component's constraint. If two of the
  components are degenerate with centers `q ≠ q′`, a ball fixed by both hyperbolic holonomies has
  `e ≤ v_ℓ(q − q′) + max μ_ℓ`.

The referee's example (`g(y) = γ^(κ(y)) y` with a neutral prime, `γ ≡ 1 mod ℓ`) is the case D3:
radial partitions of every depth are permuted. Step 3 shows that depth is never needed.

## Step 3. Radial truncation

Fix a radial prime `ℓ`. Let `E_ℓ` be the largest of: the nondegenerate bounds at `ℓ`, the D2
bounds, the two-center bounds `v_ℓ(q − q′) + max μ_ℓ` over distinct D3 centers, and `0`. Put
`K = E_ℓ + 1` and, for each D3 center `q`, `c_K(q) = q + ℓ^K Z_ℓ`. These cores are pairwise
disjoint.

Say a part `A` (base `b_A`, `ℓ`-ball `D_A`, other fibre components `B′_A`) is *deep* if
`D_A ⊆ c_K(q)` for a D3 center `q`, and *deep-core* if moreover `q ∈ D_A`.

**Lemma 2.** A deep part at `q` lies only over degenerate components with center exactly `q`.
The map `ĝ` sends deep parts at `q` onto deep parts at `q_(σj)`, deep-core onto deep-core, and
non-deep onto non-deep. For a deep part `A` and every `x ∈ b_A`, `β_x(c_K(q)) = c_K(q_(σj))`.

*Proof.* Depth `≥ K > E_ℓ` excludes nondegenerate components, D1, D2, and D3 components with a
different center `q′`: for those, `q′ ∉ D_A` and `v_ℓ(c − q′) = v_ℓ(q − q′)` give depth
`≤ v_ℓ(q − q′) + μ_ℓ < K`. For `x ∈ R_j ⊆ b_A`, `β_x(q) = q_(σj)` (Lemma 1.1) and `β_x` is an
isometry, so `β_x(D_A) ⊆ c_K(q_(σj))` and the image part is deep; it is deep-core when `A` is. For
any `x ∈ b_A`, `β_x(c_K(q))` is a ball of radius `ℓ^(−K)` containing `β_x(D_A)`, which is the same
ball `D_(ĝA)` for all `x ∈ b_A`; so it equals `c_K(q_(σj))`. The same argument for `ĝ^(−1)` shows
non-deep parts map to non-deep parts. ∎

**Truncation.** Let `𝒞` be the certificate of `𝒫` (the parts meeting `V × Φ`). Define

    𝒞′ = {A ∈ 𝒞 : A not deep} ∪ {N_A = b_A × c_K(q) × B′_A : A ∈ 𝒞 deep-core at q}.

**Lemma 3.** `𝒞′` satisfies conditions 1–3 of the search in `ct-empty-z-kourovka-21-74a-is-decidable`
(members disjoint; members over `R_j` cover `R_j × Φ` and each member lies over some `R_j`; `ĝ`
maps each member onto a member; nontrivial). Its `ℓ`-depths are at most `K + max μ_ℓ`, and its
components at every other coordinate are those of members of `𝒞`.

*Proof.*
- **Disjoint.** If `N_A` meets a non-deep `A_2`, then `D_(A_2) ⊇ c_K(q)`, so `A_2` contains
  `(x, q, y′)` for some `(x, y′) ∈ (b_A ∩ b_(A_2)) × (B′_A ∩ B′_(A_2))`, and so does `A`, since
  `q ∈ D_A`. So `A = A_2`, which is impossible. If `N_A` meets `N_(A_3)`, the same point lies in
  `A ∩ A_3`, so `A = A_3`.
- **Cover.** Let `x ∈ R_j` and let `(x, y_ℓ, y′)` lie in a deep part `A` at `q` (so `R_j` has
  center `q`, by Lemma 2). The part `A*` containing `(x, q, y′)` has an `ℓ`-ball containing `q`.
  If that ball contained `c_K(q)`, then `A*` would contain `(x, y_ℓ, y′)`, so `A* = A`. In either
  case `A*` is deep-core, and `N_(A*)` covers `(x, y_ℓ, y′)`. Bases are unchanged.
- **Onto.** By Lemma 2, non-deep members go onto non-deep members. For deep-core `A` with
  `ĝA = A″`, the fibre maps send `B′_A` onto `B′_(A″)` and `c_K(q)` onto `c_K(q_(σj))` for every
  `x ∈ b_A`, so `ĝ(N_A) = N_(A″)`.
- **Nontrivial.** If `𝒞` has a deep part, `𝒞′` contains some `N_A`, whose `ℓ`-ball `c_K(q)` is
  proper (`K ≥ 1`). So either `𝒞′` leaves `Ẑ` uncovered or `|𝒞′| ≥ 2`. Otherwise `𝒞′ = 𝒞`.
- **Depth.** A non-deep ball either contains a core (depth `≤ K`), or misses every core and so has
  depth `≤ max(E_ℓ, K − 1 + max μ_ℓ)`; new balls have depth `K`. ∎

Truncating the radial primes one at a time never changes the components at primes already
treated. Every bound used is a priori, and Lemmas 2–3 use only conditions 1–3 plus the fact that
bases are those of a permuted partition: condition 2 alone gives Lemma B.3 (if `ĝ^N A` is a box,
`β^(N)_x` maps `A`'s fibre box onto it for every `x ∈ b_A`), and truncation keeps the bases. So
the lemmas apply again after each truncation.

## Theorem

For `g` as above, compute: the flow components, the degeneracy test of Lemma 1.2 for each cycle and
each coordinate type, the moving holonomies `h` (Lemma 1.3), and the bounds of Steps 2–3. Let `L`
be the finite set of primes with a positive bound, and `B_ℓ` the bound at `ℓ ∈ L` (Step 3's bound
at radial primes). A candidate is a box (base cylinder with a hull prefix) × (product over `ℓ ∈ L`
of balls of depth `≤ B_ℓ`) × (full factors elsewhere). Then `g` permutes a nontrivial
residue-class partition iff a family of disjoint candidates satisfies conditions 1–3. The search is
finite, so **21.74(a) is decidable on the positive ray, neutral primes allowed.**

*Proof.* **⇒.** Take the certificate of a permuted partition. Steps 2–3 bound it at every prime
outside the radial ones, and at radial ones after truncation (Lemma 3); at D1 primes, and at primes
outside `L`, all components are full. **⇐.** Exactly as in the V node: the complement `Q` of the
family is a finite union of boxes, `ĝ`-invariant and inside `U × Φ`, where `ĝ^N = id` because
`g^N` has identity formulas on `U` (canonicity, confirmed by the referee for the positive ray).
Refining `Q` gives a permuted partition. ∎

## Check: the referee's degenerate example

`g(y) = γ^(κ(y)) y` with a neutral prime and `γ ≡ 1 mod ℓ`. Every formula fixes `0`, so the cycle
is degenerate with center `0` (Lemma 1.2) and `ℓ` is radial. Radial partitions around `0` of every
depth are permuted; truncation at `K` replaces all the deep structure by the single core
`ℓ^K Z_ℓ`, which leaves e.g. the depth-1 radial partition `{classes mod ℓ}` (permuted, since
`γ ≡ 1 mod ℓ`). So the answer is found at bounded depth, as the Theorem predicts.

## Rank two (remark; sketch, not a theorem)

Nothing in Steps 1–3 uses that the base is a tree. They use only: a clopen `g`-invariant
decomposition of the base into a part `U` where `g^N` has identity formulas and finitely many
computable indecomposable flow components, each with an attracting and a repelling periodic point
whose formulas have distinct slopes `≠ 1`; Lemma B.1 hulls; and rational affine fibre maps with
unit slopes. So for any `g ∈ CT(Z)`, with any slopes, whose base dynamics admits such a computable
decomposition (after moving isometric coordinates into the fibre, as neutral digits are moved
here), the same search should decide 21.74(a). For rank-two and mixed-sign slopes the missing input
is therefore the base decomposition itself. It fails for hyperbolic components, such as Conway's
amusical permutation (conjugate to the full 3-shift), and for Collatz-type components.

## Lesson for general BH

**Degenerate holonomy is radial, and radial structure truncates.** When every holonomy over a
component fixes one rational center, the dynamics commutes with scaling about that center, so the
deep part of any invariant structure can be collapsed to a single core ball without breaking
invariance. Combined with the two-center bound, fibre (coordinate) structure is always decidable.
Whatever is hard about residue-class questions in `CT(Z)` lives in the base dynamics, i.e. in
elements whose slopes pull primes in opposite directions. In particular a reduction for 21.74(a)
(`ct-z-21-74a-reductions-must-move-coarse-components`) can no longer use neutral primes on a
positive ray; it must use mixed-sign or rank-two slopes.
