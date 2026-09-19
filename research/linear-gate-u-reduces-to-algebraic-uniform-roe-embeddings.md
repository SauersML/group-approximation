---
rg: 2
id: linear-gate-u-reduces-to-algebraic-uniform-roe-embeddings
kind: claim
title: For simple recursively presented inputs the oracle of Track B is free, so linear gate U over a fixed scaffold P is the coefficient-free question whether each canonical algebra R_Γ embeds in the algebraic uniform Roe algebra of P; its C*-analogue holds exactly for exact inputs
distinct_from:
  translation-like-inputs-embed-in-full-groups-over-a-fixed-group: that writes a PERMUTATION action (move tables) into an effective subshift and needs the word problem for (T3); this writes an arbitrary, possibly noncomputable, LINEAR finite-propagation module into an effective subshift, and simplicity of the input replaces (T3).
  non-amenable-scaffolds-absorb-the-leavitt-factor: that shows the permutational caps of gate U do not bind the linear gate and puts Track B over one scaffold; this identifies the linear gate exactly, as an embedding problem with no computability content, and locates its analytic shadow (exactness).
  decidable-algebras-embed-in-oracle-leavitt-crossed-products: that is the open embedding with an oracle subshift chosen together with the embedding; Theorem A here shows the oracle can always be generated from the relations, so only the existence of some bounded-geometry module matters.
  free-algebra-linear-groups-are-exact: that is exactness for one ring inside the hosts; Theorem D here asks the same question for all of GL_n(LC(W) ⋊ P) and shows it decides whether gate U is geometric.
---

**ESTABLISHED** for Theorems A–D (lane proof, bh-algebra; elementary given the cited facts; not reviewed; no
priority claimed). Recalled, not re-read:
- Kirchberg: every unital separable exact C*-algebra embeds unitally in O_2;
- Kirchberg–Wassermann: reduced crossed products of exact C*-algebras by exact groups are exact, and a group
  is exact iff C*_r of it is;
- Ozawa / Skandalis–Tu–Yu: for a finitely generated group P, C*_u(P) = ℓ^∞(P) ⋊_r P is nuclear iff P is exact.

`k` is a finite field, `P` a finitely generated group with solvable word problem and word metric `d`, and `[n] = {1..n}`.
The **algebraic uniform Roe algebra** `C_u[P × [n]; k]` is the algebra of `(P×[n]) × (P×[n])` matrices over
`k` of finite propagation. A **diagonal corner** is `E·M·E` for a diagonal idempotent `E`. A **P-module of
bounded geometry** for a finitely generated unital `k`-algebra `A` is:
- a faithful unital `A`-module `V` with a basis `B`;
- a map `ι : B → P` with fibres of size at most `n` and coarsely dense image;
- a radius `R` such that each generator's matrix has entry `(b, b')` zero whenever `d(ιb, ιb') > R`.

## Theorem A (effective linear Roe principle: the oracle is free)

Let `A` be finitely generated, recursively presented and simple. The following are equivalent.
- **(a)** For some effectively closed free `P`-subshift `W`, `A` embeds unitally in a diagonal corner of
  `M_n(LC(W, k) ⋊ P)`, and the embedding stays injective on every nonempty closed invariant `Z ⊆ W`.
- **(b)** The same holds for some compact metrizable totally disconnected free `P`-space `W`.
- **(c)** `A` has a `P`-module of bounded geometry.

No computability is asked of the module in (c).

**Proof.** (a) ⇒ (b) is trivial.

(b) ⇒ (c).
1. Choose a minimal `Z ⊆ W`. The restricted map is injective, so the restriction `E_Z` of the corner idempotent
   `E = diag(1_(U_1), …, 1_(U_n))` is not zero.
2. Fix `z ∈ Z`. Let `B = {(v, p) : v^(-1)z ∈ U_p}` and `ι(v, p) = v`.
3. `ι(B)` is coarsely dense, because a nonempty clopen subset of a minimal system is visited syndetically.
4. The orbit representation of `M_n(LC(Z) ⋊ P)` on `k^(P·z × [n])` is faithful. The orbit is dense and free,
   and a locally constant coefficient that vanishes on a dense orbit vanishes identically. Its restriction
   to the corner is the required module, and finite propagation is automatic.

(c) ⇒ (a).
1. Write `A = k<a_1..a_m>/I` with `I` c.e. Let `R` be the propagation radius and `r_0` a density radius for `ι(B)`.
   Identify `B` with a subset of `P × [n]`.
2. The alphabet `𝔄` records, at `v ∈ P`:
   - which `(v, p)` lie in `B`;
   - the row-`(v, p)` entries `(T_i)_((v,p),(vg,q))` of each generator, for `g ∈ B_P(R)`.
   Every `x ∈ 𝔄^P` then defines a diagonal idempotent `E^x` and matrices `T_i^x` of propagation at most `R`.
3. In `M_n(LC(𝔄^P) ⋊ P)` put `â_i = E Σ_g (entry function) u_g E`, and send `1 ↦ E`. For a noncommutative
   polynomial `p`, the coefficient of `u_g` in `p(â)` is a locally constant function. At `x`, it is the entry
   `(e, g)` of `p(E^x T^x E^x)`, which depends only on `x` on the ball of radius `R·deg p`. (This is the
   standard orbit-representation calculus.)
4. Let `W_0` be the subshift forbidding two kinds of pattern:
   - every pattern on which some `p ∈ I` has a nonzero entry in row `e`;
   - every `r_0`-ball containing no point of `B`.
   The first list is c.e. because `I` is, the second is finite, and `WP(P)` is solvable. So `W_0` is
   effectively closed.
5. The configuration `x_0` coding `V` lies in `W_0`.
6. Put `W = W_0 × Y`, with `Y` an effectively closed free `P`-subshift (Aubrun–Barbieri–Thomassé, recalled).
7. By construction `a_i ↦ â_i` kills `I`. It is injective: if `p ∉ I`, then `p` acts nonzero on `V`, so some
   row `(v, ·)` of `p(T^(x_0))` is nonzero, and the coefficient function is nonzero at `v^(-1)x_0 ∈ W_0`.
8. For any nonempty closed invariant `Z ⊆ W`, the second forbidden list makes `E_Z ≠ 0`. So `A → E_Z M_n(LC(Z) ⋊ P) E_Z`
   is a nonzero unital map, and it is injective because `A` is simple. ∎

**Remark (groups).** The same argument removes (T3) from the move-table subshift for simple inputs. Replace it
by the finite condition "some generator moves some point in every `r_0`-ball", which a dense realization
satisfies.

## Theorem B (the canonical linear gate)

Fix `P`. Suppose that for every finitely generated `Γ` with solvable word problem, the canonical algebra
`R_Γ = LC(2^Δ, F_2) ⋊ (Z/2 ≀ Δ)`, `Δ = C(Γ)`, has a `P`-module of bounded geometry. Equivalently, `R_Γ` embeds
unitally in a diagonal corner of `C_u[P × [n]; F_2]` whose idempotent has coarsely dense support.

Then every such `Γ` embeds in `GL_(3n)(LC(W, F_2) ⋊ P)`, with `W` effectively closed and free, injectively on
every minimal subsystem.

*Proof.* `R_Γ` is simple:
- its groupoid `(Z/2 ≀ Δ) ⋉ 2^Δ` is minimal, since finite flips make orbits dense;
- it is effective, since a nontrivial `(f, δ)` with `δ ≠ e` moves some coordinate `v` with `v, δ^(-1)v` free
  in any cylinder, and `δ = e` means a nonzero flip.

`R_Γ` is finitely generated and has solvable word problem when `Γ` does. Theorem A gives the corner embedding
`R_Γ ↪ E M_n E`. Then `Γ ≤ H_Γ = EL_3(R_Γ)` (`fg-groups-have-simple-kazhdan-hosts-of-same-wp-degree`), and
`g ↦ g + (1 − E)` embeds `GL_3(E M_n E)` in `GL_(3n)`. ∎

With M1 over `P × Z²` and G2, the conclusion gives Boone–Higman exactly as in Theorem 3 of
`translation-like-inputs-embed-in-full-groups-over-a-fixed-group`:
- pull back along the factor map, which is a unital injective map `LC(Z) ⋊ P → LC(X') ⋊ (P × Z²)`;
- then use Farrell–Jones for the K-gate and Khanh.

So **linear gate U over `P` is a question about uniform Roe algebras with no computability in it**: does each
`R_Γ` embed in `M_n(C_u[P; F_2])`? That is `canonical-algebras-embed-in-algebraic-uniform-roe-algebras`.

## Theorem C (the analytic shadow is exactness)

Let `P` be non-amenable, and let `A_Γ = C(2^Δ) ⋊_r (Z/2 ≀ Δ)` be the C*-form of `R_Γ`.
1. If `Γ` is exact, then `A_Γ` embeds unitally in `C*_u(P)`.
2. If `P` is exact, for example `F_2`, `Z × F_2` or `F_2 × F_2`, and `A_Γ` embeds unitally in a corner of
   `M_n(C*_u(P))`, then `Γ` is exact.

*Proof.*
1. `Δ = E ⋊ Z`, with `E` a directed union of finite powers of `Γ`, is exact, and so is `Z/2 ≀ Δ`
   (`exact-groups-are-closed-under-extensions`). So `A_Γ` is exact (Kirchberg–Wassermann) and embeds unitally
   in `O_2` (Kirchberg). `O_2` embeds unitally in `C*_u(P)` through the two isometries of a 2-to-1 map of
   bounded displacement, as in Theorem 1 of `non-amenable-scaffolds-absorb-the-leavitt-factor`.
2. `C*_u(P)` is nuclear, so every C*-subalgebra of its matrix corners is exact. The unitaries `u_(δ_0(γ))`
   generate `C*_r(Γ)`, because the faithful expectation onto `C(2^Δ)` restricts to the canonical trace. So
   `C*_r(Γ)` is exact, and hence so is `Γ`. ∎

So, analytically, the linear gate over a single tree is solved for every exact input, and it fails for every
non-exact one over every exact scaffold. Decidable non-exact inputs exist
(`decidable-graphical-non-exact-groups-exist`).

## Theorem D (is linear gate U geometric? an exactness dichotomy)

Call `P` **algebraically exact** if every finitely generated subgroup of `GL_n(LC(W, F_2) ⋊ P)` is exact, for
every `n` and every compact totally disconnected `P`-space `W`.
1. If `P` is algebraically exact, linear gate U over `P` fails for every decidable non-exact `Γ`. Track B over
   `P` then needs a scaffold that is not algebraically exact. If every exact group is algebraically exact,
   that means a non-exact finitely presented Farrell–Jones scaffold, the analogue of the permutational
   meta-gate in `translation-like-hosts-are-capped-by-separation-profiles`.
2. If `F_2` is algebraically exact, then `L_(F_2)(1,2)^x` is exact, since `L` embeds unitally in `LC(X_par) ⋊ F_2`.
   So the route through `L^x` in `fp-simple-nonexact-group` would be dead.
3. Known instances of algebraic exactness for rings inside these hosts:
   - commutative coefficient rings (`commutative-ring-linear-groups-have-property-a`);
   - free algebras (`free-algebra-linear-groups-are-exact`).
   Neither reaches the crossed product itself.

*Proof.* (1) holds because gate U puts `Γ` inside such a `GL_n`. (2) holds because `GL_1` contains `L^x`. ∎

## Lesson for general BH

The Kazhdan and separation caps of gate U were caps on permutation matrices. Once the gate is posed linearly,
two things fall away:
- **Computability.** A simple, recursively presented input writes *any* finite-propagation faithful module
  into an effective subshift, just by forbidding local violations of its relations.
- **Geometry, apart from one piece.** What remains is exactness, the only obstruction that survives into the
  C*-analogue. There, a single tree already hosts every exact input (Kirchberg).

So gate U is geometric exactly to the extent that crossed products over exact groups are "algebraically
exact". Two outcomes follow:
- Either a non-exact subgroup of some `GL_n(LC(W, F_2) ⋊ F_2)` exists. Then Track B escapes geometry, and the
  obvious first candidate is `L^x`.
- Or an algebraic Guentner–Higson–Weinberger theorem for Cantor crossed products holds. Then decidable
  monsters force a non-exact finitely presented Farrell–Jones scaffold in both tracks.

The next mechanism to build is an algebraic, coefficient-free Kirchberg embedding of `R_Γ` for exact `Γ`
into `C_u[F_2; F_2]`.
