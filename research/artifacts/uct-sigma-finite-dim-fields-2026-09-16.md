---
title: UCT for continuous fields over countable unions of closed finite-dimensional sets (special-case lane, 2026-09-16)
---

# 0. Statements, and what is new

Throughout, `X` is a second countable locally compact Hausdorff space.  A
subset is *finite-dimensional* if its covering dimension is finite.  Call `X`
**sigma-finite-dimensional** if `X = ⋃_n F_n` with each `F_n` closed in `X` and
finite-dimensional.

**Theorem A.**  Let `X` be sigma-finite-dimensional and let `A` be a separable
nuclear continuous `C_0(X)`-algebra all of whose fibres `A(x)` satisfy the UCT.
Then `A` satisfies the UCT.

**Corollary B.**  Let `A` be a separable nuclear C\*-algebra whose primitive
spectrum is Hausdorff and sigma-finite-dimensional.  If every primitive quotient
of `A` satisfies the UCT, then `A` satisfies the UCT.

**Corollary C.**  Let `X` be sigma-finite-dimensional and let `A` be a separable
nuclear continuous `C_0(X)`-algebra all of whose fibres are KK-contractible (for
example all isomorphic to `O_2`).  Then `A` is KK-contractible; in particular
`K_*(A) = 0`.

**Inputs.**  Dadarlat, *Fiberwise KK-equivalence of continuous fields of
C\*-algebras*, arXiv:math/0611408v2 (read from the PDF on 2026-09-16):

* Theorem 1.4: a separable nuclear continuous `C(X)`-algebra over a finite
  dimensional locally compact space satisfies the UCT if all its fibres do.
* Theorem 2.6: over a compact metrizable finite-dimensional space, a separable
  nuclear continuous `C(X)`-algebra with KK-contractible fibres is
  `KK_X`-contractible.
* Examples 1.2 and Section 3: unital separable continuous fields `E_P` over the
  Hilbert cube, all fibres `O_2`, with `K_0(E_P) ≠ 0`.

Permanence of the UCT class (Rosenberg--Schochet, as collected in
`uct-class-permanence-properties`): KK-invariance, two-out-of-three for
semisplit extensions, nuclear inductive limits.

**What is new.**  Theorem A removes the finite-dimensionality hypothesis of
Dadarlat's Theorem 1.4 in favour of the strictly weaker hypothesis that the base
is a countable union of closed finite-dimensional subsets.  Examples of new
admissible bases: the one-point compactification of `⊔_n [0,1]^n`; a Cantor set
with cubes of every dimension attached along a dense countable set of points
with shrinking diameters; the realization of every countable locally finite
simplicial complex, with simplices of unbounded dimension (the closed simplices
are countably many closed finite-dimensional sets).  Corollary C shows that Dadarlat's Hilbert-cube
phenomenon (nonzero K-theory from `O_2` fibres) cannot occur over any
sigma-finite-dimensional base: the base of such a field must contain a nonempty
closed set all of whose nonempty relatively open subsets are
infinite-dimensional.  I did not find either statement in the sources checked
(Section 8).  The argument is a transfinite patching of Dadarlat's theorem and
could well be known to experts; no priority is claimed.  The derived sequence of
finite-dimensional loci and the Baire step also appear in this graph's W\*-bundle
lane (`r-fibre-w-star-bundle-sigma-finite-dim-base-is-trivial`, artifact of
2026-09-12), in a different category and with a different gluing mechanism.
What this artifact adds is the C\*-algebraic patching of UCT and
KK-contractibility along that sequence (Sections 1, 3, 4, 6), and the boundary
analysis of Section 7.

**What is not claimed.**  Nothing here bears on simple witnesses to the failure
of the UCT: a simple algebra has only trivial `C_0(X)`-structures.  The
statements say only that a non-UCT separable nuclear algebra cannot be assembled
as a continuous field of UCT algebras over a sigma-finite-dimensional base.

# 1. Elementary facts about C_0(X)-algebras

**Conventions.**  Let `Y` be a second countable locally compact Hausdorff space.
A `C_0(Y)`-algebra is a C\*-algebra `B` with a \*-homomorphism
`θ : C_0(Y) → Z(M(B))` such that `θ(C_0(Y))B` spans a dense subspace of `B`.
Write `f·b = θ(f)b`.  Functions on an open `U ⊆ Y` vanishing at infinity are
extended by zero, so `C_0(U) ⊆ C_0(Y)` (the extension is continuous because
`{|g| ≥ ε}` is compact in `U`, hence closed in `Y`).  For open `U` put

```text
I_U = closed linear span of C_0(U)·B,
```

a closed two-sided ideal because `θ(f)` is central.  For closed `F` put
`B(F) = B / I_{Y∖F}`, and for a point `B(y) = B({y})`; write `b(y)` for the image
of `b` in `B(y)`.  `B` is *continuous* if `y ↦ ‖b(y)‖` is continuous for every
`b ∈ B`.  Since `C_c(U)` is dense in `C_0(U)`, `I_U` is also the closed span of
`C_c(U)·B`.  Every `f ∈ C_0(U)` factors as `f = f_1 f_2` with `f_1, f_2 ∈ C_0(U)`
(take `f_1 = |f|^{1/2}` and `f_2 = f/|f|^{1/2}` where `f ≠ 0`, `f_2 = 0`
elsewhere), so `I_U` is also the closed span of `C_0(U)·I_U`.  Images of closed
ideals under surjective \*-homomorphisms are closed (they are images of
C\*-algebras), and this is used silently below.

**F1 (evaluation).**  For `f ∈ C_0(Y)`, `b ∈ B`, `y ∈ Y`: `(f·b)(y) = f(y) b(y)`.

*Proof.*  Pick `h ∈ C_c(Y)` with `h(y) = 1`.  Given `ε > 0` choose a finite sum
`s = Σ k_i·b_i` with `‖b − s‖ < ε`.  Then
`(b − h·b) − Σ (k_i − h k_i)·b_i = (b − s) − h·(b − s)` has norm at most
`(1 + ‖h‖)ε`, and each `k_i − h k_i` vanishes at `y`, so lies in `C_0(Y∖{y})`.
Hence `b − h·b ∈ I_{Y∖{y}}` and `(h·b)(y) = b(y)`.  Also
`f − f(y)h ∈ C_0(Y∖{y})`, so `(f·b)(y) = f(y)(h·b)(y) = f(y)b(y)`.  ∎

**F2 (norm).**  `‖b‖ = sup_y ‖b(y)‖`.

*Proof.*  `≥` is clear.  Choose an irreducible representation `π` of `B` with
`‖π(b)‖ = ‖b‖` (GNS of a pure state `ρ` with `ρ(b*b) = ‖b‖²`).  It extends to a
representation `π̄` of `M(B)` with `π̄(m)π(c) = π(mc)`.  For `f ∈ C_0(Y)` the
operator `π̄(θ(f))` commutes with `π(B)` because `θ(f)` is central, so by Schur's
lemma `π̄(θ(f)) = χ(f)·1` for a \*-homomorphism `χ : C_0(Y) → ℂ`.  Since `π ≠ 0`
and `θ(C_0(Y))B` spans a dense subspace, `χ ≠ 0`, so `χ = ev_y` for some `y`.  Then
`π` kills `C_0(Y∖{y})·B`, hence `I_{Y∖{y}}`, and factors through `B(y)`.  So
`‖b‖ = ‖π(b)‖ ≤ ‖b(y)‖`.  ∎

**F3 (upper semicontinuity).**  `y ↦ ‖b(y)‖` is upper semicontinuous, and
`{y : ‖b(y)‖ ≥ ε}` is compact for every `ε > 0`.

*Proof.*  Fix `y_0` and `ε > 0`.  Choose `s = Σ_{i≤m} g_i·c_i` with
`g_i ∈ C_0(Y∖{y_0})` and `‖b − s‖ < ‖b(y_0)‖ + ε/2`.  There is a neighbourhood
`W` of `y_0` on which `|g_i| < δ` for all `i`, where `δ Σ‖c_i‖ < ε/2`.  By F1, for
`y ∈ W`: `‖b(y)‖ ≤ ‖b − s‖ + Σ |g_i(y)|‖c_i‖ < ‖b(y_0)‖ + ε`.  For the second
claim approximate `b` within `ε/2` by `Σ k_i·b_i` with `k_i ∈ C_c(Y)`; by F1,
`‖b(y)‖ ≤ ε/2` off the compact set `⋃ supp k_i`.  So the closed set
`{‖b(y)‖ ≥ ε}` lies in a compact set.  ∎

**F4 (restriction).**  Let `F ⊆ Y` be closed.  Then `B(F)` is a `C_0(F)`-algebra
with `(f|_F)·(b + I_{Y∖F}) = f·b + I_{Y∖F}`, its fibre at `y ∈ F` is canonically
`B(y)`, and the norm function of `b + I_{Y∖F}` is the restriction to `F` of that
of `b`.  If `B` is continuous, separable, nuclear, so is `B(F)`.

*Proof.*  Every `g ∈ C_0(F)` is a restriction `f|_F` with `f ∈ C_0(Y)` (Tietze in
the one-point compactification `Y⁺`, applied to the closed set `F ∪ {∞}` with
value `0` at `∞`).  If `f|_F = 0` then `f ∈ C_0(Y∖F)` and `f·b ∈ I_{Y∖F}`; and
`I_{Y∖F}` is an ideal.  So the action is well defined; it is central and
nondegenerate because `θ` is.  For `y ∈ F`, functions in `C_0(F∖{y})` are exactly
the restrictions of functions in `C_0(Y∖{y})` (extend by zero to `F`, then by
Tietze as before; the extension vanishes at `y`).  So the ideal of `B(F)` over
`F∖{y}` is the image of `I_{Y∖{y}} ⊇ I_{Y∖F}`, and the fibre is
`(B/I_{Y∖F})/(I_{Y∖{y}}/I_{Y∖F}) ≅ B(y)`, with `b + I_{Y∖F} ↦ b(y)`.  Quotients of
separable nuclear algebras are separable and nuclear (Choi--Effros).  ∎

**F5 (ideals over open sets).**  Let `U ⊆ Y` be open.  Then `I_U` is a
`C_0(U)`-algebra (by restricting `θ`), its fibre at `y ∈ U` is canonically `B(y)`
via `b ↦ b(y)`, and its norm functions are restrictions to `U` of those of `B`.
If `B` is continuous, separable, nuclear, so is `I_U`.

*Proof.*  Nondegeneracy was noted in the conventions.  Fix `y ∈ U` and let
`J_y` be the closed span of `C_0(U∖{y})·I_U`.

(i) `b ↦ b(y)` maps `I_U` onto `B(y)`: for `h ∈ C_c(U)` with `h(y) = 1` and any
`b ∈ B`, `h·b ∈ I_U` and `(h·b)(y) = b(y)` by F1.

(ii) `J_y ⊆ I_U ∩ I_{Y∖{y}}`: clear.

(iii) `I_U ∩ I_{Y∖{y}} ⊆ J_y`.  Let `b ∈ I_U` with `b(y) = 0`, and `ε > 0`.  By F3
there is an open `V ∋ y` with `‖b(z)‖ < ε` on `V`.  Take `h ∈ C_c(V ∩ U)` with
`0 ≤ h ≤ 1` and `h = 1` near `y`.  By F1 and F2, `‖h·b‖ ≤ ε`.  Write `b` as a
limit of sums `Σ k_i·a_i` with `k_i ∈ C_0(U)`; then `b − h·b` is the limit of
`Σ (k_i(1 − h))·a_i` (the error is at most twice that of the approximation).
Each `k_i(1 − h)` lies in `C_0(U∖{y})`, and factoring it as `g_1 g_2` with
`g_1, g_2 ∈ C_0(U∖{y})` gives `(k_i(1−h))·a_i = g_1·(g_2·a_i) ∈ C_0(U∖{y})·I_U`.  So
`b − h·b ∈ J_y`, and `dist(b, J_y) ≤ ε`.

Hence the fibre `I_U/J_y = I_U/(I_U ∩ I_{Y∖{y}}) ≅ (I_U + I_{Y∖{y}})/I_{Y∖{y}} = B(y)`,
with `b + J_y ↦ b(y)`.  Ideals of separable nuclear algebras are separable and
nuclear.  ∎

**F6 (disjoint supports).**  If `U, V ⊆ Y` are disjoint open sets then
`I_U ∩ I_V = 0`.

*Proof.*  For `y ∉ U`, `U ⊆ Y∖{y}`, so `I_U ⊆ I_{Y∖{y}}`.  Every `y` lies outside
`U` or outside `V`, so `b ∈ I_U ∩ I_V` has `b(y) = 0` for all `y`, and `b = 0` by F2.  ∎

**F7 (successive quotients).**  Let `U ⊆ U'` be open in `Y`, and let
`q : B → B(Y∖U)`.  Then `q` induces `I_{U'}/I_U ≅ I^{B(Y∖U)}_{U'∖U}`, the ideal of
the `C_0(Y∖U)`-algebra `B(Y∖U)` over its relatively open subset `U' ∖ U`.

*Proof.*  `ker q ∩ I_{U'} = I_U ∩ I_{U'} = I_U`.  The image `q(I_{U'})` is the
closed span of `(f|_{Y∖U})·q(B)` over `f ∈ C_0(U')`.  Such restrictions lie in
`C_0(U'∖U)`.  Conversely, let `g ∈ C_c(U'∖U)` with compact support `K`.  Extend
`g` by zero to `Y∖U`, then to `f̃ ∈ C_0(Y)` by Tietze, and choose `k ∈ C_c(U')`
with `k = 1` on `K`.  Then `f = k f̃ ∈ C_c(U')` and `f|_{Y∖U} = g`.  Since
`C_c(U'∖U)` is dense in `C_0(U'∖U)`, `q(I_{U'}) = I^{B(Y∖U)}_{U'∖U}`.  ∎

**F8 (increasing unions).**  If `U_1 ⊆ U_2 ⊆ …` are open with union `U`, then
`I_U` is the closure of `⋃_n I_{U_n}`.

*Proof.*  `I_U` is the closed span of `C_c(U)·B`, and the compact support of
`f ∈ C_c(U)` lies in some `U_n`.  ∎

# 2. Dimension theory of the base

Second countable locally compact Hausdorff spaces are metrizable, hence normal,
Lindelöf, and Baire (locally compact Hausdorff).  Closed subsets of such spaces
are again second countable locally compact Hausdorff.  Covering dimension is the
Čech--Lebesgue dimension: `dim Z ≤ n` if every finite open cover of `Z` has a
finite open refinement of order at most `n + 1`.

**D1 (closed monotonicity).**  If `Z` is a closed subset of a normal space `W`,
then `dim Z ≤ dim W`.

*Proof.*  Let `dim W = n` and let `{V_1, …, V_k}` be a finite open cover of `Z`,
`V_i = G_i ∩ Z` with `G_i` open in `W`.  Refine the open cover
`{G_1, …, G_k, W∖Z}` of `W` by a finite open cover of order at most `n + 1`, and
intersect its members with `Z`.  Members contained in `W∖Z` give empty traces,
the others lie in some `G_i` and have traces in `V_i`.  The traces form an open
refinement of order at most `n + 1`.  ∎

**The finite-dimensional locus.**  For a second countable locally compact
Hausdorff space `Y` let

```text
O(Y) = { y ∈ Y : y has a compact neighbourhood N in Y with dim N < ∞ }.
```

It is open: if `N` is such a neighbourhood of `y`, every point of the interior of
`N` has `N` as a neighbourhood.

**D2 (Baire step).**  If `Y` is sigma-finite-dimensional and nonempty, then
`O(Y) ≠ ∅`.  Every closed subset of a sigma-finite-dimensional space is
sigma-finite-dimensional.

*Proof.*  The second sentence: `F ∩ F_n` is closed in `F_n`, so
finite-dimensional by D1.  For the first, write `Y = ⋃_n F_n`.  By the Baire
property some `F_n` has nonempty interior `V`.  Pick `y ∈ V` and a compact
neighbourhood `N ⊆ V` of `y`.  Then `N` is closed in `F_n`, so `dim N ≤ dim F_n`
by D1, and `y ∈ O(Y)`.  ∎

**D3 (derived sequence).**  Define closed sets `X_0 = X`,
`X_{α+1} = X_α ∖ O(X_α)`, and `X_λ = ⋂_{α<λ} X_α` for limit ordinals `λ`.  If `X`
is sigma-finite-dimensional, there is a countable ordinal `γ` with `X_γ = ∅`.

*Proof.*  Each `X_α` is closed and the sequence decreases, so every `X_α` is
sigma-finite-dimensional by D2.  Fix a countable base `(G_j)_j` of `X`.  For each
`α` with `X_α ≠ ∅`, D2 gives a point `x_α ∈ O(X_α)`; choose `j(α)` with
`x_α ∈ G_{j(α)}` and `G_{j(α)} ∩ X_α ⊆ O(X_α)`, possible because `O(X_α)` is
relatively open.  Then `G_{j(α)} ∩ X_{α+1} = ∅`.  If `α < α'` and `X_{α'} ≠ ∅`,
then `X_{α'} ⊆ X_{α+1}`, so `G_{j(α)} ∩ X_{α'} = ∅` while
`x_{α'} ∈ G_{j(α')} ∩ X_{α'}`.  So `j` is injective on the set of ordinals
`S = {α : X_α ≠ ∅}`, which is therefore countable.  `S` is an initial segment
because the sequence decreases, so it does not contain every countable ordinal,
and the least ordinal `γ ∉ S` is countable (it equals the countable set `S` of
its predecessors) and satisfies `X_γ = ∅`.  ∎

**D4 (the class is exactly the one the method sees).**  Conversely, if
`X_γ = ∅` for some ordinal `γ`, then `X` is sigma-finite-dimensional.

*Proof.*  Take `γ` least.  For `α < γ` we have `X_α ≠ ∅` and `O(X_α) ≠ ∅`:
otherwise the sequence would be constant from `α` on and `X_γ = X_α ≠ ∅`.  The
injectivity argument of D3 used only these two facts, so `γ` is countable.  Every
`x ∈ X` has a least `α` with `x ∉ X_α`; it is neither `0` nor a limit, so
`α = β + 1` and `x ∈ O(X_β)`.  Each `O(X_β)` is second countable, hence Lindelöf,
so it is covered by the interiors of countably many compact finite-dimensional
sets `N ⊆ X_β`, which are closed in `X`.  So `X` is a countable union of closed
finite-dimensional sets.  ∎

D4 is not used in the proofs.  It records that sigma-finite-dimensionality is
exactly the condition "the finite-dimensional-locus derivation exhausts `X`".
In the Hilbert cube `Q` every nonempty open set contains cubes of every
dimension, so `O(Q) = ∅` and `Q` is not sigma-finite-dimensional.

# 3. The finite-dimensional patches

In this section `Y` is a second countable locally compact Hausdorff space and
`B` is a separable nuclear continuous `C_0(Y)`-algebra all of whose fibres
satisfy the UCT.  "Two-out-of-three" and "nuclear inductive limits" refer to
items 2 and 3 of `uct-class-permanence-properties`.  Every extension
`0 → J → E → Q → 0` of separable C\*-algebras with `Q` nuclear is semisplit
(Choi--Effros lifting theorem), and all extensions below have nuclear quotients
by F4 and F5.  The zero algebra satisfies the UCT.

**L1 (a patch inside a finite-dimensional compactum).**  Let `N ⊆ Y` be compact
with `dim N < ∞`, and let `U ⊆ Y` be open with `U ⊆ N`.  Then `I_U` satisfies the
UCT.

*Proof.*  Let `q : B → B(N)`.  The open sets `U` and `Y∖N` are disjoint, so by F6
the restriction of `q` to `I_U` is injective.  Its image is the closed span of
`(f|_N)·q(B)` over `f ∈ C_0(U)`.  Since `U` is open in `N`, and extension by zero
identifies `C_0(U)` with the functions in `C_0(Y)` (resp. `C(N)`) vanishing off
`U`, restriction to `N` maps these functions onto `C_0(U) ⊆ C(N)`.  So
`I_U ≅ I^{B(N)}_U`, the ideal of the `C(N)`-algebra `B(N)` over `U`.  There is an
exact sequence

```text
0 → I^{B(N)}_U → B(N) → B(N)(N∖U) → 0.                                (L1.1)
```

By F4, `B(N)` is a separable nuclear continuous `C(N)`-algebra with fibres
`B(y)`, `y ∈ N`, and `B(N)(N∖U)` is a separable nuclear continuous
`C(N∖U)`-algebra with fibres `B(y)`, `y ∈ N∖U`.  The spaces `N` and `N∖U` are
compact metrizable, and `dim(N∖U) ≤ dim N < ∞` by D1.  By Dadarlat's Theorem 1.4
both algebras satisfy the UCT.  (L1.1) is semisplit, so the ideal satisfies the
UCT by two-out-of-three.  ∎

**L2 (the finite-dimensional stratum).**  The ideal `I_{O(Y)}` satisfies the
UCT.

*Proof.*  Each `y ∈ O(Y)` has a compact finite-dimensional neighbourhood; the
interiors of these neighbourhoods cover `O(Y)`, which is Lindelöf.  So
`O(Y) = ⋃_{k≥1} V_k` with `V_k` the interior of a compact set `N_k ⊆ Y` of finite
dimension (if `O(Y) = ∅` there is nothing to prove).  Put `W_0 = ∅` and
`W_k = V_1 ∪ ⋯ ∪ V_k`.  We show by induction that `I_{W_k}` satisfies the UCT.
The case `k = 0` is trivial.  For `k ≥ 1` let `Y' = Y∖W_{k−1}` and
`B' = B(Y')`.  By F7,

```text
I_{W_k} / I_{W_{k−1}}  ≅  I^{B'}_{W_k ∖ W_{k−1}}.
```

By F4, `B'` is a separable nuclear continuous `C_0(Y')`-algebra with UCT fibres,
and `Y'` is second countable locally compact Hausdorff.  The set
`W_k∖W_{k−1} = V_k ∩ Y'` is open in `Y'` and contained in `N_k ∩ Y'`, which is
compact and finite-dimensional by D1.  By L1 applied to `B'`, the quotient
satisfies the UCT.  The extension `0 → I_{W_{k−1}} → I_{W_k} → quotient → 0` is
semisplit, so `I_{W_k}` satisfies the UCT by two-out-of-three.  By F8,
`I_{O(Y)}` is the closure of the increasing union of the `I_{W_k}`, an inductive
limit of UCT algebras with nuclear limit (F5).  So it satisfies the UCT.  ∎

# 4. Proof of Theorem A

Let `X` and `A` be as in Theorem A, let `(X_α)` be the derived sequence of D3,
and let `γ` be a countable ordinal with `X_γ = ∅`.  Put `U_α = X∖X_α`, an
increasing family of open sets with `U_0 = ∅` and `U_γ = X`.  We prove by
transfinite induction on `α ≤ γ`:

```text
S(α):  the ideal I_{U_α} of A satisfies the UCT.
```

* `S(0)`: `I_∅ = 0`.
* `S(α) ⟹ S(α+1)`.  `U_{α+1} ∖ U_α = X_α ∖ X_{α+1} = O(X_α)`, which is open in
  `X_α = X∖U_α`.  By F7,
  `I_{U_{α+1}} / I_{U_α} ≅ I^{A(X_α)}_{O(X_α)}`.  By F4, `A(X_α)` is a separable
  nuclear continuous `C_0(X_α)`-algebra with UCT fibres over the second countable
  locally compact Hausdorff space `X_α`, and `O(X_α)` is its finite-dimensional
  locus computed in `X_α`.  By L2 the quotient satisfies the UCT.  The extension
  `0 → I_{U_α} → I_{U_{α+1}} → I^{A(X_α)}_{O(X_α)} → 0` has nuclear quotient, so it
  is semisplit, and two-out-of-three gives `S(α+1)`.
* Limit `λ ≤ γ`.  `λ` is countable, so there are `α_1 < α_2 < ⋯` with supremum
  `λ`, and `U_λ = X ∖ ⋂_{α<λ} X_α = ⋃_n U_{α_n}`.  By F8, `I_{U_λ}` is the closure
  of the increasing union of the `I_{U_{α_n}}`, which satisfy the UCT by the
  induction hypothesis.  Its limit is an ideal of `A`, hence nuclear, so `S(λ)`
  holds by nuclear inductive limits.

So `S(γ)` holds.  Since `U_γ = X` and `I_X = A` by nondegeneracy, `A` satisfies
the UCT.  ∎

**Where each hypothesis was used.**  Continuity of the field is used only through
Dadarlat's Theorem 1.4 on the compact patches `N` and `N∖U` in L1 (restrictions
of continuous fields are continuous by F4).  The facts F1--F8 hold for every
`C_0(Y)`-algebra.  Nuclearity is used for Theorem 1.4, for semisplitness, and for
inductive limits.  Sigma-finite-dimensionality is used only to make the derived
sequence reach `∅` (D3).  Zero fibres are allowed: Dadarlat's proof of
Theorem 1.4 first passes to the open set of nonzero fibres.

# 5. Corollary B

Dadarlat's introduction (math/0611408v2, p. 1) states, citing references [14]
and [5] of that paper (not fetched here): *any separable
C\*-algebra `A` with Hausdorff primitive space `X` is isomorphic to the
C\*-algebra of continuous sections of a C\*-bundle over `X` with fibers the
primitive quotients of `A`*, and a continuous C\*-bundle is the same as a
continuous `C(X)`-algebra.  For separable `A`, `Prim(A)` is locally compact and
second countable (standard, Dixmier's *C\*-algebras*, Chapter 3; not reproved
here).  So `A` is a separable nuclear continuous `C_0(Prim A)`-algebra whose
fibres are the primitive quotients, and Theorem A applies.  ∎

This corollary depends on the imported bundle fact and on the standard
topology of `Prim(A)`, not only on Theorem A; it is recorded in the artifact and
in prose, and is not part of the claim proved by the route
`uct-for-fields-over-sigma-finite-dimensional-bases-proof`.

**Example.**  Let `X` be the one-point compactification of `⊔_n [0,1]^n`, and let
`D_n` be separable nuclear simple C\*-algebras satisfying the UCT.  Every
separable nuclear algebra with Hausdorff spectrum `X` and primitive quotients
from `{D_n}` (and a UCT quotient at `∞`) satisfies the UCT.  No local
triviality is assumed, and `X` is infinite-dimensional, so Dadarlat's
Theorem 1.4 does not apply directly.  For this particular `X` one extension
suffices (the ideal over `X∖{∞}` is a `c_0`-sum of fields over cubes); the
transfinite induction is needed for long derived sequences.  For instance, with
`K_1 = [0,1]` and `K_{n+1}` the one-point compactification of
`⊔_m K_n × [0,1]^m`, the derived sequence of `K_n` has length `n` (using the
product inequality `dim(N × [0,1]^m) ≤ dim N + m` for compacta), and the
one-point compactification of `⊔_n K_n` has derived length `ω + 1`.

# 6. Corollary C and the Hilbert-cube boundary

**Proof of Corollary C.**

1. *The fibres satisfy the UCT.*  A KK-contractible algebra is KK-equivalent to
   the commutative algebra `0`, so it satisfies the UCT (item 1 of
   `uct-class-permanence-properties`).  By Theorem A, `A` satisfies the UCT.
2. *`K_*(A) = 0`.*  Let `𝒦` be the class of separable C\*-algebras with vanishing
   K-theory.  It contains `0`, satisfies two-out-of-three for all extensions (the
   six-term exact sequence), and is closed under inductive limits (continuity of
   K-theory).  Rerun Sections 3 and 4 with `𝒦` in place of the UCT class.  The only
   input about the UCT class that is not one of these two closure properties is
   Dadarlat's Theorem 1.4 in L1, applied to `B(N)` and `B(N)(N∖U)`.  Replace it by
   Dadarlat's Theorem 2.6: these are separable nuclear continuous `C(M)`-algebras
   with KK-contractible fibres over compact metrizable finite-dimensional spaces
   `M = N`, `N∖U`.  So they are `KK_M`-contractible.  Forgetting the
   `C(M)`-structure is a group homomorphism `KK_M(D, D) → KK(D, D)` sending
   `[id_D]` to `[id_D]`, so `[id_D] = 0` in `KK(D, D)`.  Since `[id_D]` acts as the
   identity on `K_*(D) = KK_*(ℂ, D)`, `K_*(D) = 0`.  With this replacement, L1, L2
   and the induction of Section 4 give `K_*(A) = 0`.
3. *KK-contractibility.*  Since `A` satisfies the UCT, the Rosenberg--Schochet
   sequence `0 → Ext¹_ℤ(K_*(A), K_{*+1}(A)) → KK_*(A, A) → Hom(K_*(A), K_*(A)) → 0`
   is exact, and both outer groups vanish.  So `KK(A, A) = 0`.  ∎

**The Hilbert-cube boundary.**  Dadarlat's fields `E_P` (Examples 1.2, Section 3
of math/0611408v2) are unital separable continuous fields over the Hilbert cube
`Z` with all fibres `O_2` and `K_i(E_P) = C(K, G_i)` for a Cantor set `K`.  They
show that "finite-dimensional" cannot be dropped from Theorem 2.6.  Corollary C
shows that it can be weakened to "sigma-finite-dimensional", and that any
separable nuclear continuous field with KK-contractible fibres and nonzero
K-theory lives over a base whose derived sequence stabilizes at a nonempty closed
set `X_∞` with `O(X_∞) = ∅` (the sequence stabilizes at a countable stage by the
injectivity argument of D3).  The open set `V = X∖X_∞` is a countable union of
compact finite-dimensional sets (the covering argument in the proof of D4), so it
is sigma-finite-dimensional.  By F5 and Corollary C the ideal `I_V` is
KK-contractible.  The extension `0 → I_V → A → A(X_∞) → 0` is semisplit, and its
six-term exact sequences in `KK(D, –)` and `KK(–, D)` show that the quotient map
`A → A(X_∞)` is a KK-equivalence.  So all K-theory of such a field is carried by
the nowhere-finite-dimensional kernel `X_∞`.

*Remark on the examples.*  The fields `E_P` themselves satisfy the UCT.  In
Dadarlat's construction `E_P` is an extension
`0 → C_0(Z∖Y, O_2) → E_P → F → 0` with `F = A ⊗ D`, where `A = ⊗_n B_n` is an
infinite tensor product of full corners `B_n` of matrix algebras over `C(S²)`,
and `D` is a UCT Kirchberg algebra.  Each `B_n` is Morita equivalent to `C(S²)`
(as Dadarlat notes), hence KK-equivalent to it, so finite tensor products satisfy
the UCT (items 1 and 4 of `uct-class-permanence-properties`), `A` satisfies it as
a nuclear inductive limit, `F` as a tensor product, `C_0(Z∖Y, O_2)` as a
KK-contractible algebra, and `E_P` by two-out-of-three.  So these examples are
not UCT counterexamples.  They show that the dimension hypothesis is essential in
Dadarlat's Theorems 1.1 and 2.6; whether any dimension hypothesis is needed in
Theorem 1.4 is open (Section 7).

# 7. Where the method stops

**7.1 The patching principle.**  Sections 3 and 4 use the UCT class only through
the following properties of a class `𝒫` of separable C\*-algebras, relative to
a class `𝒮` of admissible fibres.  `𝒮` needs no closure properties, because the
restrictions `B(F)` and ideals `I_U` have the original fibres (F4, F5).

* (P0) Every separable nuclear continuous `C(M)`-algebra over a compact
  metrizable finite-dimensional `M`, all of whose fibres lie in `𝒮`, lies in
  `𝒫`.  Used in L1, for `B(N)` and `B(N)(N∖U)`.
* (P1) `0 ∈ 𝒫`.
* (P2) For an extension `0 → J → E → Q → 0` of separable nuclear C\*-algebras:
  `E, Q ∈ 𝒫 ⟹ J ∈ 𝒫` (used in L1), and `J, Q ∈ 𝒫 ⟹ E ∈ 𝒫` (used in L2 and in
  the successor step of Section 4).
* (P3) A separable nuclear C\*-algebra that is the closure of an increasing
  sequence of subalgebras in `𝒫` lies in `𝒫`.  Used in L2 and in the limit step.

*Conclusion:* for every sigma-finite-dimensional `X`, every separable nuclear
continuous `C_0(X)`-algebra with all fibres in `𝒮` lies in `𝒫`.  The proof is
Sections 3 and 4 verbatim, with `𝒫` in place of the UCT class.  Two instances
are proved above: `(𝒫, 𝒮) = (UCT, UCT)` is Theorem A, and
`(𝒫, 𝒮) = (K_* = 0, KK-contractible)` is step 2 of Corollary C.

A third candidate, **not verified here**: for a strongly self-absorbing `D`, take
`𝒫 = 𝒮 =` the `D`-stable algebras.  (P0) would come from the theorem of
Hirshberg--Rørdam--Winter on `C_0(X)`-algebras over finite-dimensional spaces,
and (P1)--(P3) from the Toms--Winter permanence properties (ideals, extensions,
inductive limits).  Neither source was fetched in this lane, so no statement or
theorem number is asserted.  If they read as recalled, the principle gives
`D`-stability for separable nuclear continuous fields with `D`-stable fibres over
sigma-finite-dimensional bases.

**7.2 Nowhere-finite-dimensional bases.**  The method dies at a nonempty closed
set `X_∞` with `O(X_∞) = ∅`.  There is no finite-dimensional patch, so the
induction has nothing to start from.  Examples are the Hilbert cube and
`∏_{n≥1} S²`: every nonempty open subset of either contains a closed copy of
`[0,1]^m` for every `m`.

*The principle is false over such bases for general `(𝒫, 𝒮)`.*

* For `(K_* = 0, KK-contractible)` the counterexamples are Dadarlat's `E_P` over
  the Hilbert cube.
* For `(U-stable, U-stable)`, with `U` the universal UHF algebra, take the
  algebra `A = ⊗_n B_n` of Dadarlat's Section 3.  It is a continuous field over
  `∏ S²` with all fibres `U` and `K_0(A) ≅ C(K, ℤ)`.  This group is not
  divisible, while `K_0(A ⊗ U) ≅ K_0(A) ⊗ ℚ` by the Künneth theorem.  So
  `A ≇ A ⊗ U`.

So any extension of Theorem A to the Hilbert cube must use properties of the UCT
class beyond (P0)--(P3).  Neither example is a UCT counterexample: `E_P` by the
remark in Section 6, and `A` as a nuclear inductive limit of the finite tensor
products `⊗_{n≤m} B_n`, which satisfy the UCT.

*What Dadarlat's proof gives without any dimension hypothesis.*  His Section 2
assumes only that `X` is compact metrizable, and Theorem 2.5 is stated there with
no dimension hypothesis.  So a separable nuclear continuous `C(X)`-algebra `A`
over any compact metrizable `X` is `KK_X`-equivalent, hence KK-equivalent, to a
unital separable nuclear continuous `C(X)`-algebra `A♯`.  The fibres of `A♯` are
Kirchberg algebras, and each is KK-equivalent to the corresponding fibre of `A`.
In the printed proof of Theorem 1.4, finite dimensionality enters through [8,
Thm. 4.6] of that paper: an exhaustive sequence of subalgebras of finite
category, to which Lemma 5.1 applies.  I did not read [8].

Taking Theorem 2.5 as printed, the dimension-free form of Theorem 1.4 for
compact metrizable bases is therefore equivalent to the following statement:
*every unital separable nuclear continuous `C(X)`-algebra over a compact
metrizable space, all of whose fibres are UCT Kirchberg algebras, satisfies the
UCT.*  I found no source settling it.  A counterexample would be a separable
nuclear non-UCT algebra and would refute Problem II.  A proof would not settle
Problem II, since Kirchberg's reductions (root node, Attempts (iii)) concentrate
the problem on simple algebras.

**7.3 Upper semicontinuous fields.**  F1--F8, D1--D4, and the arguments of L1,
L2 and Section 4 never use continuity, except through Theorem 1.4 in L1.  So
Theorem A would hold for upper semicontinuous `C_0(X)`-algebras over
sigma-finite-dimensional `X` once Theorem 1.4 holds for upper semicontinuous
`C(M)`-algebras over compact metrizable finite-dimensional `M`.  I have not seen
such a statement.  Dadarlat's Theorem 2.5 and his use of [8] are for continuous
fields.

**7.4 Other dimension classes.**  The class used here consists of countable unions
of closed finite-dimensional subsets.  As far as I recall, Engelking calls such
spaces *strongly countable-dimensional*; this was not checked against the book.
The broader class of countable unions of finite-dimensional subsets that need not
be closed is not covered, because D2 needs closed pieces for the Baire argument.
I have not checked whether the two classes differ for compacta, and nothing is
claimed for the broader class.  Weakly infinite-dimensional bases, and bases with
transfinite dimension, are not addressed either.

**7.5 Fibrewise KK-equivalence.**  Corollary C suggests a sigma-finite-dimensional
form of the KK-part of Dadarlat's Theorem 1.1.  Let `φ : A → B` be a
`C_0(X)`-linear \*-homomorphism of separable nuclear continuous fields over a
sigma-finite-dimensional `X`, with every `φ_x` a KK-equivalence.  Is `φ` a
KK-equivalence?

The natural route has three steps:

1. The mapping cone `C_φ` is a `C_0(X)`-algebra.
2. Corollary C makes it KK-contractible.
3. The Puppe sequence of the semisplit extension `0 → SB → C_φ → A → 0` then
   shows that `φ` is a KK-equivalence.

The missing input is that `C_φ` is a *continuous* field with fibres `C_{φ_x}`.
This needs the fibre functor to be exact on this pullback, which I have not
verified.  The `KK_X`-version would also need six-term and Milnor sequences in
`KK_X` for the extensions of Sections 3 and 4.  Nothing is claimed.

**7.6 Relation to Problem II.**  Theorem A adds one item to the list of what a
witness for `nuclear-algebra-without-uct-exists` must avoid.  A separable nuclear
non-UCT algebra is not a continuous field of UCT algebras over a
sigma-finite-dimensional base.  In particular, by Corollary B and modulo the
imported bundle fact, if its primitive spectrum is Hausdorff and
sigma-finite-dimensional, some primitive quotient fails the UCT.  The problem is
already concentrated on simple algebras, which have only trivial central
structure, so this is structural information and not a reduction of Problem II.

# 8. Sources

**Read in full text (PDF from arXiv, 2026-09-16).**

* M. Dadarlat, *Fiberwise KK-equivalence of continuous fields of C\*-algebras*,
  arXiv:math/0611408v2.  Used: abstract and introduction (including the bundle
  sentence citing its [14], [5]); Theorem 1.1; Examples 1.2; Theorem 1.4;
  standing assumption of Section 2; Theorems 2.5, 2.6, 2.7; Corollary 2.8;
  Section 3 (construction of `A`, `F`, `E_P` and the exact sequence
  `0 → C_0(Z∖Y, O_2) → E → F → 0`); Lemma 5.1; Theorem 5.2; proof of
  Theorem 1.4, which first passes to the open set of nonzero fibres.
* N. Brown, S. L. Browne, R. Willett, J. Wu, *The UCT problem for nuclear
  C\*-algebras*, arXiv:2005.03184v3 (16 Nov 2021).  Consulted for the reduction
  theorems and the known UCT classes.  As far as I found, it records no UCT
  theorem for fields over infinite-dimensional bases.
* C. Schafhauser, A. Tikuisis, S. White, *Nuclear C\*-algebras: 99 problems*,
  arXiv:2506.10902.  Problem II as recorded in the root node.

**Abstracts only (arXiv abstract pages, 2026-09-16).**

* M. Dadarlat, *Continuous fields of C\*-algebras over finite dimensional
  spaces*, arXiv:math/0611405 (finite-dimensional compact metrizable bases).
* M. Dadarlat, C. Pasnicu, *Continuous fields of Kirchberg C\*-algebras*,
  arXiv:math/0409124 (zero-dimensional bases).
* S. Echterhoff, R. Nest, H. Oyono-Oyono, *Fibrations with noncommutative
  fibers*, arXiv:0810.0118 (Leray--Serre type spectral sequence for K-theory of
  fibrations; no UCT statement for general fields in the abstract).
* *Classification of certain continuous fields of Kirchberg algebras*,
  arXiv:1308.2126, and *One-parameter continuous fields of Kirchberg algebras
  with rational K-theory*, arXiv:1306.1691.  Titles and abstracts only from
  search listings; both concern fields with UCT Kirchberg fibres over specific
  low-dimensional bases.

**arXiv search listings (2026-09-16).**  Abstract searches for
`"continuous fields" UCT` and `"C(X)-algebra" "universal coefficient"`, newest
first.  None of the listed abstracts claims a UCT theorem for continuous fields
over infinite-dimensional or countable-dimensional bases.  Other ids from those
listings (2608.13000, 2605.30147, 2604.17921, 2506.22163, 2205.04013) were judged
irrelevant from the listings alone.  Ids consulted for an earlier, abandoned
groupoid angle in this lane (2503.23203, math/0403071, 1511.02697, 2307.08841,
1408.2365, 1709.00222, 1407.1277, 1510.05469, 2406.11787, 2501.01775, 2510.01947)
are not used here.

**Not fetched; cited only as attributed or recalled.**

* References [3], [8], [14], [5], [24] of math/0611408v2, cited only through
  Dadarlat's text.
* Dixmier's *C\*-algebras*, Chapter 3 (topology of `Prim(A)`).
* Engelking's dimension-theory terminology (Section 7.4).
* Hirshberg--Rørdam--Winter and Toms--Winter (Section 7.1).

**Graph nodes consulted.**  `stw99-problem-ii-nuclear-uct`,
`uct-class-permanence-properties` and its citation route,
`coprime-uhf-stabilizations-detect-uct`,
`dadarlat-tracially-af-universal-uhf-reduction-citation` (format),
`r-fibre-w-star-bundle-sigma-finite-dim-base-is-trivial` and its artifact
`research/artifacts/w-bundle-sigma-finite-dim-triviality-2026-09-12.md` (same
derived sequence, W\*-setting), `stw81-af-fibre-fields-have-base-bound`, and
`research/artifacts/stw-uct-reduction-map-2026-09-11.md`.
