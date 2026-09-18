---
rg: 2
id: brin-sapir-is-equivalent-to-equal-support-one-bump-pairs-proof
kind: route
title: "Proof: put the generators of H into disjoint f-translated blocks along a Sidon set and multiply them into f"
target: brin-sapir-is-equivalent-to-equal-support-one-bump-pairs
requires: []
---

Notation as in the target claim. Two standard facts about `F` are used
(Cannon–Floyd–Parry, *Introductory notes on Richard Thompson's groups*, Enseign.
Math. 42 (1996), §4): (i) for dyadic `c < d` in `[0,1]` there is a PL homeomorphism
`φ: [0,1] → [c,d]` with dyadic breakpoints and slopes in `2^ℤ` such that `u ↦ φuφ^{-1}`
(extended by the identity) is an isomorphism of `F` onto the subgroup `F_{[c,d]}` of
elements supported in `[c,d]`; (ii) every nontrivial normal subgroup of `F` contains
`[F,F]`, and `[F,F]` contains `F_{[1/4,3/4]} ≅ F`. For `PL_o(I)` take `φ` affine and
replace (ii) by its use below only for the subgroup `F` (the copy of `F` found in `G`),
so nothing changes.

**Construction.** Let `H = ⟨u_1, …, u_k⟩`. By (i) let `v_i = φ u_i φ^{-1} ∈ B_0`, so
`H_0 := ⟨v_1, …, v_k⟩ ≅ H`. Let `τ_m: B_0 → B_m`, `τ_m(x) = f^m x f^{-m}`, an
isomorphism, since `f^m(J) = J_m`. Take positions `a_i = 2^i` (`1 ≤ i ≤ k`). They form a
Sidon set: if `a_l − a_p = a_i − a_j ≠ 0`, then `(l,p) = (i,j)` (compare the 2-adic
valuation `p = j` and the odd part `2^{l−p} − 1 = 2^{i−j} − 1`). Put

`h = τ_{a_1}(v_1) τ_{a_2}(v_2) ⋯ τ_{a_k}(v_k)`,

a product of commuting factors with disjoint supports. Let `g = f h`.

**Disjointness of the blocks.** `J = [c,d]` with `f(c) > d`. Since `f` is increasing,
`f^m(d) < f^{m+1}(c)`, so `J_m < J_{m+1}` and the `J_m` are pairwise disjoint. There
are points of `(0,1)` outside `U = ⋃_m J_m`, for example in `(d, f(c))`.

**(1) `g` is one-bump on `(0,1)`.** `g` fixes `0` and `1`. If `x ∈ (0,1) \ U`, then
`h(x) = x` and `g(x) = f(x) > x`. If `x ∈ J_m`, then `h(x) ∈ J_m`, so
`h(x) ≥ f^m(c)` and `g(x) = f(h(x)) ≥ f^{m+1}(c) > f^m(d) ≥ x`. So `g(x) > x` on
`(0,1)`, and `g ∈ F`.

**(2) Structure of `G`.** `⟨f, g⟩ = ⟨f, h⟩`. Let `N = ⟨f^n h f^{-n} : n ∈ ℤ⟩`. It
contains `h`, is invariant under conjugation by `f^{±1}`, and so is normal in `G`,
with `G = N⟨f⟩`. Here `f^n h f^{-n} = ∏_i τ_{a_i+n}(v_i)`. Every generator of `N`, and
hence every element of `N`, maps each `J_m` to itself, fixes every point outside `U`,
and is supported in finitely many blocks. So restriction gives an injective
homomorphism `N → ⊕_m B_m`, `x ↦ (x|_{J_m})_m`. The `m`-th projection `ρ_m` sends
`f^n h f^{-n}` to `τ_m(v_i)` if `m = a_i + n`, and to `1` otherwise. So
`ρ_m(N) = τ_m(H_0) ≅ H` for every `m`. A nontrivial `f^n` moves the points of
`(0,1) \ U`, which `N` fixes, so `N ∩ ⟨f⟩ = 1` and `G = N ⋊ ⟨f⟩ ≅ N ⋊ ℤ`. The slope of
`f^n x` (`x ∈ N`) at `0` is `2^n`, so `N` is exactly the germ-trivial kernel at `0`,
and at `1` as well.

**(3) EA.** If `H` is elementary amenable, so is `⊕_m τ_m(H_0)`, a directed union of
finite direct products of copies of `H`. Its subgroup `N` is too, and `G`, an extension
of `N` by `ℤ`. Conversely, if `G` is elementary amenable, so is `N`, and so is its
quotient `ρ_0(N) ≅ H`.

**(4) Copies of `F`.** *`G ⊇ F ⇒ H ⊇ F`.* Let `E ≤ G`, `E ≅ F`. Then `E ∩ N` is normal
in `E` with `E/(E ∩ N) ↪ G/N ≅ ℤ`, so `E ∩ N` contains `[E,E]`, which contains a copy
`E_1 ≅ F` by (ii). `E_1` is finitely generated, so `E_1 ≤ N` projects nontrivially to
only finitely many blocks `m_1, …, m_r`, and `E_1 ↪ ∏_{s ≤ r} ρ_{m_s}(N)`. The kernels
`ker(ρ_{m_s}|_{E_1})` are normal in `E_1 ≅ F` and intersect trivially. If all were
nontrivial, each would contain `[E_1,E_1] ≠ 1` by (ii), and so would their
intersection. So some `ρ_{m_s}` is injective on `E_1`, and `F ≅ E_1 ↪ ρ_{m_s}(N) ≅ H`.

*`H ⊇ F ⇒ G ⊇ F`.* Let `N_0 = {x ∈ N : supp x ⊆ J_0}`. It is normal in `N`, because
elements of `N` preserve `J_0`, so `N_0` is normalized by `ρ_0(N) = H_0`: for `y ∈ N`
and `x ∈ N_0`, `y x y^{-1} = ρ_0(y) x ρ_0(y)^{-1}`. Fix `i ≠ j`. The element
`x = f^{-a_i} h f^{a_i} = ∏_l τ_{a_l − a_i}(v_l)` has block-0 coordinate `v_i`. The
element `y = f^{-a_j} h f^{a_j}` has block-0 coordinate `v_j`. A block common to both
has `a_l − a_i = a_p − a_j`. If `l = p` then `i = j`, excluded. Otherwise
`a_l − a_p = a_i − a_j` and the Sidon property gives `(l,p) = (i,j)`, which is block 0.
Coordinates in different blocks commute, so `[x,y] = [v_i, v_j] ∈ N_0`. So `N_0` is a
normal subgroup of `H_0` containing all `[v_i, v_j]`, hence containing their normal
closure `[H_0, H_0]`. If `H ⊇ F`, then `H_0` contains some `E ≅ F`, and
`[E,E] ≤ [H_0,H_0] ≤ N_0 ≤ G` contains a copy of `F` by (ii).

**Equivalences.** (BS) ⇒ (BS₂) ⇒ (BS₁) is trivial, since `x_0` is one-bump on `(0,1)`,
and `⟨x_0, g⟩ = ⟨f, g⟩`. For (BS₁) ⇒ (BS), let `H ≤ F` be a counterexample. By directed
unions, and because `F` is finitely generated, some finitely generated subgroup of `H`
is a counterexample. For it, (3) and (4) make `G = ⟨x_0, g⟩` a counterexample, with
`g` one-bump on `(0,1)` by (1).

**(BS₃).** (BS) ⇒ (BS₃) is trivial. Conversely, if (BS) fails, the previous paragraph
gives a 2-generated counterexample `H = ⟨u_1, u_2⟩`. Apply the construction with
`k = 2` and positions `a_1 = 0`, `a_2 = 1` in place of `1, 2` (the set `{0,1}` is Sidon, and
nothing above used `a_i > 0`). Then `h = v_1 · f v_2 f^{-1}`, and `G = ⟨f, h⟩ = ⟨f, h f⟩ =
⟨f, v_1 f v_2⟩ = ⟨x_0, (v_1 x_0^{-1} v_2)^{-1}⟩ = ⟨x_0, v_2^{-1} x_0 v_1^{-1}⟩` is a
counterexample of the form in (BS₃), with `u = v_2^{-1}` and `v = v_1^{-1}` supported
in `J`. Conversely, for `u, v` supported in `J`, `⟨x_0, u x_0 v⟩ = ⟨f, v^{-1} f u^{-1}⟩ =
⟨f, v^{-1} f u^{-1} f^{-1}⟩`, and `v^{-1}·τ_1(u^{-1})` is supported in `J_0 ∪ J_1`.

**(BS₄).** (BS₃) ⇒ (BS₄) is trivial. Conversely, if (BS) fails, then (BS₁) fails, so
there is a counterexample `H = ⟨x_0, g⟩`. Apply the (BS₃) construction to it with
`u_1 = g` and `u_2 = x_0`, using the fixed `φ` of the claim for both generators. Then
`v_2^{-1} = φ x_0^{-1} φ^{-1} = w` does not depend on `H`. The counterexample
`⟨x_0, v_2^{-1} x_0 v_1^{-1}⟩` is `⟨x_0, w x_0 v⟩` with `v = φ g^{-1} φ^{-1}`, which is
supported in `J`.

*Sharpness of the width.* If `h ∈ B_0`, the conjugates `f^n h f^{-n} ∈ B_n` have pairwise
disjoint supports, so they commute and generate `⊕_n ⟨f^n h f^{-n}⟩`. A nontrivial
element of this direct sum is not a power of `f`, since it fixes `(d, f(c))` pointwise.
So `⟨f, h⟩ ≅ ⟨h⟩ ≀ ℤ`, and `⟨h⟩ ≅ ℤ` when `h ≠ 1`, because `F` is torsion-free.

**`PL_o(I)`.** The same construction with `φ` affine and `f = x_0^{-1}` works for
finitely generated `H ≤ PL_o(I)`. Steps (1)–(3) use only the dynamics. In (4) fact (ii)
is applied only to subgroups isomorphic to `F`. ∎
