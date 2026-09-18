---
rg: 2
id: pasku-whitehead-proof-gap-relative-exactness-lemma-proof
kind: route
title: Source-level audit locating the failing inference in Pasku's relative exactness lemma
target: pasku-whitehead-proof-gap-relative-exactness-lemma
requires: []
---

# Proof: the gap in Pasku's one-relator-deletion argument

Source: E. Pasku, arXiv:2107.12293v1, e-print `main.tex`, fetched 2026-09-17 and
read at source. Line numbers `l.N` refer to that file. The notation is the
paper's.

## 0. Method notes (paradigm rule)

- **Why this can succeed.** Earlier swarm audits of claimed resolutions stopped
  at abstracts, so nothing was decided. This audit reads the body, finds the
  single load-bearing lemma, and shows two things: the lemma's proof misapplies
  a theorem, and the lemma alone implies the main theorem. So no other part of
  the paper can repair it.
- **First falsifiable step.** Exhibit a 1-cycle of `D_1` in
  `J·s_1·ZF + ZF·s_1·J` that is not a square boundary of `D_1`.
- **Calibration case.** `P = ⟨x,y | x,y⟩`, a contractible complex, with
  `r_0 = y`. The deletion `P_1 = ⟨x,y | x⟩` is aspherical, so no contradiction
  is possible there. The *inference* used in the proof still fails there.

## 1. Setup, as in the paper

- **Presentations.** `P = (x, r)` presents the trivial group `G`. Fix `r_0 ∈ r`,
  set `r_1 = r \ {r_0}`, and let `G_1` be the group of `P_1 = (x, r_1)`. `F` is
  the free monoid on `x ∪ x^{-1}`. The monoid presentations are
  `M = ⟨x, x^{-1} : s⟩` and `M_1 = ⟨x, x^{-1} : s_1⟩`, where `s` (resp. `s_1`)
  contains `(r^{±1}, 1)` for `r ∈ r` (resp. `r_1`) together with the free
  cancellations (l.980–987).
- **Squier complex (l.354–392).**
  - The vertices of `D` are the words of `F`.
  - The edges are `e = (w, s, ε, w')`, with `∂_1 e = ιe − τe`.
  - The 2-cells are squares `[e,f]` with
    `∂_2 [e,f] = e·(ιf − τf) − (ιe − τe)·f`, extended bilinearly.
  - `F` acts on both sides.
  - The components of `D` correspond bijectively to the elements of the
    presented monoid (l.374), so those of `D_1` correspond to `G_1`. Every
    square and every translate `u·Q(r,1)·v` lies in a single component.
- **The ideal `J` (l.374).** It is spanned by the `ιe − τe` over edges `e` of
  the presentation in question, i.e. `J = ker(ZF → Z[monoid])`. For `D` this
  gives `J = ker(ZF → ZG) = ker(ε : ZF → Z)`. For `D_1` it gives
  `J_1 = ker(ZF → ZG_1)`. If `G_1 ≠ 1`, then `J_1 ⊊ J`.
- **Kobayashi–Otto Theorem 6.6, as transcribed at l.393–402.** For a monoid
  presentation `(Σ, R)` with Squier complex `D(R)` and its own ideal `J_R`:
  `Ker ∂_1 ∩ (J_R·R·ZΣ* + ZΣ*·R·J_R) = Im ∂_2`.
- **The complexes `(D,p)` and `(D_1,p_1)` (l.855–862, l.988).**
  - `(D,p)` is obtained from `(D,t)` by attaching 2-cells along `u·Q(r,1)·v`
    for `r ∈ r`, together with 3-cells `[e,σ]` and `[σ,e]`.
  - `(D_1,p_1)` is built the same way from `r_1`, and is a subcomplex of `(D,p)`.
  - The 1-skeleton of `(D_1,p_1)` is `Γ(M_1)`, the 1-skeleton of `D_1`.
- **Theorem `asphh` (l.859).** `P` is aspherical if and only if
  `H_1(D, q ∪ t) = 0`. It is stated for an arbitrary presentation, so it applies
  to `P_1` as well.
- **The relative complex (l.991–1005).**
  - `μ_i` is the quotient map by `C_i(D_1,p_1)`, and `∂̂_i μ_i = μ_{i−1} ∂̃_i`.
  - `C_2(rel) ≅ μ_2(C_2(D)) ⊕ C_2^{q_0}`, where `μ_2(C_2(D))` is spanned by the
    squares `[e,f]` with `e` or `f` an `r_0`-edge.
  - `K_rel = μ_2(C_2(D)) + J·q_0·ZF + ZF·q_0·J`.
- **Lemma `c-rel-ext` (l.1039).** The complex
  `0 → B_2(rel) → K_rel → B_1(D,D_1) → 0` is exact. Concretely,
  `ker(∂̂_2|K_rel) = B_2(rel) = Im ∂̂_3`.

## 2. An elementary invariant of `H_1(D_1)`

Let `E_1` be the set of rules of `s_1` of the form `(r^{±1}, 1)`. Define a
homomorphism `λ : C_1(D_1) → ⊕_{E_1} ZG_1` on positive edges by
`λ(u, s, 1, v) = ū·e_s` when `s ∈ E_1`, and `λ = 0` on free-cancellation edges.

**Lemma 2.1.** `λ` vanishes on `B_1(D_1)`, the boundaries of square 2-cells.

*Proof.* By definition `λ(e·w) = λ(e)` and `λ(w·e) = w̄·λ(e)` for `w ∈ F`.
Extend both rules bilinearly. Then
`λ(∂_2[e,f]) = λ(e·ιf) − λ(e·τf) − λ(ιe·f) + λ(τe·f) = λ(e) − λ(e) − (ιe‾ − τe‾)·λ(f) = 0`,
because `ιe = τe` in `G_1` for every edge `e` of `D_1`. ∎

## 3. The inference at l.1051–1052 is false as stated

The proof of Lemma `c-rel-ext` takes `ξ ∈ ker ∂̂_2 ∩ K_rel` and lifts it to a
chain `Σ z_i σ_i` made of `r_0`-squares and terms `j·q_0·v`, `u·q_0·j`. The
lift's boundary is a 1-cycle of `D_1` lying in `J·s_1·ZF + ZF·s_1·J`. The proof
then asserts that "Theorem 6.6 of [OK2002] implies there is a 2-chain
`Σ k_j β_j ∈ C_2(D_1)`" with the same boundary. That theorem applies to `D_1`
only with `J_1`. The coefficients produced by the lift are `ιf − τf`, where
`f` is an `r_0`-edge, and these lie in `J`, not in `J_1`.

**Proposition 3.1 (explicit failure inside the lemma's own hypotheses).**
Let `P = ⟨x, y | x, y⟩`, which is aspherical and presents the trivial group,
and let `r_0 = y`. Then `G_1 = ⟨y⟩ ≅ Z`. Take the loop `c = q(x,1)` from
l.885 and the `r_0`-edge `f = (1, y, 1, 1)`, and set `σ = Σ ε_i [f, e_i]`,
where `c = Σ ε_i e_i`. Then:

- (a) `ξ := μ_2 σ` lies in `ker ∂̂_2 ∩ K_rel`;
- (b) `∂̃_2 σ = −(y − 1)·c` is a 1-cycle of `D_1` lying in `J·s_1·ZF`;
- (c) `∂̃_2 σ ∉ B_1(D_1)`, so no chain `Σ k_j β_j ∈ C_2(D_1)` as asserted
  exists.

*Proof.*

- (b) By bilinearity of the square boundary,
  `∂̃_2 σ = Σ ε_i (f·(ιe_i − τe_i) − (ιf − τf)·e_i) = f·∂_1 c − (y − 1)·c = −(y − 1)·c`,
  because `∂_1 c = 0`.
  - Every edge of `c` is an edge of `D_1`, and translates of `D_1`-edges are
    `D_1`-edges.
  - `y − 1 = ιf − τf ∈ J`, so `(y − 1)·c ∈ J·s_1·ZF`.
- (a) `σ` is a sum of squares with an `r_0`-edge, so `μ_2 σ ∈ μ_2(C_2(D)) ⊆ K_rel`.
  Also `∂̂_2 μ_2 σ = μ_1 ∂̃_2 σ = 0` by (b).
- (c) `q(x,1) = (1, x, 1, x^{-1}) + (1, x^{-1}, 1, 1) − τ_{xx^{-1}}`, where the
  `τ` term consists of free-cancellation edges (l.881–886). So
  `λ(c) = e_{(x,1)} + e_{(x^{-1},1)}` and
  `λ(−(y − 1)·c) = −(ȳ − 1)(e_{(x,1)} + e_{(x^{-1},1)})`.
  - This is nonzero in `ZG_1^{E_1}`, because `ȳ ≠ 1` in `G_1 ≅ Z`.
  - By Lemma 2.1, the chain is not in `B_1(D_1)`. ∎

In this example the *conclusion* of the lemma still holds. The 3-cell
`[f, σ_c]` on the `q_1`-cell `σ_c` over `c` gives `ξ = −∂̂_3 μ_3[f, σ_c]`.
This is consistent: `P_1` is aspherical, so `c` dies in `(D_1,p_1)`. What
fails is the justification. Section 4 shows that no justification can exist
without proving the main theorem.

## 4. Lemma `c-rel-ext` by itself implies the main theorem

**Proposition 4.1.** Let `P` be a presentation of the trivial group and
`r_0 ∈ r`, and suppose `r_0 ≠ 1` in `G_1`, which is equivalent to `G_1 ≠ 1`.
If the sequence in Lemma `c-rel-ext` is exact for `(P, r_0)`, then
`H_1(D_1, p_1) = 0`. So `P_1` is aspherical by Theorem `asphh` applied to `P_1`.

*Proof.*

1. Let `c = Σ ε_i e_i` be any 1-cycle of `D_1` supported in a single component
   `g ∈ G_1`. Every 1-cycle is a finite sum of such cycles.
2. With `f = (1, r_0, 1, 1)` and `σ = Σ ε_i [f, e_i]`, the computation of
   Proposition 3.1 gives `μ_2 σ ∈ ker ∂̂_2 ∩ K_rel` and `∂̃_2 σ = −(r_0 − 1)·c`.
3. Exactness gives `w ∈ C_3(D,p)` with `μ_2 σ = ∂̂_3 μ_3 w = μ_2 ∂̃_3 w`.
4. So `β := σ − ∂̃_3 w ∈ C_2(D_1, p_1)` and
   `∂̃_2 β = ∂̃_2 σ = −(r_0 − 1)·c`. Hence `r_0·c − c ∈ B_1(D_1, p_1)`.
5. Every 2-cell of `(D_1, p_1)` is a square or a translate `u·Q(r,1)·v`, and
   each lies in one component. So
   `B_1(D_1, p_1) = ⊕_{h ∈ G_1} B_1(D_1, p_1, h)`, and membership can be tested
   componentwise.
6. The chain `r_0·c` lies in component `r̄_0 g`, and `c` lies in component `g`.
   These are different because `r̄_0 ≠ 1`.
7. Taking the component-`g` part gives `c ∈ B_1(D_1, p_1, g)`. So every
   1-cycle bounds, i.e. `H_1(D_1, p_1) = 0`. Since `p_1 = q_1 ∪ t`, Theorem
   `asphh` (l.859, stated for any presentation) gives that `P_1` is
   aspherical. ∎

This argument uses none of the snake-lemma step (l.1067–1096), Lemma `inv`,
Lemma `st`, Proposition `quasi`, Proposition `free`, or the infinite-cyclic
argument (l.1162–1185).

## 5. The case where the inference is valid is trivial

If `G_1 = 1`, then `J_1 = J`, and the transcribed Theorem 6.6 does apply to
`D_1`. In that case the theorem needs no machinery:

- `P` is aspherical with trivial group, so `K(P)` is a contractible 2-complex
  and `Z_2(K(P)) = H_2(K(P)) = 0`.
- `K(P_1)` is a subcomplex with no 3-cells, so
  `H_2(K(P_1)) = Z_2(K(P_1)) ⊆ Z_2(K(P)) = 0`.
- `K(P_1)` is simply connected, so Hurewicz gives `π_2 = 0`, and `K(P_1)` is
  contractible. This holds for finite or countable presentations alike.

## 6. Conclusion

Lemma `c-rel-ext` is the paper's declared key lemma (l.324: "theorem 6.6 of
[OK2002] is vital in the proof of key lemma c-rel-ext").

- **Case `G_1 = 1`.** The lemma's proof is valid, and the theorem is trivial
  (Section 5).
- **Case `G_1 ≠ 1`.** This covers every type-(a) situation, since a finite
  one-cell complement of a contractible 2-complex has `H_1 = Z`.
  - The proof invokes Theorem 6.6 at the wrong ideal, and the invoked inference
    is false (Proposition 3.1).
  - The lemma itself is at least as strong as the theorem (Proposition 4.1).

Therefore arXiv:2107.12293v1 does not prove the type-(a) case. The Ivanov
reduction quoted at l.84 does not yield Whitehead's conjecture from it.

**Class-level remark.** From the long exact sequence at l.989 and
`H_1(D,p) = 0`, the group `H_1(D_1,p_1)` is the cokernel of
`H_2(D,p) → H_2(rel)`. So proving `H_2(rel) = 0`, or any exactness statement
that forces it, is a restatement of asphericity of `P_1`. The only independent
content such a framework can supply is a genuine computation of the relative
2-cycles that involve `r_0`, which is exactly what Section 3 shows was not
supplied.

**Not audited.** The correctness of Props `quasi`, `free` and `p14`, of
Lemma `[A,B]`, and of Theorem `asphh` beyond its statement. None of these
affects the verdict: Proposition 4.1 only uses the statement of `asphh`, which
is a repackaging of Pride's isomorphism `H_1(D,t,1) ≅ π_2(P̂)` (l.662–670)
with the trivial identities killed.
