---
rg: 2
id: self-wreathing-groups-have-full-sigma-invariants-proof
kind: route
title: Every character of R = R wr_X P restricts to the diagonal (lambda,...,lambda) on the finite-index base R^X, and diagonal characters of a product of |X| infinite factors avoid every Sigma-complement and every nonzero L2-Kunneth term below degree |X|
target: self-wreathing-groups-have-full-sigma-invariants
requires:
  - fully-self-replicating-tree-groups-give-fg-tits-hosts
---

The notation is that of the target. Write `θ = χ ∘ ψ^{-1}` for a character `χ` of `R`,
viewed on `W = R^X ⋊ P`. For `x ∈ X` let `ι_x : R → R^X` put `r` in coordinate `x` and
`1` elsewhere.

**Examples.** A fully self-replicating `R ≤ Aut(X*)` with root image `P` satisfies
`R ≅ R^X ⋊ P` through its section map, by (R1) of
`fully-self-replicating-tree-groups-give-fg-tits-hosts-proof` (with `P` in place of `A_d`).
So everything below applies to it.

**`R` is infinite.** If `R` were finite, then `|R| = |R|^d |P|` with `d ≥ 2` would force
`|R| = 1`, and `R ≠ 1` by hypothesis.

## 1. Item 4: characters restrict diagonally

Let `χ ≠ 0`. `θ` vanishes on the finite group `P`. Conjugation by `p ∈ P` carries
`ι_x(r)` to `ι_{p·x}(r)`, and `θ` is conjugation-invariant. So `λ_x := θ ∘ ι_x` is
independent of `x`, because `P` is transitive. Call it `λ`. Then
`θ((r_x)_x) = Σ_x λ(r_x)` on `R^X`. If `λ = 0`, then `θ` vanishes on `R^X` and on `P`.
These generate `W`, so `θ = 0` and `χ = 0`, a contradiction. So `λ ≠ 0`.

## 2. Item 1: `Σ¹(R) = S(R)`

Recall the Bieri--Neumann--Strebel definition. For a finitely generated group `G`,
a finite generating set `S` and `χ ≠ 0`, `[χ] ∈ Σ¹(G)` iff the full subgraph of the
Cayley graph `Cay(G, S)` on `G_χ = {g : χ(g) ≥ 0}` is connected. This does not depend
on `S`. Two facts are used.

- **(F1) Finite index** (Bieri--Neumann--Strebel, Invent. Math. 90 (1987), cited).
  Let `H ≤ G` have finite index. Then `[χ] ∈ Σ¹(G)` iff `[χ|_H] ∈ Σ¹(H)`.
- **(F2) Products.** Let `G = A × B` with `A, B` finitely generated, and let
  `χ = (α, β)` with `α ≠ 0 ≠ β`. Then `[χ] ∈ Σ¹(G)`.

*Proof of (F2).* Choose `a ∈ A` with `α(a) > 0` and `b ∈ B` with `β(b) > 0`. Let `S` be
a finite generating set of `A` together with one of `B`, plus `a` and `b`. Take
`g = (g_1, g_2)` with `χ(g) = α(g_1) + β(g_2) ≥ 0`. We join `g` to `1` by a path that stays
in `G_χ`. Edges are right multiplications by elements of `S^{±1}`.

1. Multiply by `a` a total of `K` times. `χ` increases at each step.
2. Spell a word in `S_B` for `g_2^{-1}`. The vertices are `(g_1 a^K, g_2 u)` for the
   prefixes `u`. Their `χ`-values are at least `α(g_1) + Kα(a) − M_2`, where `M_2` bounds
   `|β(g_2 u)|` over the prefixes. Choose `K` so that this is `≥ 0`. We reach `(g_1 a^K, 1)`.
3. Multiply by `b` a total of `L` times. We reach `(g_1 a^K, b^L)`.
4. Spell a word in `S_A` for `(g_1 a^K)^{-1}`. The vertices are `(g_1 a^K u, b^L)`, with
   `χ ≥ Lβ(b) − M_1`. Choose `L` so that this is `≥ 0`. We reach `(1, b^L)`.
5. Multiply by `b^{-1}` a total of `L` times. The `χ`-values are `jβ(b) ≥ 0`. We reach `1`.

So the full subgraph on `G_χ` is connected. ∎

*Proof of item 1.* Let `χ ≠ 0`. By item 4, `θ|_{R^X} = (λ, …, λ)` with `λ ≠ 0`. Write
`R^X = R × R^{X ∖ {x_0}}`. Both components of `θ|_{R^X}` are nonzero, since `d ≥ 2`.
So `[θ|_{R^X}] ∈ Σ¹(R^X)` by (F2). The subgroup `R^X` has index `|P|` in `W`, so
`[θ] ∈ Σ¹(W)` by (F1). Transporting along `ψ` gives `[χ] ∈ Σ¹(R)`.

The consequence is the BNS theorem (Theorem B1 of BNS, cited). For `N ⊴ G` with `G/N`
abelian, `N` is finitely generated iff every character vanishing on `N` lies in `Σ¹(G)`. ∎

## 3. Item 2: higher Σ over a field

The following are cited.

- **(F3) Finite index** (Bieri--Renz, Comment. Math. Helv. 63 (1988)). The analogue of
  (F1) holds for `Σ^n(−; A)`, for any coefficient ring `A`.
- **(F4) Kernel criterion** (Bieri--Renz). For `G` of type `FP_n` over `A` and `N ≥ [G, G]`,
  `N` is of type `FP_n` over `A` iff every character vanishing on `N` lies in `Σ^n(G; A)`.
- **(F5) Product formula over a field** (Bieri--Geoghegan, Groups Geom. Dyn. 4 (2010)).
  For `G, H` of type `FP_n` over a field `k`,
  `Σ^n(G × H; k)^c = ⋃_{p+q=n} Σ^p(G; k)^c ∗ Σ^q(H; k)^c`.
  Here `Σ^0(·)^c = ∅`, and the join `A ∗ B` contains a class `[(χ_1, χ_2)]` with both
  components nonzero iff `[χ_1] ∈ A` and `[χ_2] ∈ B`.

**Lemma.** Let `R` be of type `FP_n` over `k`, and let `m ≥ 1` and `0 ≤ n ≤ m − 1`. If
`λ_1, …, λ_m` are all nonzero, then `[(λ_1, …, λ_m)] ∈ Σ^n(R^m; k)`.

*Proof.* Induct on `m`. For `m = 1`, `n = 0`, and `Σ^0 = S`. For the step, `n ≤ m`, and
`R^{m+1} = R × R^m` with both factors of type `FP_n`. Suppose the class were in the
complement. By (F5) there are `p + q = n` with `[λ_1] ∈ Σ^p(R; k)^c` and
`[(λ_2, …, λ_{m+1})] ∈ Σ^q(R^m; k)^c`. The first forces `p ≥ 1`. The induction
hypothesis puts the second class in `Σ^q(R^m; k)` for every `q ≤ m − 1`, so `q ≥ m`.
Then `n = p + q ≥ m + 1`, a contradiction. ∎

*Proof of item 2.* Let `χ ≠ 0` and `n ≤ d − 1`. By item 4 and the Lemma with `m = d`,
`[θ|_{R^X}] ∈ Σ^n(R^X; k)`. By (F3), `[θ] ∈ Σ^n(W; k)`, so `[χ] ∈ Σ^n(R; k)`.
The statement about `N` is (F4). ∎

## 4. Item 3: L²-Betti numbers

Use Lück, *L²-Invariants* (2002), Theorem 6.54, for arbitrary countable groups, with
values in `[0, ∞]`. Three parts are needed:

- `b_0^{(2)}(G) = 0` for infinite `G`;
- `b_j^{(2)}(H) = [G : H] b_j^{(2)}(G)` for `H` of finite index;
- the Künneth formula `b_j^{(2)}(G × H) = Σ_{i+l=j} b_i^{(2)}(G) b_l^{(2)}(H)`, with
  `0 · ∞ = 0`.

**Claim.** `b_j^{(2)}(R^m) = 0` for `j ≤ m − 1`.

*Proof.* Induct on `m`. For `m = 1`, `b_0^{(2)}(R) = 0` because `R` is infinite. For the
step, expand `R^{m+1} = R × R^m` by Künneth, with `j ≤ m`. A term with `i = 0` contains the
factor `b_0^{(2)}(R) = 0`. A term with `i ≥ 1` has `l ≤ m − 1`, so it contains the factor
`b_l^{(2)}(R^m) = 0`. Both products vanish, by the convention `0 · ∞ = 0`. ∎

With `m = d`, finite index and `ψ` give `b_j^{(2)}(R) = b_j^{(2)}(R^X)/|P| = 0` for
`j ≤ d − 1`.

**Deficiency.** Let `Y` be the presentation complex of a finite presentation
`⟨S | Q⟩` of a group `G`. Then

`1 − |S| + |Q| = χ(Y) = b_0^{(2)}(Ỹ) − b_1^{(2)}(Ỹ) + b_2^{(2)}(Ỹ)`.

Here `b_0^{(2)}(Ỹ) = b_0^{(2)}(G)`. Also `b_1^{(2)}(Ỹ) = b_1^{(2)}(G)`, because `Ỹ` is
simply connected, so it is the 2-skeleton of a model of `EG`. And `b_2^{(2)}(Ỹ) ≥ 0`.
So `|S| − |Q| ≤ 1 − b_0^{(2)}(G) + b_1^{(2)}(G)`. For `G = R` and for every finite-index
subgroup of `R`, both `b_0^{(2)}` and `b_1^{(2)}` vanish, so the deficiency is at most `1`.
For `d ≥ 3`, `b_2^{(2)}(R) = 0` as well. So neither of the two `L²` necessary conditions
for finite presentation fails: `b_1^{(2)}` and `b_2^{(2)}` are both finite. ∎

## 5. The dead Bieri--Strebel argument, precisely

Bieri--Strebel (cited): if `G` is finitely presented and `χ : G ↠ ℤ`, then `G` is an HNN
extension `B ∗_{A, t}` with `B` finitely generated and `χ(B) = 0`. If `G` has no
non-abelian free subgroup, then `A = B` or `tAt^{-1} = B`. So `ker χ` is an ascending
union of conjugates of `B`, in the direction `t` or `t^{-1}`.

An obstruction would have to show that neither ascending description exists. That is
equivalent to `±χ ∉ Σ¹`. By item 1, both ascending descriptions exist, and even
`ker χ` itself is finitely generated. The argument therefore stops at its last step, for
every finitely generated `R ≅ R ≀_X P`.
