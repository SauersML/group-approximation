---
rg: 2
id: euler-lamplighter-automorphisms-admit-no-fp-sandwich
kind: claim
title: The base M of the Euler lamplighter G_l is its Fitting subgroup, Aut(G_l) is the soluble group Z^1(H,M) ⋊ (Z_(l)^× × ⟨x, δ⟩) with δ the Pochhammer automorphism, and by Bieri–Strebel no finitely presented subgroup of Aut(G_l) contains Inn(G_l); so G_l is dead as an Aut-sandwich candidate for (SL)
distinct_from:
  separable-subgroups-are-z-semilocal-root-closed: that reformulates (SL) as a finitely presented P with Inn(G) ≤ P ≤ Aut(G) and names G_l as the live candidate; this computes Aut(G_l) completely and kills that candidate.
  z-localized-embeds-in-fg-rf-soluble-group: that builds G_l and proves it is residually finite; this determines its automorphism group.
---

## Proposed dependency record (not an accepted route)

The following rejected claim-level metadata is preserved verbatim as a
proposed dependency record. It is not a compiled route, does not establish
this claim, and requires individual mathematical review before any route
is accepted. The historical mathematical prose below is unchanged.

```yaml
requires:
  - separable-subgroups-are-z-semilocal-root-closed
  - z-localized-embeds-in-fg-rf-soluble-group
  - z-semilocalized-embeds-in-fp-rf-group
```

**ESTABLISHED** (lane proof; bh-invent-12, 2026-09-19; elementary, plus two recalled theorems of Bieri–Strebel;
not independently reviewed; no priority claimed). It settles the question posed in
`separable-subgroups-are-z-semilocal-root-closed`: there is no automorphism of `G_l` moving `M`, and the
Aut-sandwich over `G_l` does not exist.

## Setting

Notation is that of `z-localized-embeds-in-fg-rf-soluble-group`:
- `M = Z_(l)[y^±]` with basis `f_j = y^j`, `x f_j = f_(j−1)` and `β f_j = (1 + lj) f_j`;
- `β_k = x^(−k) β x^k = diag(1 + l(j − k))`, and `A = ⊕_k ⟨β_k⟩`;
- `H = ⟨x, β⟩ = A ⋊ ⟨x⟩ ≅ Z ≀ Z`, and `G_l = M ⋊ H`.

`H` acts faithfully on `M`. For finitely supported `e ∈ Z^(Z)` put `R_e(j) = ∏_k (1 + l(j − k))^(e_k)`, so
that `A = {diag(R_e(j))_j}`. The **Pochhammer automorphism** is `δ = diag(c_j)`, with `c_j / c_(j−1) = 1 + lj`
and `c_0 = 1`. It satisfies `δ β δ^(−1) = β` and `δ^(−1) x δ = x β`.

## Theorem

1. **`M` is characteristic.** `M` is the Fitting subgroup of `G_l`.
2. **The normalizer.** In `GL_(Z_(l))(M)`, `N(H) = Z_(l)^× × Γ`, where the scalars `Z_(l)^×` are central and
   `Γ = ⟨x, δ⟩ = (A × ⟨δ⟩) ⋊ ⟨x⟩`, with `β = x^(−1) δ^(−1) x δ`.
3. **The automorphism group.** Restriction to `M` gives an exact sequence
   `1 -> Z^1(H, M) -> Aut(G_l) -> N(H) -> 1`, whose kernel is the abelian group of crossed homomorphisms. So
   `Aut(G_l)` is soluble of derived length at most 4.
4. **No sandwich.** No finitely presented subgroup `P ≤ Aut(G_l)` contains `Inn(G_l)`. More generally, no finitely
   presented subgroup of `Aut(G_l)` has an image in `Γ` containing `H`.

## Proof

**1.**
- `M` is abelian and normal. Let `g = (m, h)` lie in the Fitting subgroup. Then `g` lies in a nilpotent normal
  subgroup `N ⊇ M` of some class `c` (Fitting's theorem).
- Iterated commutators `[m', g, …, g]` of length `c + 1` vanish, so `(h^(−1) − 1)^c = 0` on `M`.
- **`h` has no shift.** Write `h = x^r a` with `a ∈ A`. If `r ≠ 0`, then `(h − 1)^c f_0` has a nonzero term in
  degree `−cr`, whose coefficient is a product of units. So `r = 0`.
- **`h` is trivial.** Then `a = diag(R_e(j))` is unipotent, so `R_e(j) = 1` for all `j`. The factors
  `1 + l(j − k)` are distinct linear polynomials, so `e = 0`.
- **Conclusion.** `g ∈ M`, so the Fitting subgroup is `M`.

**2.**
- **`s` is monomial.** Let `s ∈ N(H)`. Conjugation by `s` is an automorphism of `H`, so it preserves its Fitting
  subgroup `A` (proved as in 1). The characters `a ↦ a_j` of `A` on `Q f_j` are pairwise distinct, since the
  entries `1 + lj` of `β` are. So `s` permutes the lines `Q f_j`: `s f_j = u_j f_(σ(j))` with `σ` a bijection and
  `u_j ∈ Z_(l)^×`.
- **`s` shifts by a constant.** `s β s^(−1) = diag_i(1 + l σ^(−1)(i)) ∈ A`, so `R_e(i) = 1 + l σ^(−1)(i)` for all
  `i`.
  - A rational function taking integer values at all integers is a polynomial.
  - A polynomial bijection `Z -> 1 + lZ` has degree 1: degree `d >= 2` hits only `O(N^(1/d))` values in `[−N, N]`.
  - So `R_e` is a polynomial of degree 1 without poles, i.e. `R_e = 1 + l(i − k)` for one `k`. Then
    `σ(j) = j + k`, and `s = x^(−k) D` with `D` diagonal.
- **Which diagonals normalize.** `D x D^(−1) = x · diag(u_(j−1) / u_j)`. Elements of `H` of shift 1 are `x a`
  with `a ∈ A`, so `D ∈ N(H)` iff the ratio `ρ(D) = diag(u_(j−1) / u_j)` lies in `A`.
- **The diagonal part.** `ρ` is a homomorphism onto `A` with kernel the scalars. `ρ(β_k) = β_(k+1) β_k^(−1)` and
  `ρ(δ) = β_0^(−1)`, and these generate `A`. So the diagonal part of `N(H)` is `Z_(l)^× · A · ⟨δ⟩`.
- **The product is direct.** Augmentation shows `Z_(l)^× ∩ A⟨δ⟩ = 1`: `ρ(A)` has augmentation `0` and `ρ(δ)` has
  augmentation `−1`. So `N(H) = Z_(l)^× × Γ`.

**3.**
- **Restriction lands in `N(H)`.** By 1, every `α ∈ Aut(G_l)` preserves `M`. Also `α(h)` acts on `M` as
  `α|_M h α|_M^(−1)`, and this lies in `H`. So `α|_M ∈ N(H)`.
- **Surjective.** Each `s ∈ N(H)` is realized by conjugation by `s` inside `M ⋊ GL(M)`.
- **The kernel.** If `α|_M = id`, faithfulness gives `α(h) = d(h) h` with `d ∈ Z^1(H, M)`, and
  `α_d α_(d') = α_(d + d')`.
- **Derived length.** `Z^1`, `Z_(l)^×` and `A × ⟨δ⟩` are abelian, and `Γ / (A × ⟨δ⟩) ≅ Z`. That gives length at
  most 4.

**4.**
- **Setup.** Let `P ≤ Aut(G_l)` be finitely presented, and let `π : P -> Γ` be the composite of the map to
  `N(H)` with the projection onto `Γ`.
  - If `Inn(G_l) ≤ P`, then `π(P) ⊇ H`, because inner automorphisms by `h ∈ H` map to `h`.
  - `H` is normal in `Γ` with `Γ / H ≅ ⟨δ⟩`. So `Q := π(P) = A ⟨δ^n⟩ ⋊ ⟨x⟩` for some `n >= 0`.
  - Let `χ : Γ -> Z` be the `x`-exponent. `χ π` maps `P` onto `Z`.
- **Bieri–Strebel.** `P` is finitely presented, so `P` is an HNN extension `⟨B, t | t^(−1) C t = D⟩` with `B`
  finitely generated in `ker χπ`, `C, D ≤ B` finitely generated, and `χπ(t) = 1` (Bieri–Strebel 1978, recalled).
  `P` is soluble by 3, so it has no free subgroup of rank 2. Hence `C = B` or `D = B` (Britton's lemma), and
  `ker χπ = ⋃_(k>=0) t^(±k) B t^(∓k)` for one sign.
- **Push forward.** `π` is onto `Q`, so `K := ker χ|_Q = ⋃_(k>=0) τ^(±k) B' τ^(∓k)`, with `τ = π(t)` and
  `B' = π(B)` finitely generated. Now `K = A × ⟨δ^n⟩` is abelian and `τ ∈ x K`, so conjugation by `τ` on `K` is
  conjugation by `x`.
- **Coordinates.** Write `K ≅ Z[t^±] ⊕ Z` (or `Z[t^±]` when `n = 0`), with `t^k ↔ β_k` and `1 ↔ δ^n`.
  Conjugation by `x^(−1)` is `φ(a, m) = (t a − n m, m)`, using `x^(−1) δ^n x = δ^n β_0^(−n)`.
  - The `a`-supports of `⋃_(k>=0) φ^k(B')` are bounded below.
  - Those of `⋃_(k>=0) φ^(−k)(B')` are bounded above.
- **Contradiction.** Neither union is `K`. ∎

## Where the Aut-sandwich went wrong, and what survives

- **The mechanism of the kill.** The sandwich forces a finitely presented soluble group to map onto an overgroup
  `A⟨δ^n⟩ ⋊ ⟨x⟩` of `Z ≀ Z` in which the base is not finitely generated over either half of `⟨x⟩`. By
  Bieri–Strebel, a finitely presented group without free subgroups never has such a quotient. This is the BNS
  statement `Σ^1 ∪ −Σ^1 = S` for finitely presented groups without `F_2`, which passes to quotients.
- **A general filter for Aut-sandwiches.** If `Aut(G)` has no `F_2`, then every subgroup of `Aut(G)` is
  `F_2`-free. So a finitely presented `P ⊇ Inn(G)` needs `Σ^1 ∪ −Σ^1 = S` on every quotient of `P`, in particular on
  the image of `P` in `Aut(G)/Z^1`. Soluble candidates `G` must have automorphism groups whose images contain
  tame overgroups of `G/M`. The `A`-with-`δ` structure of `G_l` is forced by its spectrum (item 2), and it is not
  tame.
- **What survives for (SL).** Finitely presented overgroups of `G_l` outside `Aut(G_l)`. They must realize a tame
  overgroup of `Z ≀ Z` (like Baumslag's `⟨a, s, t⟩`) acting on a module extending `M`. The Baumslag letter cannot
  act on `M` itself (parity, `separable-subgroups-are-z-semilocal-root-closed`). So the module must be enlarged:
  this is the characteristic-0 KMS problem, now with the spectral constraint that `M` sits inside a
  non-diagonalizable, or non-simple-spectrum, module. Hosts containing `F_2` escape the filter entirely.

## Lesson for general BH

**Automorphism groups inherit the input's shape, and Bieri–Strebel then decides finite presentation.**
- Simple spectrum rigidifies. `M` is the Fitting subgroup, every automorphism is monomial with a constant shift,
  and `Aut(G_l)` is soluble. That makes the whole Aut-sandwich a question about `Σ^1` of one metabelian group
  `Γ = ⟨x, δ⟩`.
- `Γ` is untame in the `x` direction, so no finitely presented group without free subgroups maps onto a subgroup
  of `Γ` containing `Z ≀ Z`.
- **General moral.** Sandwiching a soluble input between its inner and its full automorphism group cannot create
  finite presentation: it reproduces the input's own `Σ^1` defect. An (SL) witness over an Euler-type module must
  change the module (non-simple spectrum), or leave the soluble world (contain `F_2`).
