---
rg: 2
id: fpbs-cs-barrier-hypothesis-fails-normal-cyclic-proof
kind: route
title: Two core elements in one coset of a normal cyclic subgroup collide at length two, so nested barriers cannot reach the fibre line
target: fpbs-cs-barrier-hypothesis-fails-normal-cyclic
requires: []
artifacts:
  - experiments/fpbs-normal-cyclic-barrier-2026-09-17/check_normal_cyclic_barrier.py
  - experiments/fpbs-normal-cyclic-barrier-2026-09-17/output.txt
  - research/artifacts/fpbs-acylindrical-l2-gap-2026-09-16.md
---

This proof is complete and self-contained. It uses only the *statements* of
Choi–Seo's Definitions 2.11 and 2.13 and Theorems 2.9 and 2.17
(arXiv:2508.08932v2, PDF pp. 13–16), quoted verbatim below. It does not use
the truth of either theorem.

**Notation.**
* `|g| = ||g||_S` is word length, `d(g,h) = |g^(-1) h|`, and `B(ρ)` is the
  closed `ρ`-ball about `id`.
* `N_ρ(X) = {g : d(g,X) <= ρ} = X·B(ρ)`.
* `Z = <z>` is infinite cyclic and normal, and `c = |z|`.
* For each `t ∈ G`, conjugation by `t` restricts to an automorphism of `Z`,
  so `t z t^(-1) = z^(ε_t)` with `ε_t ∈ {+1,-1}`.

## Quoted statements (verbatim from the PDF text)

> **Definition 2.11.** Let G be a group with a finite generating set S. For
> subsets A,B,C ⊆ G, we say that B is a dS-barrier between A and C if every
> dS-path (g0,g1,...,gn)⊆G starting at A (i.e., g0∈A) and ending at C (i.e.,
> gn∈C) intersects B (i.e., ∃i[gi∈B]).

> **Definition 2.13.** Let G be a group with a finite generating set S. We say
> that a set B⊆G is r-roughly branching if there exists a subset B′⊆G such
> that: (1) B is contained in the r-neighborhood of B′ in the word metric dS.
> (2) For every k≥1, if g1,...,gk and h1,...,hk are distinct sequences of
> elements of B′, then g1···gk ≠ h1···hk.

> **Theorem 2.17.** Let Γ = Cay(G,S) be the Cayley graph of a finitely
> generated group G. Suppose that there exists r>0, and for each D,E>0 there
> exist S_D = ⊔_{i=1}^∞ S_{D;i} ⊆ G, G_{D,E} ⊆ G and a collection H_D of
> subsets of G such that (1) S_D is r′-roughly branching for some r′ = r′_D,
> (2) for each H∈H_D there exists an r-roughly branching subset
> B = B1⊔...⊔BD ⊆ G such that Bi is a dS-barrier between id and H for
> i = 1,...,D; (3) for each D,E>0, ⊔_{i≥E} S_{D;i} is a dS-barrier between id
> and G_{D,E}. Suppose that for each ϵ>0 and D,E>0, there exists a constant
> N = N(ϵ,D,E) such that for every finite set A⊆G there exists A′⊆A
> satisfying: (1) #A′ ≥ (1−ϵ)#A; (2) For each a∈A′ there exist H1,H2∈H_D such
> that #(A \ a·(H1∪H2∪G_{D,E})) ≤ N. Then Equation 2.8 holds for Γ.

> **Theorem 2.9.** Let Γ = Cay(G,S) be the Cayley graph of a finitely
> generated group G. Let H = {H(g) : g ∈ G} be a collection of subsets of G.
> Suppose that there exists R > 0 such that the following holds: For each
> finite set A⊆G there exists A′⊆A with #A′ ≥ #A/2 such that for each a∈A′,
> there exists g,h ∈ G such that ∥g∥S,∥h∥S ≤ R, A⊆aH(g) and H(g)∩hH(g) = ∅.
> Then Equation 2.7 holds for Γ.

The TeX labels and the line numbers of the displays (2.7) and (2.8) are
recorded in `research/artifacts/fpbs-acylindrical-l2-gap-2026-09-16.md` (CS3,
CS4, CS6).

## Step 1. Core lemma (part C)

**Lemma 1.** Let `B'` satisfy Definition 2.13(2), and let `t ∈ G`. Then
`#(B' ∩ Z t) <= 1`.

*Proof.* Suppose `g_1 = z^m t` and `g_2 = z^n t` are distinct elements of
`B'`, so `m ≠ n`. Since `t z^k = z^(ε_t k) t`,

```text
g_1 g_2 = z^(m + ε_t n) t^2,   g_2 g_1 = z^(n + ε_t m) t^2,
g_1 g_1 = z^((1+ε_t) m) t^2,   g_2 g_2 = z^((1+ε_t) n) t^2.
```

* If `ε_t = +1`, then `g_1 g_2 = g_2 g_1`. The sequences `(g_1,g_2)` and
  `(g_2,g_1)` are distinct and have the same product.
* If `ε_t = -1`, then `g_1 g_1 = t^2 = g_2 g_2`. The sequences `(g_1,g_1)` and
  `(g_2,g_2)` are distinct and have the same product.

Either way Definition 2.13(2) fails at `k = 2`. ∎

**Lemma 2.** If `B` is `r`-roughly branching and `ρ >= 0`, then

```text
#(B ∩ N_ρ(Z)) <= K(r,ρ) := #B(r) · #B(r+ρ).
```

*Proof.* Let `B'` be as in Definition 2.13. Take `b ∈ B ∩ N_ρ(Z)`, so
`b = z^m u` with `|u| <= ρ`. Pick `b' ∈ B'` with `d(b,b') <= r`, so
`b' = b v` with `|v| <= r`. Then `b' = z^m (uv) ∈ Z t` with
`t = uv ∈ B(r+ρ)`.

There are at most `#B(r+ρ)` cosets `Z t` with `t ∈ B(r+ρ)`. By Lemma 1 each
contains at most one point of `B'`. So at most `#B(r+ρ)` points of `B'` arise
this way. Each `b'` lies within `r` of at most `#B(r)` points `b`. ∎

**Lemma 3 (fibre paths).** For every `n ∈ Z` there is a `d_S`-path from `id`
to `z^n` inside `N_c(Z)`.

*Proof.* Let `z = s_1 ⋯ s_c` be a geodesic word. The path
`id, s_1, s_1 s_2, …, z, z s_1, …, z^2, …, z^n` has vertices
`z^j s_1 ⋯ s_i` with `i <= c`, each within `c` of `z^j`. For `n < 0`, use the
word `s_c^(-1) ⋯ s_1^(-1)`. ∎

## Step 2. Part (A): the hypothesis of Theorem 2.17 fails

Suppose `r` and families `S_D`, `G_(D,E)`, `H_D` satisfy conditions (1)–(3)
of Theorem 2.17. We show that the magic-lemma condition fails.

**(2a) No `H ∈ H_D` meets `Z` once `D > K(r,c)`.** Let `H ∈ H_D` and suppose
`z^n ∈ H`. Condition (2) gives an `r`-roughly branching
`B = B_1 ⊔ … ⊔ B_D` in which every `B_i` is a barrier between `id` and `H`.
The fibre path `P` of Lemma 3 from `id` to `z^n` starts at `id` and ends in
`H`, so it meets every `B_i`. The `B_i` are disjoint and `P ⊆ N_c(Z)`, so
`#(B ∩ N_c(Z)) >= D`. Lemma 2 gives `D <= K(r,c)`. The bound `K(r,c)` does
not depend on `D`, because `r` is fixed before `D` in Theorem 2.17.

**(2b) `G_(D,E)` misses `Z` once `E` is large, for each fixed `D`.** By
condition (1) and Lemma 2, `S_D ∩ N_c(Z)` is finite, with at most
`K(r'_D, c)` points. The pieces `S_(D;i)` are disjoint, so only finitely many
indices `i` have `S_(D;i) ∩ N_c(Z) ≠ ∅`. Let `E_0(D)` exceed all of them.
For `E >= E_0(D)` the tail `T_E = ⊔_(i>=E) S_(D;i)` misses `N_c(Z)`.

If `z^n ∈ G_(D,E)`, the fibre path to `z^n` lies in `N_c(Z)` and must meet
`T_E` by condition (3). That is impossible. So `G_(D,E) ∩ Z = ∅`.

**(2c) Contradiction.** Take `ε = 1/2`, `D > K(r,c)` and `E >= E_0(D)`, and
let `N = N(1/2, D, E)`. Put `A = {z^0, z^1, …, z^N}`, so `#A = N+1`.

For any `a = z^j ∈ A` and any `H_1, H_2 ∈ H_D`, we have `a^(-1) A ⊆ Z`. By
(2a) and (2b), `Z ∩ (H_1 ∪ H_2 ∪ G_(D,E)) = ∅`. Hence

```text
#(A \ a (H_1 ∪ H_2 ∪ G_(D,E))) = #(a^(-1)A \ (H_1 ∪ H_2 ∪ G_(D,E))) = N + 1 > N.
```

So no point of `A` can lie in `A'`, but `#A' >= (1/2) #A > 0`. The hypothesis
of Theorem 2.17 fails. ∎(A)

The argument never uses condition (1) of the magic lemma beyond `A' ≠ ∅`.
Even the weaker "some `a ∈ A`" version fails.

## Step 3. Part (B): the hypothesis of Theorem 2.9 fails

**(3a) The necessary condition.** This is Step 1 of
`fpbs-cs-set-family-hypothesis-fails-infinite-centre-proof`, repeated here.
Suppose `A ⊆ a H(g)` and `H(g) ∩ h H(g) = ∅`. Then `a^(-1) A ⊆ H(g)` and
`h a^(-1) A ⊆ h H(g)`, so `a^(-1) A ∩ h a^(-1) A = ∅`. Equivalently
`A ∩ (a h a^(-1)) A = ∅`, that is, `a h a^(-1) ∉ A A^(-1)`.

**(3b) The witness.** Fix `R`, let `L = 2 #B(R)`, and put

```text
A = Λ ∪ z^L B(R) ∪ z^(-L) B(R),   where Λ = {z^j : |j| <= L}.
```

Take `h ∈ B(R)` and `i ∈ [-L, L]`. Since `z^L h`, `z^(-L) h` and `z^i` all
lie in `A`,

```text
(z^L h)(z^i)^(-1) = z^(L - ε_h i) h,    (z^(-L) h)(z^i)^(-1) = z^(-L - ε_h i) h.
```

As `i` ranges over `[-L, L]`, the exponents cover `[0, 2L]` and `[-2L, 0]`.
So `z^μ h ∈ A A^(-1)` for all `|μ| <= 2L` and all `h ∈ B(R)`.

For `a = z^j ∈ Λ` and `h ∈ B(R)`,

```text
a h a^(-1) = z^j (h z^(-j) h^(-1)) h = z^((1 - ε_h) j) h ∈ {h, z^(2j) h} ⊆ A A^(-1).
```

By (3a) no point of `Λ` admits a pair `(g,h)`, so
`A' ⊆ z^L B(R) ∪ z^(-L) B(R)` and `#A' <= 2 #B(R)`. On the other hand
`#A >= #Λ = 2L + 1 = 4 #B(R) + 1`, so `#A/2 > 2 #B(R) >= #A'`. This
contradicts `#A' >= #A/2`, for every family `{H(g)}` and every `R`. ∎(B)

## Remarks

**R1 (virtually cyclic normal subgroups).** Suppose `V` is an infinite
virtually cyclic normal subgroup of `G`. Then `G` has an infinite cyclic normal
subgroup, so (A) and (B) apply.

*Proof.*
1. Let `F` be the largest finite normal subgroup of `V`. It is
   characteristic, and `V/F` is `Z` or `D_infinity`.
2. Let `V_1` be the preimage of the translation subgroup of `V/F`. It is
   characteristic, since the infinite cyclic subgroup of index 2 in
   `D_infinity` is unique.
3. Let `W = V_1 ∩ C_V(F)`. It is characteristic of finite index in `V`, so it
   is infinite.
4. `F' = F ∩ W` is finite and central in `W`, and `W/F' ≅ Z`. So
   `W = F' × <w>` for any lift `w` of a generator.
5. With `n = #F'`, the subgroup generated by the `n`-th powers of `W` is
   `<w^n>`. It is characteristic in `W`.
6. A characteristic subgroup of a characteristic subgroup of a normal
   subgroup is normal. So `<w^n>` is normal in `G`. ∎

**R2 (the counting form, for extensions).** Let `Y ⊆ G` be finite and put
`n = #(B' ∩ Y)`. The `n^k` sequences from `B' ∩ Y` have distinct products in
`Y^k`, so

```text
#(B' ∩ Y) <= lim_k (#Y^k)^(1/k).
```

Lemma 1 is the case where `Y` is a window of `Z t` and the growth is linear.
To extend (A) to a normal subgroup `K` that is not virtually cyclic, one needs
tubes `N_ρ(K)` whose windows have product growth rate below 2, together with
fibre paths as in Lemma 3. For `Z^2 ⋊_φ F_2` with `φ` hyperbolic,
`(Ft)^k = (F + φ_t F + … + φ_t^(k-1) F) t^k` is a twisted sumset. The
`k = 2` collision of Lemma 1 is not available, and whether its growth rate
is below 2 is not decided here.

**R3 (calibration).** In `F_2`, the set `{a^m b : m ∈ Z}` is 0-roughly
branching, since its products are distinct reduced words. It meets the 1-tube
of the non-normal subgroup `<a>` infinitely often. So normality in Lemma 1 is
essential. The script checks this for `|m| <= 3` and `k <= 3`. It also checks
that the same shape `{z^m b}` in `F_2 x Z` collides at `k = 2`.

**Machine check.**
`experiments/fpbs-normal-cyclic-barrier-2026-09-17/check_normal_cyclic_barrier.py`
(output in `output.txt`) checks three groups, `F_2 x Z`, `Z ⋊ F_2` (with `a`
inverting `z`) and `F_2 x D_infinity`, each with a standard and a skewed
generating set.
* Lemma 1 is checked exhaustively on windows `|m| <= 6` of every coset `Z t`
  with `|t| <= 2`.
* R3 is checked as described above.
* The (3b) witness is checked by brute force for `R = 1, 2`.