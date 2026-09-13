# Lampshuffler groups are not of type FP_2 (lane z1-25-lampshuffler-fp2, 2026-09-13)

Full proof of `lampshuffler-groups-are-not-fp2-over-q`, written for Zaremsky Problems 1.25 and 1.20:
the lampshuffler route to faithful `[HA_2]` actors is dead.

## 0. Statement

**Theorem A.** Let `Γ` be a group with a surjection `φ : Γ → Z`, let `X` be a set on which `Γ` acts
freely with finitely many orbits, let `K = FSym(X)` be the group of finitely supported permutations
of `X`, and let `G = K ⋊ Γ`. Then `G` is **not** of type `FP_2` over `Q`.

**Corollary B.** If `Γ` is finitely generated and virtually indicable (some finite-index subgroup
surjects onto `Z`) and `X` is a free `Γ`-set with finitely many orbits, then `FSym(X) ⋊ Γ` is not of
type `FP_2` over `Q`, hence not of type `FP_2` over `Z` and not finitely presented.

In particular the **lampshuffler** `Shuffler(Γ) = FSym(Γ) ⋊ Γ` is not `FP_2` for every finitely
generated virtually indicable `Γ`: for `Z^d`, for one-ended right-angled Artin groups and surface
groups, for free groups, and for `G_L(S) × Z` with `G_L(S)` one of Leary's groups — the candidate
the 1.25 lane had proposed.

**Credit.** For `Γ = Z` this is Houghton's group `H_2` and the statement is Brown's (Finiteness
properties of groups, JPAA 44 (1987), `H_n` is of type `F_(n-1)` but not `FP_n`). The proof below is
a generalisation of the repository's own rational proof for `H_2`,
`houghton-h2-not-fp2-over-q-proof` (another lane, unreviewed there), whose averaging-idempotent
mechanism it reuses. Genevois–Tessera, arXiv:2401.13520, Theorem 1.5, already give that lampshuffler
groups over infinite groups are never finitely presented; Theorem A strengthens that to `FP_2` in the
virtually indicable range, and is stated for arbitrary free `Γ`-sets.

## 1. Notation

`X` is a free `Γ`-set with finitely many orbits; `K = FSym(X)`; `G = K ⋊ Γ`; all modules are left
modules over `Q[G]` and all tensor products are over `Q[G]` unless said otherwise. For a subgroup
`F ≤ K` write `e_F = |F|^(-1) Σ_(f in F) f` when `F` is finite, and `I_H` for the augmentation ideal
of `Q[H]`. For a subgroup `H ≤ G` and a module `M`, `M_H = M / I_H M`.

`Δ = ker φ`, and `t in Γ` is any element with `φ(t) = 1`; `t` has infinite order. Set

  `N = K ⋊ Δ`,  so  `N` is normal in `G` and `G/N ≅ Z = <t>`.

`Γ` acts freely on `X`, so for `x in X` the points `t^i x` (`i in Z`) are pairwise distinct.

## 2. Three standard lemmas

**Lemma 1 (Bieri–Eckmann, the direction used).** If `G` is of type `FP_2` over `Q`, then
`H_1(G; Π_I Q[G]) = 0` for every index set `I`.

*Proof.* Take a partial free resolution `P_2 → P_1 → P_0 → Q → 0` with each `P_i` finitely generated
free. For finitely generated free `P` the natural map `P ⊗ Π_I Q[G] → Π_I (P ⊗ Q[G])` is an
isomorphism, because a finite direct sum commutes with products; products of modules are exact; so
`H_1(G; Π_I Q[G]) ≅ Π_I H_1(G; Q[G]) = 0`, the last equality because `Q[G]` is free. ∎

**Lemma 2 (the shape of `I_K M`).** Let `K` be locally finite and `M` any `Q[K]`-module. Then
`I_K M = { m in M : e_F m = 0 for some finite subgroup F ≤ K }`.

*Proof.* If `e_F m = 0` then `m = (1 - e_F) m` and `1 - e_F = |F|^(-1) Σ_(f in F) (1 - f) in I_F`, so
`m in I_K M`. Conversely if `m = Σ_(i=1)^r (k_i - 1) m_i`, put `F = <k_1, ..., k_r>`, a finite
subgroup because `K` is locally finite; then `e_F (k_i - 1) = e_F - e_F = 0`, so `e_F m = 0`. ∎

This is the rational form of "locally finite groups are invisible"; the repository states it as
`fp2-over-q-descends-along-locally-finite-kernels`, whose Step 1 is exactly Lemma 2. The proof above
is self-contained, so nothing here depends on that node.

**Lemma 3 (five-term).** For any `Q[G]`-module `M`, the Lyndon–Hochschild–Serre five-term exact
sequence of `1 → N → G → Z → 1` ends in

  `H_1(G; M) → H_1(Z; M_N) → 0`,  and  `H_1(Z; M_N) = ker( t - 1 : M_N → M_N )`.

*Proof.* The five-term sequence is standard. The identification of `H_1(Z; A)` comes from the free
resolution `0 → Q[Z] --(t-1)--> Q[Z] → Q → 0`. ∎

So: **to prove Theorem A it is enough to exhibit an index set `I` and an element `y` of
`M = Π_I Q[G]` with `(t - 1) y in I_N M` and `y not in I_N M`.**

## 3. The element

Fix `x_0 in X` and `z in X` with `z ≠ x_0`. Let `s = (x_0 z) in K` be that transposition and, for
`n ≥ 1`,

  `s_n = t^(-n) s t^n = (t^(-n) x_0, t^(-n) z)`.

Because the action is free and `t` has infinite order, the four points `x_0, z, t^(-n)x_0, t^(-n)z`
are pairwise distinct for all large `n`; fix `n_0` with this property for `n ≥ n_0`, and let
`I = { n in N : n ≥ n_0 }`. Put

  `a_n = (1 - s)(1 - s_n) in Q[K]`,   `y_n = (Σ_(i=0)^(n-1) t^i) a_n in Q[G]`,   `y = (y_n)_n in M`.

**Step 1: `(t - 1) y in I_K M ⊆ I_N M`.** Coordinatewise `(t - 1) y_n = (t^n - 1) a_n`. Let
`F = <s> = {1, s}`, a subgroup of `K` of order 2, independent of `n`. Then

- `e_F a_n = e_F (1 - s)(1 - s_n) = 0`, since `e_F (1 - s) = (1 + s)(1 - s)/2 = 0`;
- `e_F t^n a_n = t^n e_(t^(-n) F t^n) a_n = t^n e_(<s_n>) a_n = t^n (1 - s) e_(<s_n>)(1 - s_n) = 0`,
  using `γ e_(γ^(-1) F γ) = e_F γ`, that `t^(-n) s t^n = s_n`, and that `s` and `s_n` commute
  (disjoint supports).

So `e_F (t - 1) y = 0` in `M` with the single finite subgroup `F`, and Lemma 2 gives
`(t - 1) y in I_K M`. ∎

## 4. `y` is not in `I_N M`

Coinvariants in stages give `M_N = (M_K)_Δ`, so `y in I_N M` if and only if

  `y = u + Σ_(j=1)^m (δ_j - 1) z_j`  with `u in I_K M`, `m` finite, `δ_j in Δ`, `z_j in M`.   (*)

(The finitely many `δ_j` and the single `u` are the whole content of the argument: they are chosen
before `n` varies, while the coordinates `y_n` escape.)

Assume (*). By Lemma 2 there is a finite subgroup `F' ≤ K` with `e_(F') u = 0`; enlarging, there is a
finite subset `B ⊆ X` with `F' ≤ Sym(B)` and hence `e_(Sym(B)) u = 0`. Put

  `Δ_0 = <δ_1, ..., δ_m> ≤ Δ`,   `H = <Sym(B), Δ_0> ≤ G`.

Because `Δ_0` normalises nothing of `Sym(B)` beyond conjugating it to `Sym(δB)`,

  `H = P ⋊ Δ_0`  with  `P = < Sym(δ B) : δ in Δ_0 > ≤ FSym(Δ_0 B)`,   `H ∩ K = P`,

and every element of `H` has `Γ`-part in `Δ_0 ⊆ Δ`.

**The functional.** Let `λ : G → Q` be any function constant on the right cosets `H g`, and for
`x in Q[G]` put `Λ(x) = Σ_(g in G) λ(H g) x_g` (a finite sum). Then

- `Λ(π x) = Λ(x)` for `π in Sym(B)`, so `Λ(x) = Λ(e_(Sym(B)) x)`; applying this to the `n`-th
  coordinate of `u` gives `Λ(u_n) = 0`;
- `Λ((δ_j - 1) w) = 0` for every `w`, since `H δ_j g = H g`.

Reading (*) in the `n`-th coordinate therefore forces `Λ(y_n) = 0` for every `n` and every such `λ`;
equivalently **the image of `y_n` in `Q[H \ G]` is `0` for every `n`.** We now contradict this.

**The image of `y_n` in `Q[H \ G]`.** Conjugating the transpositions past the translations,

  `y_n = Σ_(i=0)^(n-1) ( 1 - u_i - v_i + u_i v_i ) t^i`,
  `u_i = t^i s t^(-i) = (t^i x_0, t^i z)`,   `v_i = t^i s_n t^(-i) = (t^(i-n) x_0, t^(i-n) z)`.

*(a) Different `i` give different cosets.* If `H σ t^i = H σ' t^j` with `σ, σ' in K`, then
`σ' t^(j-i) σ^(-1) in H`, whose `Γ`-part is `t^(j-i)`; so `t^(j-i) in Δ_0 ⊆ ker φ`, and applying `φ`
gives `j = i`.

*(b) For suitable `i` the four cosets at level `i` are distinct.* Two elements `σ t^i, σ' t^i` lie in
the same coset iff `σ' σ^(-1) in H ∩ K = P ≤ FSym(Δ_0 B)`, and every element of `FSym(Δ_0 B)` is
supported inside `Δ_0 B`. The supports of `u_i`, `v_i` and `u_i v_i` all contain `t^i x_0` or
`t^(i-n) x_0`. So if

  `t^i x_0 not in Δ_0 B`  and  `t^(i-n) x_0 not in Δ_0 B`,        (**)

then `u_i`, `v_i`, `u_i v_i` and also `u_i v_i u_i^(-1) = v_i`, `u_i v_i v_i^(-1) = u_i` all lie
outside `P`, so the four cosets `H t^i`, `H u_i t^i`, `H v_i t^i`, `H u_i v_i t^i` are pairwise
distinct.

*(c) (**) fails for at most `2|B|` values of `i`.* Fix `b in B`. If `t^i x_0 = δ b` for some
`δ in Δ_0`, write `x_0 = γ_0 x_l` and `b = γ_b x_(l')` in terms of orbit representatives. Freeness
forces `l = l'` and `t^i γ_0 = δ γ_b`, hence `δ = t^i γ_0 γ_b^(-1) in Δ = ker φ`, hence
`i = φ(γ_b) - φ(γ_0)`: at most one `i` per `b`. The same count applies to `t^(i-n) x_0 in Δ_0 B`.

*(d) Conclusion.* Take `n > 2|B| + 1` (and `n ≥ n_0`). By (c) some `i in {0, ..., n-1}` satisfies
(**). By (a) and (b) the basis element `[H t^i]` of `Q[H \ G]` receives a contribution only from the
term `1 · t^i` of the sum, so the coefficient of `[H t^i]` in the image of `y_n` is `1 ≠ 0`. Choosing
`λ` to be the indicator function of the coset `H t^i` gives `Λ(y_n) = 1`, contradicting `Λ(y_n) = 0`.

Hence (*) is impossible and `y not in I_N M`. ∎

## 5. Proof of Theorem A and Corollary B

By Step 1 and Section 4 the class of `y` in `M_N` is nonzero and killed by `t - 1`, so
`H_1(Z; M_N) ≠ 0`; by Lemma 3, `H_1(G; Π_I Q[G]) ≠ 0`; by Lemma 1, `G` is not of type `FP_2` over
`Q`. ∎

Corollary B: if `Γ' ≤ Γ` has finite index and surjects onto `Z`, then `FSym(X) ⋊ Γ'` has finite index
in `G` and `X` is a free `Γ'`-set with `[Γ : Γ'] ·` (number of `Γ`-orbits) orbits, so Theorem A applies
to it; type `FP_2` over `Q` passes between a group and its finite-index subgroups. A partial free
resolution over `Z[G]` with finitely generated terms tensors up to one over `Q[G]`, so `FP_2` over `Z`
implies `FP_2` over `Q`, and finite presentability implies `FP_2` over `Z`. ∎

## 6. Model tests and scope

- **`Γ = Z`, `X = Z`:** `G = Shuffler(Z) = H_2`, and Theorem A recovers the known failure of `FP_2`
  (Brown). The element `y` specialises to the one in `houghton-h2-not-fp2-over-q-proof`.
- **Lamplighters.** The argument never uses that `K` is a symmetric group, only that it is locally
  finite and contains a finite subgroup `<s>` whose `t`-conjugates eventually commute with it. With
  `K = ⊕_X Z/2` it reproves that `Z/2 ≀ Γ` is not `FP_2` for virtually indicable `Γ`, which is correct.
- **Finite `Γ`:** the hypothesis fails (no surjection onto `Z`) and indeed `FSym(X) ⋊ Γ` is finite.
- **Trivial action:** if `X` is a point, `K = 1` and `G = Γ` can be `FP_2`; freeness with finitely
  many orbits fails only in the sense that `K` is then trivial, and the element `a_n` does not exist.
- **Houghton `H_3` is finitely presented, and this does not contradict Theorem A.** In `H_n` for
  `n ≥ 3` the acting group `Z^(n-1)` does not act on the `n` rays by permutations at all — only
  "eventually", after a finite correction — so the ray system is not a free `Z^(n-1)`-set with
  finitely many orbits. Freeness is used exactly once, in (c); without it the bad set of `i` can be
  infinite and the argument breaks, as it must.

**Scope.** Theorem A needs a surjection `Γ → Z` (virtually). For `Γ` with finite abelianisation in
every finite-index subgroup — for instance a Kazhdan group — the reduction of Lemma 3 is unavailable
and the `FP_2` status of `FSym(Γ) ⋊ Γ` is left open here. The same element `y` and the same coset
functional are expected to work through any infinite virtually free quotient of `Γ` (`cd_Q ≤ 1` makes
the spectral sequence degenerate in the same way); only the case where `Γ` has no such quotient is
genuinely untouched.

**Novelty (bounded).** WebSearch and arXiv/HTML fetches on 2026-09-13 found no statement in the
literature about `FP_2` for lampshuffler groups: Genevois–Tessera Theorem 1.5 gives non-finite-
presentation, and Brown gives the `H_n` case. No MathSciNet or zbMATH. So this is "not found in the
sources checked", not a verified first.
