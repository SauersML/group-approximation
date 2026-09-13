---
rg: 2
id: lampshuffler-groups-are-not-fp2-over-q-proof
kind: route
title: An escaping pair of transpositions gives a t-invariant coinvariant class in a product of group algebras
target: lampshuffler-groups-are-not-fp2-over-q
requires: []
artifacts:
  - research/artifacts/zp-lampshuffler-not-fp2-2026-09-13.md
---

Direct proof; the full write-up with every verification is
`research/artifacts/zp-lampshuffler-not-fp2-2026-09-13.md`. Notation: `X` is a free
`G`-set with finitely many orbits, `K = FSym(X)`, `E = K x| G`, `φ : G -> Z` is onto,
`Δ = ker φ`, `t in G` with `φ(t) = 1`, `N = K x| Δ`, so `E/N = Z`. Modules are left
`Q[E]`-modules, `e_F = |F|^(-1) sum_(f in F) f` for a finite `F <= K`, and
`M_H = M / I_H M`.

**Step 1 (Bieri-Eckmann).** If `E` is of type `FP_2` over `Q` then
`H_1(E; prod_I Q[E]) = 0` for every `I`. Take a partial free resolution with `P_0, P_1,
P_2` finitely generated; `P (x) prod_I Q[E] = prod_I (P (x) Q[E])` for finitely
generated free `P`, products are exact, and `Q[E]` is free, so
`H_1(E; prod_I Q[E]) = prod_I H_1(E; Q[E]) = 0`.

**Step 2 (locally finite kernels).** For locally finite `K` and any module `M`,
`I_K M = { m : e_F m = 0 for some finite F <= K }`. If `e_F m = 0` then
`m = (1 - e_F) m` and `1 - e_F in I_F`. Conversely if `m = sum_(i<=r) (k_i - 1) m_i`,
then `F = <k_1, ..., k_r>` is finite and `e_F (k_i - 1) = 0`, so `e_F m = 0`. (This is
Step 1 of `fp2-over-q-descends-along-locally-finite-kernels`, reproved here so that this
route stands alone.)

**Step 3 (five-term).** The Lyndon-Hochschild-Serre sequence of `1 -> N -> E -> Z -> 1`
ends `H_1(E; M) -> H_1(Z; M_N) -> 0`, and `H_1(Z; A) = ker(t - 1 : A -> A)` by the
resolution `0 -> Q[Z] --(t-1)--> Q[Z] -> Q -> 0`. So it suffices to find `y` in
`M = prod_I Q[E]` with `(t-1) y in I_N M` and `y not in I_N M`.

**Step 4 (the element).** Pick `x_0 ≠ z` in `X`, let `s = (x_0 z)` and
`s_n = t^(-n) s t^n`. Freeness of the action and the infinite order of `t` make
`x_0, z, t^(-n)x_0, t^(-n)z` pairwise distinct for `n >= n_0`. Take `I = {n >= n_0}`,
`a_n = (1-s)(1-s_n)` and `y_n = (1 + t + ... + t^(n-1)) a_n`.

**Step 5 (`(t-1)y` dies).** `(t-1) y_n = (t^n - 1) a_n`. With the one subgroup
`F = <s>`: `e_F a_n = 0` because `e_F (1-s) = 0`; and
`e_F t^n a_n = t^n e_(<s_n>) a_n = t^n (1-s) e_(<s_n>)(1 - s_n) = 0`, using
`γ e_(γ^(-1) F γ) = e_F γ`, `t^(-n) s t^n = s_n`, and that `s, s_n` commute. So
`e_F (t-1) y = 0`, and `(t-1) y in I_K M ⊆ I_N M` by Step 2.

**Step 6 (`y` survives).** Coinvariants in stages give `M_N = (M_K)_Δ`, so `y in I_N M`
means `y = u + sum_(j<=m) (δ_j - 1) z_j` with `u in I_K M` and finitely many
`δ_j in Δ`. By Step 2 there is a finite `B ⊆ X` with `e_(Sym(B)) u = 0`. Put
`Δ_0 = <δ_1, ..., δ_m>` and `H = <Sym(B), Δ_0> = P x| Δ_0` with
`P = <Sym(δB) : δ in Δ_0> <= FSym(Δ_0 B)`, so `H ∩ K = P` and every element of `H` has
`G`-part in `Δ_0 ⊆ Δ`. Any `λ : E -> Q` constant on right cosets `H g` gives a
functional `Λ(x) = sum_g λ(Hg) x_g` which kills each `(δ_j - 1) z_j` and satisfies
`Λ(x) = Λ(e_(Sym(B)) x)`, hence kills `u` coordinatewise. So `Λ(y_n) = 0` for all `n`
and all such `λ`: the image of `y_n` in `Q[H \ E]` vanishes.

But `y_n = sum_(i=0)^(n-1) (1 - u_i - v_i + u_i v_i) t^i` with
`u_i = (t^i x_0, t^i z)` and `v_i = (t^(i-n) x_0, t^(i-n) z)`. Terms with different `i`
lie in different `H`-cosets, since the `G`-part `t^(j-i)` of the comparison element must
lie in `Δ_0 ⊆ ker φ`. At a level `i` with `t^i x_0` and `t^(i-n) x_0` outside `Δ_0 B`,
the elements `u_i, v_i, u_i v_i` are supported outside `Δ_0 B`, hence outside `P`, so
the four cosets at that level are distinct. Freeness bounds the number of bad levels:
`t^i x_0 in Δ_0 b` forces `t^i x_0 = δ b` with `δ in Δ`, so `i = φ(γ_b) - φ(γ_0)` is
determined by `b`; at most `|B|` values of `i` for each of the two conditions. Taking
`n > 2|B| + 1` gives a good level `i`, where the coefficient of `[H t^i]` in the image
of `y_n` is `1`. Choosing `λ` to be the indicator of `H t^i` contradicts `Λ(y_n) = 0`.

**Conclusion.** `[y]` is a nonzero `t`-invariant element of `M_N`, so
`H_1(Z; M_N) ≠ 0`, so `H_1(E; prod_I Q[E]) ≠ 0` by Step 3, so `E` is not of type `FP_2`
over `Q` by Step 1. Passing to a finite-index subgroup that surjects onto `Z` (which
preserves `FP_2` and keeps `X` free with finitely many orbits) gives the virtually
indicable form; `FP_2` over `Z` implies `FP_2` over `Q` by tensoring a partial resolution
with `Q`, and finite presentation implies `FP_2` over `Z`. ∎
