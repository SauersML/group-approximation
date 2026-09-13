---
rg: 2
id: ascending-hnn-fp-n-bounds-base-homology-alexander-rank-proof
kind: route
title: Colimit homology, Shapiro's lemma over k[t,t^-1] and the Wang sequences of the finite-index subgroups bound the base homology of an FP_n ascending HNN extension
target: ascending-hnn-fp-n-bounds-base-homology-alexander-rank
requires: []
---

Notation as in the target.

**Step 0 (`FP_n` over `Z` implies `FP_n` over `k`).** Let `P_* → Z` be a
projective `ZH`-resolution with `P_0, …, P_n` finitely generated. It is a
resolution by free abelian groups of the free abelian group `Z`, so it is split
exact over `Z` and stays exact after `⊗_Z k`. So `P_* ⊗_Z k → k` is a projective
`kH`-resolution, finitely generated in degrees `≤ n`.

**Step 1 (the kernel is a colimit).** The relators of `H` have `χ`-value 0, so
`χ` is well defined and onto, and `N` is normal with `H/N ≅ Z`. Put
`G_m = t^(−m) G t^m`. Since `t G t^(−1) = σ(G) ≤ G`, we have
`G ≤ t^(−1) G t`, hence `G_m ≤ G_(m+1)`. Every element of `H` is equal to one of
the form `t^(−p) g t^q` with `g ∈ G` and `p, q ≥ 0`: move negative powers of `t`
left and positive powers right using `g t^(−1) = t^(−1) σ(g)` and
`t g = σ(g) t`. It lies in `N` iff `p = q`, so `N = ∪_m G_m`. The isomorphism
`G → G_m`, `g ↦ t^(−m) g t^m`, carries `σ` to the inclusion `G_m ≤ G_(m+1)`,
because `t^(−m) g t^m = t^(−(m+1)) σ(g) t^(m+1)`. So `N ≅ colim(G, σ)`. Group
homology commutes with directed colimits, so
`H_j(N; k) ≅ colim(V_j, s)`. Let `φ_m: V_j → H_j(N; k)` be the canonical map
from the `m`-th stage, and `τ` the automorphism of `H_j(N; k)` induced by
conjugation by `t`. Conjugation by `t` maps `G_(m+1)` onto `G_m` compatibly
with the identifications, so `τ φ_(m+1) = φ_m`. With `φ_m = φ_(m+1) s` this gives
`φ_0 s = τ φ_0`.

**Step 2 (item 1).** By Shapiro's lemma
`H_j(N; k) ≅ H_j(H; k[H/N]) = H_j(H; k[t, t^(−1)])`, compatibly with `τ` acting
as multiplication by `t^(±1)`. Compute the right side with
`Q_* = P_* ⊗_Z k ⊗_(kH) k[H/N]`. For `i ≤ n`, `Q_i` is a finitely generated
projective module over the Noetherian ring `R = k[t, t^(−1)]`. So
`H_j(Q_*) = ker(d_j) / im(d_(j+1))` is a quotient of a submodule of the finitely
generated `Q_j`, hence finitely generated, for all `j ≤ n`.

**Step 3 (item 2).** `R` is a principal ideal domain, so `M = H_j(N; k)` is
`R^r ⊕ (torsion)` with `r < ∞`. Put `V' = φ_0(V_j)`. Its kernel is
`ker φ_0 = T_j`, since a class dies in a directed colimit iff it dies at some
stage, i.e. `s^m v = 0` for some `m`. So `V_j/T_j ≅ V'` as `k[s]`-modules, with
`s` acting on `V'` as `τ`. Every element of `M` is `φ_m(v) = τ^(−m) φ_0(v)`
for some `m`, so `M = ∪_m τ^(−m) V'`. Localization at the multiplicative set
`{s^m}` is exact, so `V' ⊗_(k[s]) k[s, s^(−1)] ≅ ∪_m τ^(−m) V' = M`. Tensoring
with `k(s) = k(t)` gives `dim_(k(s)) V' ⊗ k(s) = dim_(k(t)) M ⊗_R k(t) = r`.

**Step 4 (item 3).** Let `H_m = χ^(−1)(mZ)`, of index `m` in `H` and hence of
type `FP_n` over `k`. Then `H_m = N ⋊ < t^m >`, and `N = ∪_i G_(mi)` is also the
colimit of `(G, σ^m)`, a cofinal subsystem. So `H_m ≅ G *_(σ^m)` with stable
letter `t^m`, by the normal form of Step 1 applied to `σ^m`. The Bass–Serre tree
of this HNN extension gives the Mayer–Vietoris (Wang) sequence
`⋯ → H_j(G; k) --(1 − s^m)--> H_j(G; k) → H_j(H_m; k) → H_(j−1)(G; k) --(1 − s^m)--> H_(j−1)(G; k) → ⋯`.
The two edge inclusions `G → G` are the identity and `σ^m`; conjugation by the
stable letter acts trivially on `H_*(H_m; k)`. Type `FP_n` over `k` gives
`dim H_j(H_m; k) < ∞` for `j ≤ n`: compute with `P_* ⊗_Z k ⊗_(kH_m) k`. The
sequence puts `coker(1 − s^m | V_j)` inside `H_j(H_m; k)`, and
`ker(1 − s^m | V_(j−1))` is a quotient of `H_j(H_m; k)`. Both are therefore
finite-dimensional.

**Calibration.** For `BS(1,2) = Z *_(×2)` over `F_2`, `s = 0` on `V_1 = F_2`.
The rank is 0, `1 − s = 1` has zero cokernel, and `BS(1,2)` is of type `F`, as
required. For a non-example, let `G` be free of infinite rank on `x_0, x_1, …` with
`σ(x_i) = x_(i+2)`. Then `V_1/T_1 = V_1` has infinite rank over `F_2[s]` (the
even and odd generators each give a free orbit, and so does every finite set of
generators), and indeed `G` is not finitely generated. So the lemma's
hypothesis `FP_1` over `k` must fail here, and it does: `G *_σ` is not
finitely generated.
