---
rg: 2
id: braid-haagerup-iff-proper-on-noncentral-normal-subgroup-proof
kind: route
title: Conjugation bounds move properness from a normal subgroup to the whole group, up to centralizers
target: braid-haagerup-iff-proper-on-noncentral-normal-subgroup
requires: []
---

Standing notation. Every cnd function `ψ` on a group `G` has the form `ψ(g) = ‖b(g)‖²` for a cocycle
`b(gh) = b(g) + π(g) b(h)` of an orthogonal representation `π` (Schoenberg / Delorme–Guichardet). So:

- `√ψ(gh) ≤ √ψ(g) + √ψ(h)`;
- `ψ(g^{-1}) = ψ(g)`;
- sums of cnd functions are cnd, and `|χ|²` is cnd for every homomorphism `χ: G → R`.

## Lemma 1 (conjugation lemma)

Let `N ⊴ G` and let `ψ` be cnd on `G` with `ψ|_N` proper. Fix `R ≥ 0` and set `S_R = {g ∈ G : ψ(g) ≤ R}`.

1. For every `x ∈ N`, `S_R` lies in finitely many left cosets of the centralizer `C_G(x)`.
2. For every finite set `x_1, …, x_k ∈ N`, `S_R` lies in finitely many left cosets of `C = ∩_i C_G(x_i)`.

*Proof.*

1. For `g ∈ S_R`, `gxg^{-1} ∈ N`, and `√ψ(gxg^{-1}) ≤ √ψ(g) + √ψ(x) + √ψ(g^{-1}) ≤ 2√R + √ψ(x)`. Since `ψ|_N` is
   proper, `{gxg^{-1} : g ∈ S_R}` is a finite set `{y_1, …, y_m}`. If `gxg^{-1} = g'xg'^{-1}`, then
   `g^{-1}g' ∈ C_G(x)`. So `S_R ⊂ g_1 C_G(x) ∪ … ∪ g_m C_G(x)`.
2. Intersect the covers from part 1. A nonempty intersection `g C_G(x_1) ∩ g' C_G(x_2)` is a left coset of
   `C_G(x_1) ∩ C_G(x_2)`. Induct on `k`. ∎

## Lemma 2 (two elements with central joint centralizer)

Let `n ≥ 3` and `N ⊴ P_n` with `N ⊄ Z(P_n)`. Then there are `x_1, x_2 ∈ N` with
`C_{P_n}(x_1) ∩ C_{P_n}(x_2) = Z(P_n)`.

*Proof.* Let `q: P_n → M = PMod(S_{0,n+1})`. It is surjective with kernel `Z(P_n) = ⟨Δ²⟩`
(`pure-braid-group-is-center-times-sphere-pure-mcg`, or Farb–Margalit, *Primer*, §9.3). `M` is torsion-free: it
is an iterated extension of free groups by the Birman exact sequence. `q(N)` is a nontrivial normal subgroup of
`M`, so it is infinite.

It suffices to find `u_1, u_2 ∈ q(N)` with `C_M(u_1) ∩ C_M(u_2) = 1`. For then, if `x_i ∈ N` lifts `u_i`,
`q(C_{P_n}(x_1) ∩ C_{P_n}(x_2)) ⊂ C_M(u_1) ∩ C_M(u_2) = 1`, so the intersection lies in `ker q = Z(P_n)`. It
also contains `Z(P_n)`.

- **Case `n = 3`.** `M = PMod(S_{0,4}) ≅ F_2` is free. A nontrivial normal subgroup of a non-abelian free
  group is not cyclic, and a non-cyclic subgroup of a free group is non-abelian. So `q(N)` contains elements
  `u_1, u_2` that do not commute. If `1 ≠ h ∈ C(u_1) ∩ C(u_2)`, then `u_1, u_2 ∈ C(h)`, which is cyclic, so
  `u_1` and `u_2` commute. This is a contradiction.
- **Case `n ≥ 4`.** A normal subgroup of `M` that is infinite contains a pseudo-Anosov element `β`. Apply Ivanov's theory to
  `H = q(N) ∩ Γ`, where `Γ ⊴ M` is a finite-index normal subgroup of pure mapping classes (Ivanov, 1992, Thm 1.2
  and Cor. 1.8). `H` is normal in `M`, pure, and infinite, since it has finite index in `q(N)`.
  Its canonical reduction system `σ(H)` satisfies `σ(gHg^{-1}) = gσ(H)`, so it is an `M`-invariant multicurve.
  Since `M` contains pseudo-Anosov elements, `σ(H) = ∅`. An infinite pure subgroup with empty canonical reduction
  system contains a pseudo-Anosov element (Ivanov, *Subgroups of Teichmüller modular groups*, 1992, Ch. 7;
  Birman–Lubotzky–McCarthy 1983; cited, not re-verified).
  - For a pseudo-Anosov `β`, let `E(β) = {g ∈ M : gβ^p g^{-1} = β^{±p}` for some `p ≠ 0}`. This is a virtually
    cyclic subgroup containing `C_M(β)` (McCarthy, *Normalizers and centralizers of pseudo-Anosov mapping
    classes*, 1982). `M` is not virtually cyclic, since it contains `F_2` for `n ≥ 4`, so pick
    `g ∉ E(β)` and put `u_1 = β`, `u_2 = gβg^{-1} ∈ q(N)`.
  - Suppose `1 ≠ h ∈ C_M(u_1) ∩ C_M(u_2)`. Then `h` has infinite order. `C_M(u_1)` is virtually cyclic and
    contains `⟨β⟩`, and `⟨β⟩` has finite index in it, so `h^a = β^b` with `a, b ≠ 0`. Likewise `h^c = (gβg^{-1})^d = gβ^d g^{-1}` with `c, d ≠ 0`.
    Hence `β^{bc} = h^{ac} = gβ^{ad}g^{-1}`.
  - Stretch factors are conjugation invariant and `λ(β^p) = λ(β)^{|p|}` with `λ(β) > 1`, so `|bc| = |ad|`.
    Then `gβ^{ad}g^{-1} = β^{±ad}`, so `g ∈ E(β)`. This is a contradiction. ∎

## Theorem

Let `n ≥ 3` and `N ⊴ P_n` with `N ⊄ Z(P_n)`. Then `B_n` has the Haagerup property iff `P_n` admits a cnd
function whose restriction to `N` is proper.

*Proof.*

(⇒) Restrict a proper cnd function on `B_n` to `P_n`.

(⇐) Let `ψ` be cnd on `P_n` with `ψ|_N` proper. By Lemmas 1 and 2, each `S_R` lies in finitely many cosets
`g_1 Z, …, g_m Z` of `Z = ⟨Δ²⟩`. Let `e: P_n → Z` be the exponent sum. Each generator `A_{ij}` has `e = 2`, and
`e(Δ²) = n(n−1) ≠ 0`. Put `ψ' = ψ + e²`, which is cnd.

If `ψ'(g) ≤ R`, then `g ∈ S_R`, so `g = g_i Δ^{2t}` with `|e(g_i) + n(n−1)t| ≤ √R`. That leaves finitely many
`t` for each `i`, so `ψ'` is proper on `P_n`. `P_n` has index `n!` in `B_n`, and the Haagerup property passes to
finite-index overgroups (induction of cnd functions; (H3) of
`research/artifacts/zp-braid-haagerup-reductions-2026-09-13-part1.md`). ∎

## Corollary (obstruction)

Let `ψ` be cnd on `P_n` for some `n ≥ 3`. Suppose `ψ` is bounded on a subset `T ⊂ P_n` that meets infinitely many
cosets of `Z(P_n)`. Then `ψ|_N` is not proper for any non-central `N ⊴ P_n`.

*Proof.* If `ψ|_N` were proper, `T ⊂ S_R` for some `R` would lie in finitely many `Z`-cosets. ∎

Instances. In each, `T` meets infinitely many `Z`-cosets because `q(T)` is infinite.

- `T = ⟨T_c⟩` for a Dehn twist about an essential curve, when `ψ` comes from an action in which `T_c` has a
  bounded orbit. Example: a monodromy `ρ_α: P_4 → PU(2,1)` in which `ρ_α(T_c)` is elliptic, and any convergent
  weighted sum `Σ w_j ψ_{α_j}` with `sup_m Σ_j w_j ψ_{α_j}(T_c^m) < ∞`.
- `T = ∩_j ker ρ_j`, for any finite family of homomorphisms on whose targets the functions are pulled back, when
  this joint kernel is not central.

The sharper statement recorded earlier on this lane was a necessary condition on monodromy families. It follows
from Lemma 1 with `x ∈ Brun_4` and `T = ⟨T_c⟩`.

## Calibration

- The lemma fails without Lemma 2, as it should. For `G = F_2 × F_2` and `N = F_2 × 1`, a cnd function
  pulled back from the first factor is proper on `N` but not on `G`. Here `C_G(N) ⊇ 1 × F_2` is infinite.
- For `Z^2 ⋊ SL_2(Z)` with `N = Z^2`, the joint centralizer of any finite subset of `N` contains `Z^2`, so
  Lemma 1 gives nothing. This is consistent with Burger's relative property (T).
