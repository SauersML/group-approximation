---
rg: 2
id: free-centre-by-metabelian-corner-kernel-is-the-torsion
kind: claim
title: The (2n+1)x(2n+1) corner representation of F_n/[F_n'',F_n] over Z[Z^n] has kernel exactly the torsion subgroup, which is 0 for n <= 3 and (Z/d)^C(n,4) for n >= 4
distinct_from:
  free-centre-by-metabelian-linear-modulo-exterior-square-kernel: that constructs the representation and bounds its kernel K_n (rank <= C(n,3)+C(n,4)); this computes K_n exactly, proving K_3 = 0 and K_n = torsion.
  free-centre-by-metabelian-groups-are-linear: that proves every C_n linear, adding a nilpotent quotient that sees the torsion; this is the corner representation alone, faithful exactly for n <= 3.
---

**ESTABLISHED** (lane proof, inline; not independently reviewed). The one outside input
is `gupta-torsion-element-survives-modulo-gamma-seven`, used only in Step 4.

**Priority.** No novelty is claimed.
- C. K. Gupta (J. Austral. Math. Soc. 16, 1973; abstract) represents `C_n/H_n` by 3x3
  matrices for `n >= 4`, with `H_n` finite elementary abelian.
- Kuz'min (1977) identifies the torsion with `H_4(F/F') ⊗ Z/2` (per Kovács–Stöhr and a
  2023 Comm. Algebra abstract; not read).
- Gupta's Remark 2 (as cited by Kofinas, arXiv:2603.27648 §2.3) gives `F_3''/[F_3'',F_3]`
  free abelian.

This node gives a self-contained computation with an explicit representation.

## Statement

- **Notation.** `F = F(x_1..x_n)`, `G = Z^n`, `R = Z[G]`, `t_i = x_i − 1`, `C_n = F/[F'',F]`.
- **Representation.** `ρ_n: F -> GL_(2n+1)(R)`, with block sizes `n, 1, n`:
  `x_i ↦ [[I_n, e_i, 0], [0, x_i, e_i^T], [0, 0, I_n]]`.
- **Kernel.** Write `K_n = ker(ρ_n)/[F'',F] ⊆ C_n` and `T_n` for the torsion subgroup of `C_n`.

Then:
1. `ρ_n` factors through `C_n`, and `K_n = T_n`.
2. `T_2 = T_3 = 0`. So `C_2` and `C_3` are faithfully represented, in `GL_5` and `GL_7` of
   `Z[x_i^(±1)]`.
3. For `n >= 4`, `T_n ≅ (Z/d)^C(n,4)` for one even `d >= 2` (by Kuz'min, `d = 2`). For
   each 4-subset `S`, let `r_S: C_n -> C_S ≅ C_4` be the retraction that kills the other
   generators. Then `(r_S)_S: T_n -> ⊕_S T_4` is an isomorphism. `T_4` is cyclic, and its
   unique involution is Gupta's element `u_6` (`T_4 = ⟨u_6⟩` if `d = 2`).

## Proof

**Step 0 (the centre as coinvariants).**
- `M := F'/F''` is identified by Fox calculus (Magnus) with `ker(d_1: P -> R)`, where
  `P = R^n` and `d_1 e_j = t_j`. Its image is the augmentation ideal `I`.
- `F'` is free, so `F''/[F'',F'] ≅ Λ²_Z M`, and conjugation acts diagonally. Hence
  `F''/[F'', F] ≅ (Λ²M)_G`.
- As in `free-centre-by-metabelian-linear-modulo-exterior-square-kernel`:
  - the block entries of `ρ_n(w)` are `g(w)`, the Fox vector `b(w)`, `α(w)` and a corner
    `n×n` matrix;
  - `ker ρ_n ⊆ F''`;
  - on `F''` the corner is `Φ ∘ (b ∧ b)` with `Φ` injective on `(Λ²P)_G`.

  So `K_n = ker((Λ²M)_G -> (Λ²P)_G)`. The image of `ρ_n` is torsion-free: if `g^m = 1`
  then `g = 1`, and the unipotent part has entries in the torsion-free group `R`. So
  `T_n ⊆ K_n`.

**Step 1 (skew-hermitian model).** Let `¯` be the involution of `R` inverting monomials,
and for column vectors let `S(u, v) = ū v^T − v̄ u^T`.
- The map `u ∧ v ↦ S(u, v)` identifies `(Λ²R^k)_G` with `Sk_k`, the skew-hermitian
  `k×k` matrices over `R`. There is no extra condition on the diagonal: every skew
  element of `Z[G]` is `λ − λ̄`, because `G` is torsion-free.
- On each orbit basis vector `[f_i ∧ h f_j]`, the map is the matrix with `h` at `(i,j)`
  and `−h^(−1)` at `(j,i)`. These have disjoint supports, so it is injective.
- A linear map `D: R^k -> R^l` induces `X ↦ D̄ X D^T`.

**Step 2 (K_3 = 0).** For `n = 3`, let `D: N = R^3 -> P` be `Du = u × t`, with columns
`m_23, m_31, m_12`, where `m_jk = t_j e_k − t_k e_j`. By Koszul exactness (`t` is a
regular sequence) and because the `t_j` are pairwise coprime in the UFD `R`:
- `D(N) = M` and `ker D = R t`;
- so `(Λ²M)_G = Sk_3 / W`, with `W = {S(t, v) : v ∈ R^3}`;
- and `K_3 = {X ∈ Sk_3 : D̄ X D = 0} / W`.

Let `X` lie in the kernel.
- **Columns of `XD` lie on `t̄`.** Each column of `XD` is killed by `D̄ = (· × t̄)`, so it
  lies in `R t̄`, as `gcd(t̄_j) = 1`.
- **Reduce mod `t̄`.** The columns `X_i` then satisfy `t_i X_j ≡ t_j X_i` in
  `N' = R^3/R t̄`. That is a Koszul 1-cocycle.
- **The cocycle is a coboundary.** `H^1(t; N') ≅ H_2(t; N') = H_2(G; N') = 0`, from
  `0 -> R -> R^3 -> N' -> 0`. So `X = β t^T + t̄ μ^T` with `β, μ ∈ R^3`.
- **Skew-hermitian condition.** `X* = −X` gives `t̄ a^T + ā t^T = 0` with `a = β̄ + μ`.
  Hence `a = c t` with `c ∈ R` and `c̄ = −c`, so `c = λ − λ̄`.
- **Conclusion.** `X = S(t, −β̄ + λ t) ∈ W`. So `K_3 = 0`. (`K_2 = 0` was proved in
  `free-centre-by-metabelian-rank-two-linearity-proof`.)

**Step 3 (structure for all n).** Put `Q = Λ²P/Λ²M`. Then:
- `Λ²P` is `ZG`-free, because `G` acts freely on unordered pairs of basis vectors. So
  `K_n ≅ H_1(G; Q)`.
- There is an equivariant exact sequence `0 -> M⊗I -> Q -> Λ²I -> 0`, and dimension
  shifting gives:
  - `H_1(M⊗I) ≅ H_2(M) ≅ H_4(G)`;
  - `H_2(Λ²I) ≅ H_4(G)`;
  - `H_1(Λ²I) ≅ H_3(G)`.

  So we get the exact sequence
  `Λ^4 Z^n --δ--> Λ^4 Z^n -> K_n -> Λ^3 Z^n`.

  Everything is natural in maps of free groups sending basis elements to basis elements
  or to 1.
- **The `Λ^3` part vanishes.** For a 3-subset `S`, the retraction induces the coordinate
  projection `p_S` on `Λ^3`, and it factors through `K_S = K_3 = 0`. So the image of
  `K_n` in `Λ^3` is killed by every `p_S`, hence is 0.
- **`δ` is a scalar.** For a 4-subset `S`, naturality under the inclusion `F_S -> F_n` and
  the retraction `F_n -> F_S` gives `δ(e_S) = d e_S`. Here `d` is the rank-4 constant.
- **Conclusion.** `K_n ≅ (Z/d)^C(n,4)`, and the retraction maps are the coordinates.

**Step 4 (d).** By `gupta-torsion-element-survives-modulo-gamma-seven`, `u_6 ∈ C_4` has
order 2. By Step 0 it lies in `T_4 ⊆ K_4 = Z/d`. So `d` is even, in particular `d ≠ 0`.
Then:
- `K_n` is finite, so `K_n ⊆ T_n`, and `K_n = T_n`;
- `T_4` is cyclic of even order, with unique involution `u_6`. ∎

## Consequence

`C_n/T_n` is linear in characteristic zero for every `n`, and `C_2`, `C_3` are linear.
For every `n`, see `free-centre-by-metabelian-groups-are-linear`.
