---
rg: 2
id: rover-nekrashevych-higher-sigma-full-via-kernel-brown
kind: route
title: Brown's criterion for the kernel of the full character map acting on the tall part of the Stein--Farley complex
target: rover-nekrashevych-higher-sigma-invariants-are-full
requires:
  - rover-nekrashevych-stein-farley-complex-properties
  - characters-living-on-m-plus-one-factors-lie-in-sigma-m
  - rover-nekrashevych-characters-are-sum-invariant
---

Properties (a)–(d) are those of `rover-nekrashevych-stein-farley-complex-properties`.

**Standard inputs, used at statement level (theorem numbers not re-read).**

- (BR) Bieri–Renz: let `Γ` be of type `F_m` and `N ⊴ Γ` with `Γ/N` abelian. Then `N` has type `F_m` iff
  `S(Γ, N) ⊆ Σ^m(Γ)`.
- (Br) Brown's criterion (Brown 1987): a group acting on a contractible complex has type `F_m` if every cell
  stabilizer has type `F_m` and the complex has an essentially `(m-1)`-connected filtration by cocompact subcomplexes.
- (ML) The Morse lemma. Adjacent vertices of `X` have different heights, so coning off links changes connectivity
  only as the links allow.

**Setup.** `G` has type `F_m` and `Γ = V_d(G)`. Let `N` be the kernel of `Φ: Γ -> Γ/N ≅ Z^r`, the torsion-free
abelianization. Then `S(Γ, N) = S(Γ)`. By the characters claim, `Φ(V_d) = 0` and `Φ` of a table is the sum of `Φ_G`
of its labels, where `Φ_G: G -> Z^r` is `Φ` on one-cone labels.

**Step 1 (tall part).** Put `n_1 = m + 1`, and let `X_{>= n_1}` be the full subcomplex on heights `>= n_1`. By (c) it
is contractible: its vertex poset is directed, because an upper bound of two tall vertices is tall.

**Step 2 (filtration).** Let `Y_n` be the full subcomplex on heights in `[n_1, n]`. It is `Γ`-cocompact by (a).

- Passing from `Y_n` to `X_{>= n_1}` cones off, at each height `n' > n`, the descending link inside `X_{>= n_1}`.
  That link is the family complex of (d) restricted to at most `⌊(n' - n_1)/(d - 1)⌋` members.
- By (d) this is `(m-1)`-connected for `n' >= n_0`. So for `n >= n_0` the inclusion `Y_n -> X_{>= n_1}` is an
  isomorphism on `π_j` for `j <= m - 1`.
- Hence `Y_n` is `(m-1)`-connected, and the filtration is essentially `(m-1)`-connected.

**Step 3 (the kernel acts cocompactly).** Let `σ` be a cell whose bottom vertex has height `k`.

- By (b), `Stab_Γ(σ)` contains the elements acting by one label `g` on one copy. These are `Γ`-conjugates of `g_(u)`.
- So `Φ(Stab_Γ σ) ⊇ Φ_G(G) = Φ(Γ)`, i.e. `N · Stab_Γ(σ) = Γ`.
- Every `Γ`-orbit of cells is therefore a single `N`-orbit, and each `Y_n` is `N`-cocompact.

**Step 4 (kernel stabilizers).** By (b), conjugating by a table map of the bottom vertex identifies `Stab_Γ(σ)` with a
finite-index subgroup of `Q_k = G^k ⋊ S_k` containing `G^k`.

- On `G^k`, `Φ` becomes `(g_1, ..., g_k) -> Σ_i Φ_G(g_i)`. So `N ∩ Stab_Γ(σ)` contains
  `K_k = ker(Φ_G ⊕ ... ⊕ Φ_G)` with finite index.
- The characters of `G^k` vanishing on `K_k` are `(λ∘Φ_G, ..., λ∘Φ_G)` with `λ != 0` on `Φ(Γ)`. Each component is
  nonzero, since `Φ_G(G) = Φ(Γ)`.
- With `k >= m + 1` and `G` of type `F_m`, `characters-living-on-m-plus-one-factors-lie-in-sigma-m` puts them in
  `Σ^m(G^k)`. By (BR), `K_k` has type `F_m`, and so does `N ∩ Stab_Γ(σ)`.

**Step 5 (conclusion).**

- (Br) with the stabilizers `Stab_Γ(σ)` (finite index over `G^k`, type `F_m`) shows `Γ` has type `F_m`.
- (Br) with the stabilizers of Step 4 shows `N` has type `F_m`.
- (BR) then gives `S(Γ) = S(Γ, N) ⊆ Σ^m(Γ)`. ∎

**Remarks.**

- For finitely generated abelian `G`, `K_k` is free abelian, so the second requirement is automatic.
- The same argument with `m = 1` recovers `rover-nekrashevych-groups-have-full-bns-invariant` only under the extra
  input (d). The direct proof there needs none.
- Nothing here uses property (d) beyond connectivity growing with height. The bound is independent of `G`: the labels
  enter only through stabilizers.
