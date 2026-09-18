# Referee report (gq-referee-a, proof-gap lens): Kazhdan subgroups of almost-V hosts, and normal germ extensions of V

**Reviewed** (lane bh-kazhdan-inputs), read on origin/main:
- `kazhdan-subgroups-of-almost-v-have-no-central-v-elements`, with route `kazhdan-almost-v-central-v-elements-proof`
  (933586f43);
- its corollary `deligne-lattice-in-almost-v-sits-in-one-germ-group`, with route `deligne-lattice-almost-v-germ-group-proof`;
- `normal-germ-extensions-of-v-have-only-finite-kazhdan-subgroups`, with route `normal-germ-extensions-finite-kazhdan-proof`
  (e8f4766f4).

**Verdict: PASS for all three.** There is one nit.
- For the citation lens:
  - the revealing-pair facts (BBGLGHMS);
  - Margulis's normal subgroup theorem;
  - Minkowski;
  - the Haagerup property of `V`;
  - (T) for `Aut(F_n)`;
  - Lemmas 2 and 4 of the `SL_3(Z)` proof, a cited node.

## 1. The central-V lemma
- **The local form.**
  - A cone `cone(u) ∋ a` is mapped by `w^q` by a prefix replacement `u ↦ u'`, where `u'` is a prefix of `a`.
  - Equal lengths make `a` non-attracting, and so does a shorter `u'`, which expands. So `u'` extends `u`: `u' = ue`.
  - From `ua' = uea'` we get `a' = ea'`, so `a = ue^∞`. ✓
- **The basin and fundamental domain (the author asked about this).**
  - `{n : w'^n x ∈ N}` is nonempty and upward closed, because `w'(N) ⊆ N`. It is bounded below unless `x ∈ ⋂ w'^k(N) = {a}`.
  - The orbit of `x` meets `D` exactly once: a second hit would lie in `w'(N)`, which is disjoint from `D`.
  - Each `w'^n(D)` is compact open, so `π` is continuous.
  - `B = {x : w'^n x → a}`, so `γ` preserves it. ✓
- **`ψ` is a homomorphism.** It uses `π(γw'^jy) = π(γy)`, and `ψ(γ^(−1))` is its inverse. ✓
- **`sing(γ)` is `w`-invariant (the author asked about this).**
  - `w ∈ V` gives `sing(wγw^(−1)) = w(sing γ)`, and `wγw^(−1) = γ`. So `sing(γ)` is a finite `w`-invariant set of
    `w`-periodic points.
  - A `w'`-periodic point of `B` converges to `a`, so it equals `a`. So `γ` is V-local on `B ∖ {a}`. ✓
- **`ψ` lands in `V` after extension by the identity (the author asked about this).**
  - On `D`, `ψ(γ)` is locally `w'^(−n)∘γ`, which is V-local.
  - `D` is clopen, so the extension by the identity is V-local everywhere, hence lies in `V` by compactness.
  - (T) plus Haagerup makes `ψ(Λ_1)` finite. ✓
- **The translation-number homomorphism (the author asked about this).**
  - `n_γ` is defined because `w'` acts freely on `B ∖ {a}`.
  - It is locally constant, as the preimage of the clopen `w'^n(D)`, and `w'`-invariant.
  - It is additive: `n_(γδ)(x) = n_γ(δx) + n_δ(x) = n_γ(x) + n_δ(x)`.
  - (T) makes the image in the torsion-free `C(D,Z)` finite, hence trivial. ✓
- **Item 2.**
  - `k^(−1)Λk ≤ H`.
  - `w'^m` lies in the finite-index subgroup `Λ_2`, which fixes `B`. But `w'^m` moves every point of `B ∖ {a}`, which is
    nonempty because a Cantor set has no isolated points (N1). ✓

## 2. The Deligne corollary
- **The dichotomy.**
  - If `p(N)` is finite, it lies in the torsion-free `Γ(3)`, so `N ≤ ker p ∩ Γ_1 = Z_1`.
  - Otherwise `Γ_1/N` is an extension of a finite group by the cyclic `Z_1N/N`, so it is virtually cyclic. With (T) it
    is finite. ✓
- **Injectivity.**
  - A finite-index `ker φ` would put an infinite Kazhdan group in `V`, which is impossible. So `ker φ ≤ Z_0`, which is
    central and lies in `hVh^(−1)`.
  - The lemma then makes `ker φ` torsion, so `ker φ = 1`. ✓
- **One coordinate.**
  - Every nontrivial `K_y` meets `Z_0` in a finite-index subgroup, whether `K_y` has finite index or lies in `Z_0`.
  - Finitely many such subgroups have nontrivial intersection, which contradicts `⋂K_y = 1`. ✓
- **Singularity.** The non-singular germ groups are trivial or cyclic, and `Γ_0` is nonabelian. The finite-presentation
  item follows through SingFix. ✓

## 3. Normal germ extensions have only finite Kazhdan subgroups
- **Step 1.**
  - At non-singular points, `(G)_p = (V)_p` is trivial or `Z` by Lemma 2, so it is abelian.
  - In case (a), `(G)_p` is virtually cyclic.
  - In case (b), Lemma 4's map `ψ_p : (G)_p → V(D)` has abelian kernel. Its Kazhdan image in `V` is finite, and the
    finite-index abelian Kazhdan part `K ∩ A_p` is finite.
  - So `K` is finite in every case. ✓
- **Step 2.**
  - The FW germ reduction applies, since `G ≤ H`.
  - By Step 1, each `φ_y(Λ_0)` is finite, whether or not `y` is singular. So `ker φ` has finite index, and it is a
    Kazhdan subgroup of `hVh^(−1)`, hence finite. So `Λ` is finite. ✓
- **The consequences and scope.**
  - They follow from (T) of the listed groups, and `Out(F_5)` inherits (T) as a quotient of `Aut(F_5)`.
  - Aperiodic points in case (b) are correctly left uncovered.

## Nit
- **N1 (central-V, item 2).** Note that `B ∖ {a} ≠ ∅` because `B` is open and `C` has no isolated points.
