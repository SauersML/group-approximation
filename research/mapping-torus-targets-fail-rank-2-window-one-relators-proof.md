---
rg: 2
id: mapping-torus-targets-fail-rank-2-window-one-relators-proof
kind: route
title: Conjugation by the image of t acts on the rational lower central quotients of a finitely generated residually torsion-free nilpotent base by integer matrices, so the relation forces an eigenvalue that is a root of e2 x^2 + e1 x + e0, which is irreducible with non-integral roots unless |e2| = 1
target: mapping-torus-targets-fail-rank-2-window-one-relators
requires:
  - malcev-root-steps-put-commutator-root-one-relators-in-h
  - edge-injective-quotients-give-hughes-free-division-rings
---

## Setting

- `G = <a, t | r>` is one of the 128 length-15 relators of item 2 of
  [[malcev-root-steps-put-commutator-root-one-relators-in-h]] with occurrence pattern `(3, 1, 3)`. Its span-2
  Magnus rewrite is `r' ∈ F(a_0, a_1, a_2)`, `a_i = t^{-i} a t^i`, with exponent vector `e = (e_0, e_1, e_2)`.
- `a_1` occurs once, so `e_1 = ±1`. `a_0` and `a_2` occur three times each, so `e_0, e_2 ∈ {±1, ±3}`.
- `f(x) = e_2 x^2 + e_1 x + e_0 ∈ Z[x]`, and `f*(x) = e_0 x^2 + e_1 x + e_2` is its reverse.
- For a group `B`, `√γ_k B` is the isolator of the `k`-th lower central term: the elements with a nonzero power
  in `γ_k B`.

## Step 0: facts about f

These are checked word by word by `eigen_obstruction.py` (the script aborts if one fails).

- `f(1) = e_0 + e_1 + e_2` is a sum of seven odd terms `±1`, so it is odd and nonzero.
- `f` is primitive, because `e_1 = ±1`.
- The discriminant `1 - 4 e_0 e_2` lies in `{-35, -11, -3, 5, 13, 37}`. None of these is a square, so `f` is
  irreducible over `Q`, and so is `f*`.
- A root `λ` of `f` has minimal polynomial `f / e_2`. So `λ` is an algebraic integer iff `|e_2| = 1`.
- `λ^{-1}` is a root of `f*`. So `λ^{-1}` is an algebraic integer iff `|e_0| = 1`.
- `1` is not a root, because `f(1)` is odd.

## Step 1: a lies in the fibre

Let `π: Q -> Z` be a homomorphism and `φ: G -> Q`. Apply `π ∘ φ` to `r`. The exponent sum of `t` in `r` is `0`
and that of `a` is `f(1)`. So `f(1) · π(φ(a)) = 0`, hence `π(φ(a)) = 0`. Every `φ(a_i)` is a conjugate of
`φ(a)`, so every `φ(a_i)` lies in `ker π`.

## Step 2: the graded relation

Let `B` be a group, `g ∈ B` with `g ≠ 1`, and `θ: B -> B` an endomorphism. Suppose
`r'(g, θ g, θ^2 g) = 1` in `B`, and suppose some `√γ_k B` fails to contain `g` (for example, `B` is residually
torsion-free nilpotent). Take `k` maximal with `g ∈ √γ_k B`.

- `√γ_j B` is a subgroup: it is the preimage of the torsion subgroup of the nilpotent group `B / γ_j B`.
- The `√γ_j B` form a central series, i.e. `[B, √γ_j B] ⊂ √γ_{j+1} B`. This is P. Hall's theorem on isolators,
  applied in the nilpotent group `B / γ_{j+1} B`.
- The factors are torsion-free, because `B / √γ_{j+1} B` is.
- Endomorphisms preserve the series, because they preserve `γ_j` and roots.
- If `B` is residually torsion-free nilpotent, then `∩_j √γ_j B = 1`. Indeed, if `B / K` is torsion-free
  nilpotent of class `c`, then `√γ_{c+1} B ⊂ K`.
- Put `L = (√γ_k B / √γ_{k+1} B) ⊗ Q`. Let `θ_k` be the linear map `θ` induces on `L`, and `ℓ ≠ 0` the class
  of `g`.
- Every letter of `r'(g, θg, θ^2 g)` lies in `√γ_k B`, and `√γ_k / √γ_{k+1}` is abelian. Reading the relation
  modulo `√γ_{k+1} B` gives
  `e_0 ℓ + e_1 θ_k ℓ + e_2 θ_k^2 ℓ = 0`, i.e. `f(θ_k) ℓ = 0`.
- So the minimal polynomial of `θ_k` on the cyclic subspace spanned by `ℓ` divides the irreducible `f`. Since
  `ℓ ≠ 0`, `f` itself is that minimal polynomial, and **every root of `f` is an eigenvalue of `θ_k`**.
- If `θ` is an inner automorphism, then `θ_k = 1`, because the series is central. Then `f(1) ℓ = 0`, which
  contradicts Step 0.

## Item 1: residually torsion-free nilpotent targets

Let `Q` be residually torsion-free nilpotent and `φ: G -> Q` with `φ(a) ≠ 1`. Apply Step 2 with `B = Q`,
`g = φ(a)` and `θ` conjugation by `φ(t)`. Since `θ` is inner, Step 2 gives a contradiction. So `φ(a) = 1`.

## Items 2 and 3: ascending mapping tori

Let `B` be finitely generated and residually torsion-free nilpotent, `ψ: B -> B` an injective endomorphism,
and `Q = <B, s | s^{-1} w s = ψ(w), w ∈ B>`. Let `π: Q -> Z` send `s ↦ 1`. The kernel is
`N_Q = ∪_{j ≥ 0} s^j B s^{-j}`, an increasing union.

Let `φ: G -> Q` with `g = φ(a) ≠ 1`. Write `T = φ(t) = s^m h` with `h ∈ N_Q`.

- By Step 1, `g ∈ N_Q`.
- Conjugating `φ` by a power of `s` (which changes neither `m` nor whether `φ(a) = 1`), we may assume
  `g, h ∈ B`.
- **Case `m = 0`.** `θ = ` conjugation by `h` is inner on `B`, and `θ^i g = φ(a_i)`. Step 2 gives a
  contradiction.
- **Case `m > 0`.** `φ(a_1) = T^{-1} g T = h^{-1} ψ^m(g) h`. So `θ = c_h ∘ ψ^m` is an endomorphism of `B` with
  `θ^i g = φ(a_i)`, and the relation holds in `B`.
  - `B` is finitely generated, so every `√γ_k B / √γ_{k+1} B` is a finitely generated torsion-free abelian group,
    `Z^d`.
  - `θ_k` is an integer matrix, and `θ_k = ψ_k^m` because inner automorphisms act trivially.
  - By Step 2, a root `λ` of `f` is an eigenvalue of an integer matrix, so `λ` is an algebraic integer. By
    Step 0, **`|e_2| = 1`**.
  - If `ψ` is an automorphism, then `θ_k ∈ GL_d(Z)`, so `λ^{-1}` is an algebraic integer too, and
    **`|e_0| = 1`** as well.
- **Case `m < 0`.** Read the relation backwards.
  - Put `g' = φ(a_2)`, `T' = T^{-1}`, and let `r''` be the mirror of `r'` (swap `a_0` and `a_2`). Then
    `r''(g', T'^{-1} g' T', T'^{-2} g' T'^2) = 1`.
  - `r''` has exponent vector `(e_2, e_1, e_0)`, and `T'` has `s`-exponent `-m > 0`.
  - The case `m > 0` applies to `r''`, after conjugating again so that `g'` and the new `h` lie in `B`. It
    gives **`|e_0| = 1`**, and additionally `|e_2| = 1` when `ψ` is an automorphism.

This proves items 2 and 3.

- A word with `|e_0| = |e_2| = 3` admits no homomorphism `φ` with `φ(a) ≠ 1` into any such `Q`.
- A word with exactly one of `|e_0|`, `|e_2|` equal to `1` admits none into `B ⋊ Z`.

## Item 4: why this is fatal for the edge-injective lemma

`G` is the HNN extension of `F(a_0, a_2)` with stable letter `t` along the window `A = <a_0, a_1> ≅ F_2`
(`a_1 = V(a_0, a_2)`). A target of item 1 of [[edge-injective-quotients-give-hughes-free-division-rings]]
must be injective on `A`, in particular `φ(a) ≠ 1`.

- By item 1, `Q` cannot be residually torsion-free nilpotent.
- By items 2 and 3, `Q` cannot be an ascending mapping torus of the excluded kind.

Every map `G -> Z` kills `a`. So the maps to `Z` used by the landed cyclic rules see nothing here either.

## Step 5: the counts

`eigen_obstruction.py w313-L15.txt` classifies the 128 words. Each word has exactly one `(3, 1, 3)` rewrite.

- **KILL: 32 words**, with `|e_0| = |e_2| = 3`.
- **ASC: 64 words**, with exactly one of `|e_0|`, `|e_2|` equal to `1`.
- **UNIT: 32 words**, with `|e_0| = |e_2| = 1`, 8 for each of `x^2 ± x ± 1`.

The output is recorded in `eigen-L15.txt`.
