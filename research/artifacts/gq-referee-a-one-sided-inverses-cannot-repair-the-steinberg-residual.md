# Referee report (gq-referee-a, proof-gap lens): one-sided inverses cannot repair the Steinberg residual

**Reviewed:** `one-sided-inverses-cannot-repair-the-steinberg-residual` (lane gq-k2-q, 0b9dedd64), read on
origin/main. The proof is inline in the claim node, and there is no separate `-proof` route.

**Verdict: PASS.** Parts 1–3 hold, and I found no gap. There are two nits.

## Checks
- **Part 1: `Γ_N(T)` depends only on `T/I_rf` (the author asked about this).**
  - `steinberg-rf-forces-ring-rf` (`N ≥ 3`) says that a surjection `ρ` onto a finite group factors through
    `St_N(T/J)`, where `J = {r : ρ(x_12(r)) = 1}` has finite index. So `J ⊇ I_rf(T) ⊇ I`.
  - Hence every finite-index normal subgroup contains `K = ker(St_N(T) → St_N(T/I))`, and that map is onto. So
    finite-index normal subgroups correspond, `St_N(T)_rf` is the preimage of `St_N(T/I)_rf`, and
    `Γ_N(T) ≅ Γ_N(T/I)`. ✓
- **Part 1: the kernel of `St_N(T) → St_N(T/I)` (the author asked about this).**
  - Adding the relations `x_ij(a) = 1` for `a ∈ I` makes `x_ij(r)` depend only on `r mod I`. So the quotient
    satisfies the universal property of `St_N(T/I)`, and the kernel is `⟨⟨x_ij(a) : a ∈ I⟩⟩`.
  - Take `a = Σ t g t'` and `k ∉ {i,j}`. Such a `k` exists for `N = 3` as well: it is the third index.
  - Then `x_kj(g t') = [x_ki(g), x_ij(t')]`, with `k, i, j` distinct, lies in `⟨⟨x_ki(g)⟩⟩`.
  - And `x_ij(t g t') = [x_ik(t), x_kj(g t')]` lies in the same normal subgroup.
  - So `x_ij(a)` lies in the normal closure of the finitely many `x_ab(g_t)`, `a ≠ b`. ✓
  - The node says "the `x_ij(g_t)`". The proof uses them for all pairs `(a,b)`. A single pair also suffices (N1).
- **Part 2: the Dedekind-finite step (the author asked about this).**
  - In a finite quotient `F`, `f ↦ π̄f` is injective because `γ̄π̄ = 1`, hence bijective. So `π̄g = 1` for some `g`.
  - Then `γ̄ = γ̄π̄g = g`, and `π̄γ̄ = 1`.
  - So `1 − πγ` lies in every finite-index two-sided ideal. ✓
- **Part 3: the use of Part 2 (the author asked about this).**
  - `x^k(1 − π_0γ_0)x^(−k) = 1 − π_kγ_k`, so every `1 − π_kγ_k` lies in `I = (1 − π_0γ_0)`.
  - `γ_kπ_k = x^kγ_0π_0x^(−k) = 1` already holds. So in `T'` the `γ_k` are two-sided inverses.
  - `I ⊆ I_rf(T)` because `I_rf(T)` is a two-sided ideal containing `1 − π_0γ_0`. Part 1 applies. ✓
  - *Finite normal generation.* Let `p` be the surjection, with `ker p` finitely normally generated.
    - Then `p^(−1)(⟨⟨y_1..y_r⟩⟩) = ⟨⟨ỹ_1..ỹ_r, generators of ker p⟩⟩`.
    - Also `p(St_N(T)_rf) = St_N(T')_rf`, since `p` is onto and `St_N(T)_rf` is a full preimage.
    - So the equivalence holds. ✓
  - The right-inverse version is the mirror image.

## Nits
- **N1 (Part 1).** Say "the `x_ab(g_t)` for all `a ≠ b`", or note that one pair suffices. Conjugation by
  `w_ab(1) = x_ab(1)x_ba(−1)x_ab(1)` permutes the index pairs up to sign, so `⟨⟨x_12(g_t)⟩⟩` contains every
  `x_ab(g_t)`.
- **N2 (Part 3, the last sentence).** "`T'` again contains commuting units `π_k`, which is the situation of
  `euler-ring-steinberg-rf-residual-is-fng`" is exact only when `T` is presented by the `D`-relations with `B`
  replaced by the one-sided inverse `γ_0`. Then `T' ≅ D`. Say so. Otherwise `T'` merely receives a map from `D`, or
  maps to it.
