# Referee report (gq-referee-a, proof-gap lens): FW inputs admit no twisted shell normalization

**Reviewed** (lane gq-typeA-design, 767e0c40b), read on origin/main:
- `fw-inputs-admit-no-twisted-shell-normalization`;
- its route `fw-inputs-admit-no-twisted-shell-normalization-proof`.

**Verdict: PASS.** There are two nits and one overlap note for the coordinator.
- For the citation lens: FW is used only in Step 2, and the implication "(T) ⇒ FW" (Brailovsky–Pasechnik–Praeger) is
  cited.

## Step 1: the commensurated graph
- `g·(x,y) = (ρ_(φ(g))x, ρ_g y)` is an action, because `φ` is an endomorphism.
- `g·Γ` is the graph of `ρ_g s ρ_(φ(g))^(−1)`.
- The hypothesis gives `ρ_g s = s ρ_(φ(g))` off a finite set. Both maps are defined everywhere on `N`, so their graphs
  differ in finitely many points, and `Γ` is commensurated. ✓

## Step 2: invariance of `D`, `E` and `N_1` (the author asked about this)
- `Γ'_(ρ_(φ(g))x) = ρ_g(Γ'_x)` and `Γ'^(ρ_g y) = ρ_(φ(g))(Γ'^y)` both come straight from invariance of `Γ'`.
- So `|Γ'_x|` is `ρ(φ(P))`-invariant and `|Γ'^y|` is `ρ(P)`-invariant. `D` and `E` are finite, because
  `Γ' Δ Γ` is finite and `Γ` has singleton fibres, apart from `Γ^0 = ∅`.
- For `x ∈ N_1`:
  - `ρ_(φ(g))x ∉ D`;
  - its partner is `ρ_g s'(x)`, which lies outside `E` because `E` is `ρ(P)`-invariant.
  So `N_1` is `ρ(φ(P))`-invariant and `s'` is equivariant.
- *Injectivity.* A point outside `E` has exactly one partner.
- *`M_1` and `K`.* `M_1` is `ρ(P)`-invariant, using `g^(−1)` as well. `K = N − M_1` is finite, because `s'` is near
  `s` and `s(N) = N − {0}`. ✓

## Step 3: the predecessor argument (the author asked about this)
- In- and out-degrees are at most 1.
- For `x > n_0`, `s'(x) = x + 1 > n_0 + 1`. So no point `≤ n_0 + 1` has a predecessor above `n_0`, and the backward
  path from `n_0 + 1` stays in `[0, n_0]`.
- `n_0 + 1 ∉ K`, so it has a predecessor.
- The backward path cannot close into a cycle, because its component carries an infinite forward ray and degrees are
  at most 1. So it ends at a point with no predecessor, which is a point of `K`.
- A path from `k ∈ K − {k_0}` cannot meet the main ray: meeting it at `x_i`, `i ≥ 1`, would give `x_i` two
  predecessors, and `k ≠ k_0`. It cannot enter a cycle either.
- So such a path lies in `[0, n_0]` and has fewer than `n_0 + 2` points. ✓

## Steps 4 and 5
- The induction runs over `j`, uniformly in `g`. It applies the hypothesis to `φ(g)`, and it stays in `N_1` by
  `ρ(φ(P))`-invariance. ✓
- `k' = ρ_(φ^j g)k_0 ∈ K`, and `s'^j(k')` is defined. So for `j > n_0 + 1`, `k' = k_0` and `ρ_g x_j = x_j`.
- The complement of `{x_j : j > n_0 + 1}` is finite: it is the non-ray components together with `x_0, …, x_(n_0+1)`.
  ✓
- *Sanity check.* For `P = Z/2`, an involution `τ` with `s^(−1)τs` near `τ` is near a translation, hence near the
  identity. This agrees with item 1.

## Item 2, including 2(b) (the author asked about this)
- With infinite supports, `ρ : P → NearSym(N)` is injective.
- (a) `φ = ρ^(−1) ∘ Ad(s^(−1)) ∘ ρ` is an endomorphism, since conjugation by the near-permutation `s` is an
  automorphism of `NearSym(N)`. Item 1 then contradicts `P ≠ 1`. ✓
- (b) `sρ(P)s^(−1) = ρ(P)` gives `s^(−1)ρ(P)s = ρ(P)`, which is (a) with equality. ✓
- A proper inclusion `sρ(P)s^(−1) < ρ(P)` is correctly left open.

## Nits
- **N1 (item 3).** "Infinite" is not needed. Item 1 holds for every FW group, finite ones included, so any nontrivial
  FW subgroup `H` works. The phrase "no endomorphism twist … can map an infinite FW subgroup into itself" should say
  "into itself, when the twist of `P` restricts to `H`". That is what the proof uses.
- **N2 (Step 2).** Say that `0 ∈ E` is possible, because `Γ^0 = ∅`. Nothing depends on it.

## Overlap note (for team-lead)
- bh-kazhdan-inputs has asked me to review `fw-inputs-admit-no-twisted-normalizing-genuine-shell-action` (2a1326804).
  By its request, that node proves the same statement for `s^m`, `m ≠ 0`, with any map `φ` when `m > 0`.
- That subsumes items 1–2 here at `m = 1`. The two nodes should cross-reference each other in `distinct_from`, or one
  should be marked as a special case of the other.
