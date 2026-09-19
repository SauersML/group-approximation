---
rg: 2
id: rotation-centralizer-rotation-gaps-are-uniform
kind: claim
title: "For each displacement c, some rotation centralizer C_T(r_k) with 2^k >= pi/c has corona gap at r_k larger than the rounding error L pi 2^(-k)"
distinct_from:
  lifted-thompson-t-is-not-mf: equivalent to it, by item 3 of central-power-quotient-gaps-converge-to-the-extension-gap and lifted-thompson-t-quotients-are-rotation-centralizers; this is its form as a statement about the finite-order quotients C_T(r_k) only, with a quantitative threshold, and mentions no element of infinite order.
  thompson-t-has-full-mf-radical: that is the qualitative statement at one level (it gives delta_(2^k)(c) > 0 for each k via item 4 of central-eigencorners-die-over-full-radical-quotients); this asks for a quantitative gap beating L pi 2^(-k).
  lifted-thompson-t-centre-has-commutant-eigencorners: that asks for spectral projections of rho(z) in a relative commutant; this asks only for finite-dimensional defect bounds for tuples in which z has exact order 2^k.
---

**OPEN.** Fix a finite presentation `T̄ = ⟨S | R⟩` with `z ∈ S`, and let `L` be the largest
number of letters `z^{±1}` in a relator. For `k ≥ 0` let `δ_{2^k}(c)` be the gap of the target
of `central-power-quotient-gaps-converge-to-the-extension-gap` for `m = 2^k`. That is the
smallest defect, against `R ∪ {z^{2^k}}`, of a finite unitary tuple with `||U_z − 1|| ≥ c`.
By `lifted-thompson-t-quotients-are-rotation-centralizers`, `⟨S | R ∪ {z^{2^k}}⟩` presents
`C_T(r_k)` with `z ↦ r_k`. Claim:

```text
for every c in (0,2) there is k with 2^k >= pi/c and δ_{2^k}(c) > L π 2^{-k}.      (UG)
```

## Equivalent forms

By item 3 of `central-power-quotient-gaps-converge-to-the-extension-gap`, applied with
`M = {2^k}`, (UG) is equivalent to each of the following:
- `lifted-thompson-t-is-not-mf`;
- `inf_k δ_{2^k}(c) > 0` for every `c`;
- `2^k δ_{2^k}(c) → ∞` for every `c`.

In particular (UG) does not depend on the presentation chosen, although `L` and `δ` do. By item
4 there is no middle ground. Either the gaps of `r_k` are bounded below uniformly in `k`, or for
all small `c` they are at most `Lπ 2^{-k}` at every level `k` with `2^k ≥ π/c`.

## How it can fail

A refutation is a sequence of finite unitary tuples `U^{(k)}` in which
- `U^{(k)}_z` has exact order `2^k` and moves some vector by at least `c`, and
- the relators of `T̄` hold up to `Lπ 2^{-k}`, or even up to `O(2^{-k})` with any constant.

By items 1 and 2 of that claim, such a sequence exists (with the constant `L`) exactly when
there is a corona representation of `T̄` with `ρ(z) ≠ 1`, that is, when `T̄` is MF. By item 4,
whenever (UG) fails it already fails at the rounding rate `Lπ 2^{-k}`.

## Attempts

- **2026-09-19 (swarm-0917-w19-w19-ptm-last1, quantifier-shift): deriving the level-k gaps from
  the gap of `T` by cutting `U_z` into eigenclusters loses exactly the factor that item 4
  forbids losing. Heuristic, recorded as a class obstruction, not proved as a theorem.**
  - *Idea.* Let `U` be a tuple with `U_z^{2^k} = 1` exactly and small defect `ε`. The spectral
    projections `E_j` of `U_z` onto its `2^k` eigenvalues commute with `U_s` up to an error.
    On each `E_j`, `U_z` is a scalar. So the compressed tuple, with the `z`-letter deleted,
    nearly satisfies the relators of `T`. A gap `κ` for `T` would then bound `ε` below.
  - *Where it dies.* The commutator `||[E_j, U_s]||` is controlled only through polynomials
    in `U_z` that separate the `2^k` eigenvalues. Fejér-type polynomials of degree `< 2^k` do
    this, and their Lipschitz constant is of order `2^k`. So the bound obtained has the shape
    `ε ≳ κ / (C L 2^k)`. That is the same order `2^{-k}` as the threshold `Lπ 2^{-k}` of (UG).
    The method therefore decides (UG) only through a comparison of the constants `κ/C`
    and `π`, and defects are always at most 2.
  - *Also tried, no gain.*
    - Self-similarity through the dilation `λ`, which embeds `C_T(r_{k+1})` into `C_T(r_k)`
      and doubles the order of the rotation. It changes `L` by a bounded factor but again
      costs a factor `2` per level.
    - Determinant and `tr log` phases of `U_z`. The relators constrain only mean phases, not
      the displacement `||U_z − 1||`.
  - *Consequence.* Any proof of (UG) must produce gaps at level `k` that beat `2^{-k}` by an
    unbounded factor, and item 4 says that is the same as a uniform gap. So a proof has to see
    all levels at once, for instance through a uniform-in-`k` stability or spectral-gap
    statement for the family `C_T(r_k)`, not level by level from `T`.
