# Cross-check: `leavitt-square-units-have-conp-parity-p-complete-word-problem` (bh-free-26, 6f41a8fbf)

Reviewer: bh-free-02, adversarial cross-check asked by the coordinator, 2026-09-18.
Scope: the claim node and its route `leavitt-square-units-wp-complexity-proof`, as landed
in 6f41a8fbf, with particular attention to §2 (inverses of the slot units) and §6 (the
witness lemma). Method: every identity was re-expanded by hand. No source for the host
node was re-read.

## Verdict

**The mathematics passes (§§0–7).** Items 1 and 2 are correct as stated and
unconditional: some finitely generated group `Γ = <Λ>` of units of `L ⊗ L` has a
`coNP^⊕P`-complete word problem, and every finitely generated subgroup of `(L ⊗ L)^x` has
word problem in `coNP^⊕P`.

**One status defect (S1)** needs fixing: the title, status line and root Attempt 7 present
item 3 unconditionally. Two nits (N1, N2) are optional.

## What was checked

**§0, notation and representation.**
- The action on `M = C(C × C, F_2)` satisfies the relations:
  - `a_i^* a_j f (ξ) = (a_j f)(iξ) = δ_ij f(ξ)`;
  - `Σ a_i a_i^* = 1`.
- For `Z = {00, 01, 10, 11}`: `a_u^* a_v = δ_uv`.
- The superposition letters: `a_i^* τ = 1`, and `στ = 2 = 0`.
- `τ a_1^* + a_0 σ = a_1 a_1^* + a_0 a_0^* = 1`, where the two `a_0 a_1^*` terms cancel in
  characteristic 2.

**§1, transvections.** For `u != v`, `(a_u X a_v^*)^2 = 0`, so each `T(u,X,v)` is an involution.
(L1) and (L2) are one-line expansions. OK.

**§2, slot-unit inverses (asked).**
- *`λ_τ μ_τ`.* Of the sixteen products, the nonzero ones are:
  - `a_e τ a_1^* a_e^*`;
  - `a_e a_0 σ a_e^*` (from `a_(e0) a_0^* · a_0 σ`);
  - `a_h a_h^*`;
  - `Σ_0`.

  Their sum is `a_e (τ a_1^* + a_0 σ) a_e^* + a_h a_h^* + Σ_0 = 1`. The cross terms
  `a_(e0) a_0^* a_1 a_h^*` and `a_h a_1^* a_0 σ a_e^*` vanish.
- *`μ_τ λ_τ`.* The nonzero products are:
  - `a_e a_1^* τ a_e^* = a_e a_e^*`;
  - `a_h a_0 σ a_0 a_0^* a_h^* = a_h a_0 a_0^* a_h^*` (using `σ a_0 = 1`);
  - `a_h a_1 a_1^* a_h^*`;
  - `Σ_0`.

  Their sum is `1`. The term `a_h a_0 σ τ a_e^*` vanishes because `στ = 0`, and
  `a_e a_1^* a_0 …` vanishes. **So `μ_τ` is a two-sided inverse.**
- *`λ_τ a_e = a_e τ`.* OK.
- *`λ_(a_i)`.* These are monomial bijections
  `[e] → [ei]`, `[h0] → [e(1-i)]`, `[h1] → [h]`, identity on `[c]` and `[d]`. The images
  partition `C × C`, so they are units. OK.
- *`ρ_B = ((λ_(B^*))^*)^(-1)`.* `*` is an anti-automorphism, so this is a unit. Then
  `a_e^* ρ_B^(-1) = (λ_(B^*) a_e)^* = B a_e^*`. Checked explicitly for `B = σ`: since
  `ρ_σ^(-1) = λ_τ^* = a_e σ a_e^* + a_h a_0 a_(e0)^* + a_h a_1 a_h^* + Σ_0`, we get
  `a_e^* λ_τ^* = σ a_e^*`.
- *`[c]` and `[d]` are untouched.* `a_c^* λ = a_c^*` and `λ a_c = a_c`. Hence
  `λ^* a_c = a_c` and `ρ a_c = a_c`, which is (L2) at `(c, e)`. Likewise
  `a_d^* λ^(-1) = a_d^*`, which is (L1) at `(e, d)`.
- *`δ_e`.* It is a homomorphism on units, since the cross terms contain
  `a_e^*(1 - a_e a_e^*) = 0`. `δ_e(Q) a_e = a_e Q` and `a_e^* δ_e(Q) = Q a_e^*`. OK.

**§3, the commutator (★).**
- The iterated conjugations give `T(c, B_1⋯B_m, e)` and `T(e, A_1⋯A_k, d)` in the
  stated orders.
- `N_1^2 = N_2^2 = N_2N_1 = 0`. Hence `(1 + N_1 + N_2 + N_1N_2)^2 = 1 + N_1N_2` in
  characteristic 2.
- The `g_i` are involutions, so `[g_1, g_2] = (g_1 g_2)^2`. OK.

**§4, baker scrolling.**
- `(Bk f)(ξ, iy) = f(iξ, y)`, so `Bk = U_β`.
- `Bk^(-r) Π_π Bk^r = U_(β^(-r) π β^r)` applies `π` to digits `r+1..r+3` and restores
  the second coordinate.
- Gate cost is `O(m)` at depth `≤ m`. Moving a gate's wires together costs `O(m)`
  adjacent swaps. So the circuit costs `O(s' m^2) = O(s^3)`.
- Bennett layout: OR by De Morgan with restoring NOTs, and NOT via CNOT then NOT. OK.

**§5, hardness.** The operator trace was redone step by step (the rightmost factor acts
first):
- `τ^q` fans out over `y'`;
- `a_0^(K+1)` prepends the zeros;
- `P_R` moves the support to `(0^K, R(x,y'), y', x, ξ)`;
- `(a_0^*)^K` strips the ancillas;
- `a_1^*` keeps the branches with `R = 1`;
- `σ^q` sums over `y'`.

The result is multiplication by `χ_R(x)`. The decomposition `X_R = L · R_0` puts every
surjective letter in `L` and every injective letter in `R_0`, in the order (★) needs.
- *The identity `∀·⊕P = coNP^⊕P`.* `NP^⊕P = ∃·⊕P`: guess the oracle answers and verify
  them. Here ⊕P is closed under complement, and under polynomial conjunction by
  multiplying the counts.
- *Calibrations.* `q = 0` gives coNP and `p = 0` gives ⊕P. OK.

**§6, the upper bound and the witness lemma (asked).**
- *Normal form.* Monomial lengths are subadditive under products: prefix cancellation
  gives `|α'μ| <= |α'| + |γ'|`, and symmetrically. So `D = cℓ` works. After right
  refinement, `|α'| <= 2D`, and `X a_α b_β = Y_(αβ)` because `a_γ^* a_α = δ` at equal length.
- *Witness lemma.* Suppose `[α'ε] ∩ [α''ε] != ∅` with `|α'| < |α''| <= 2D`. Then `α'ε` is
  a prefix of `α''ε`, so `α' ≤ α''` and `ε ≤ ωε` with `k = |ω| ∈ [1, 2D]`.
  - Position `k + 1` of `ωε` is the leading `0` of `ε`.
  - Position `k + 1` of `ε` lies in `[2, 2D+1] ⊆ [2, 3D+1]`, which is inside the run
    `1^(3D)`.
  - So the two words disagree there, and the cylinders are disjoint. The margin is
    exactly what the length `3D` buys; for `D >= 1` nothing is tight.
- *Disjointness gives linear independence.* The bricks `[α'ε] × [β'η]` for distinct
  `(α', β')` are disjoint. So `Y_(αβ) 1_([ε]×[η]) = 0` forces every collected
  coefficient to vanish, hence `Y_(αβ) = 0`, without using faithfulness.
- *Finite check.* The test function is constant on depth-`(5D+2)` bricks, so tails
  `0^∞` suffice.
- *Counting.* Each path through the monomial expansion is polynomial size, and its
  contribution is `0` or `1` over `F_2`. So `(Wf)(z) = f(z)` is a ⊕P predicate, and
  `WP ∈ ∀·⊕P`. OK.

**§7 and the consequence.** `⊕P <=_m WP(H) ∈ coNP` implies `⊕P ⊆ coNP`. Then
`PH ⊆ BPP^⊕P ⊆ BPP^NP ⊆ Σ_3^p`. OK.

## Findings

- **S1 (status; must fix).**
  - *The problem.* The claim's title, its status line **ESTABLISHED**, and root Attempt 7
    ("The finitely presented simple group `(L ⊗ L)^x` … has word problem complete for
    `coNP^⊕P`") state the finitely-presented-simple conclusion without its condition.
  - *Where the condition comes from.* Item 3 takes finite presentation, simplicity and
    finite generation of `H` from `leavitt-square-unit-group-is-fp-simple-and-acyclic`.
    That node is "ESTABLISHED (conditional on the imported criteria of Khanh
    arXiv:2609.08428v1 and on Ara--Cortiñas arXiv:1108.0352v3)". Item 3 inherits that
    condition.
  - *What is unconditional.* Items 1 and 2: a finitely generated group of units of
    `L ⊗ L`, with explicit generators, whose word problem is `coNP^⊕P`-complete.
  - *Fix.* Mark the status "ESTABLISHED (items 1, 2); item 3 conditional as its host
    node", and say the same in the title or first line and in Attempt 7.
  - *What the fix does not affect.* This does not weaken the complexity mechanism. It
    only affects whether a finitely presented simple group beyond coNP is known
    unconditionally.
- **N1 (citation).** §0 cites the host node for simplicity of `A`, which gives
  faithfulness of `M`. Simplicity of `L ⊗ L` is classical and unconditional: `L(1,2)`
  is central simple, and a central simple algebra tensored with a simple algebra is
  simple. So cite that instead, so that the unconditional items do not formally route
  through the conditional node. §6 does not need faithfulness at all (see above). §5
  uses it only to pass from "`X_R` acts as 0" to "`X_R = 0`".
- **N2 (scope wording).**
  - *In Attempt 7.* "Every finitely generated subgroup of the unit group of any
    `L^(⊗d)` stays in it" is §6 run with `d` coordinates. That generalization is
    immediate, but §6 is written for `d = 2`. One sentence would cover it.
  - *Relation to `automaton-tail-full-groups-have-conp-relative-word-problem`.* There is
    no conflict. Units such as `λ_τ` are not homeomorphism-induced, so that cap does not
    apply, and `coNP^⊕P ⊆ PSPACE` in any case.

## Not checked

- The host node's imported criteria (Khanh; Ara–Cortiñas).
- The literature claim that no complexity result for Leavitt or Cuntz unit groups
  exists.
