# Swarm 3 and 4 adversarial review (2026-09-12)

Reviewer lane `swarm4-reviewer`.

**Scope.** Claims first landed on main after 2026-09-12 15:00 CDT by the swarm 3 and swarm 4 lanes of
session `01PWzwKNBr2dwjX4pucBuXff`.
- Claims landed earlier belong to `review-backlog` and `review-backlog-2`.
- Claims from the w3 and gk lanes of the Gottschalk session are covered in
  `research/artifacts/w3-vf-*-verification-2026-09-12.md` and `gk-vf-*-verification-2026-09-12.md`.

Each section covers one claim and gives the verdict (PASS, FAIL or GAP) with the specifics. Sections are
landed one batch at a time.

## 1. `subgroup-cosets-are-independent-over-division-closure` (f00694d22): PASS

Checked against `subgroup-cosets-independence-proof`.
- **Denominators.** `U(H)` is the Ore localization of `N(H)` at its non-zero-divisors, so finitely many
  elements have a common left denominator `b`. The inclusion `N(H) <= N(G)` sends non-zero-divisors to
  non-zero-divisors, so clearing `b` inside `U(G)` is legitimate.
- **Supports.** `N(G)` commutes with right translations. So `c δ_x` is the right translate of
  `c δ_e ∈ l^2(H)`, and it lies in `l^2(Hx)`. Distinct right cosets give orthogonal subspaces, and `δ_e`
  is separating for `N(G)`, so each `c_i = 0`.
- **Free module.** `d·(hx) = (dh)·x` with `dh ∈ D_H`, so the span is `Σ_x D_H x`, and the lemma makes it
  free.
- The statement is standard, as the node says, and it uses no hidden hypothesis.

## 2. `vertex-division-closure-escapes-edge-coset-span` (f00694d22): PASS on the statement, three slips in the route corrected forward

**The statement holds.** `(1+s)^(-1)` lies in `D_A` but not in `span_(D_C)(A)`, for any `s` normalizing
`C` with infinite order in `N_A(C)/C`.

**Slip 1, step 1 (justification only).**
- The route identifies `l^2(P)` with `l^2(C) ⊗ l^2(Z)` by `c s^k ↦ δ_c ⊗ δ_k`. Under that map `λ(s)` is
  `U_σ ⊗ shift`, not `1 ⊗ shift`, unless `s` centralizes `C`.
- The conclusion survives. `l^2(A)` is the orthogonal sum of the `l^2(<s>g)` over the right cosets of
  `<s>`, and `λ(s)` is the bilateral shift on each.
- So `1 + λ(s)` is multiplication by `1 + z` on `L^2(T) ⊗ l^2(<s>\A)`. It is injective with dense range,
  so it is invertible in `U(A)`.

**Slip 2, step 3 (unjustified, not needed).**
- The route asserts that `D_C` has no zero divisors. That is not justified: the claim assumes neither
  torsion-freeness nor Strong Atiyah for `C`, and for finite `C` the division closure is `K[C]` itself.
- Step 4 does not need it. Suppose `(1+s) y = 1` with `y = Σ_(k=m..M) y_k s^k` and `y_m ≠ 0 ≠ y_M`.
  - The degree-`m` coefficient of the product is `y_m`, so `m = 0`.
  - The degree-`(M+1)` coefficient is `σ(y_M)`, so `M + 1 = 0`.
  - That contradicts `m <= M`.
- Only the extreme coefficients of `1 + s` enter, and both are `1`.

**Slip 3, the closing remark (false as stated).**
- The remark says the argument runs verbatim for any element of `K[P]` that is supported on at least two
  `C`-cosets and invertible in `U(P)`.
- Counterexample: `A = P = Z/2 × Z`, `C = Z/2 = <ε>`, `s` a generator of `Z`, `e = (1 + ε)/2`.
  - `x = e + (1 - e)s` is supported on `C` and `Cs`.
  - `x·(e + (1 - e)s^(-1)) = 1` in `K[P]`, so `x^(-1)` lies in `span_(D_C)(P)`.
- The remark is correct when the extreme coefficients are non-zero-divisors of `D_C`. That includes
  torsion-free `C` satisfying Strong Atiyah, where `D_C` is a division ring, and that is the only case the
  Atiyah region uses.

**Scope of the "Consequence" section.** The sentence that tree methods "cannot decide injectivity of φ"
describes methods; it is not a theorem. The node already calls it an obstruction to a method, and no
route consumes it.

**Cairn.** The route text is corrected in the same landing as this section. No status changes: the claim
stays ESTABLISHED and `kazhdan-edge-coproduct-rank-is-inner-rank` stays OPEN.
