---
rg: 2
id: artin-level-zero-witnesses-need-not-twist-proof
kind: route
title: "Non-descending level-0 witnesses: specialisation at s = 0, a two-functional computation in dimension 2, and exact checks over F_5"
target: artin-level-zero-witnesses-need-not-twist
requires: []
artifacts:
  - experiments/artin-level-descent-census-2026-09-17/verify_example.py
  - experiments/artin-level-descent-census-2026-09-17/verify_example.log
  - experiments/artin-level-descent-census-2026-09-17/char0_witness.py
  - experiments/artin-level-descent-census-2026-09-17/char0_witness.log
  - experiments/artin-level-descent-census-2026-09-17/verify_candidate2.py
  - experiments/artin-level-descent-census-2026-09-17/verify_candidate2.log
  - experiments/artin-level-descent-census-2026-09-17/verify_perm.py
  - experiments/artin-level-descent-census-2026-09-17/verify_perm.log
  - experiments/artin-level-descent-census-2026-09-17/candidate_anatomy.py
  - experiments/artin-level-descent-census-2026-09-17/candidate_anatomy_l5.log
  - experiments/artin-level-descent-census-2026-09-17/candidate_anatomy_l7.log
  - experiments/artin-level-descent-census-2026-09-17/perm_search.py
  - experiments/artin-level-descent-census-2026-09-17/perm_calib.log
  - experiments/artin-level-descent-census-2026-09-17/perm_candidate_n6.log
  - experiments/artin-level-descent-census-2026-09-17/calib2.log
---

Notation is as in the claim. All kernels are column kernels, matrices act on the left, and
`χ(p_ρ) = 1` for every cross edge.

## Part 1: `ct <= c0`

`M_π(s)` is a `4n x n` matrix whose entries are polynomials in `s`.
- At `s = 0`, the `ρ`-block is `-π(σ_ρ)`. So `corank M_π(0) = c0(π)`.
- The rank of a polynomial matrix at a specialisation is at most its rank over `F(s)`. So
  `ct = n - rank_(F(s)) M_π <= n - rank M_π(0) = c0`.
- Hence `ct > 0` forces `c0 > 0`. Any vector in the twisted kernel can be scaled to a
  polynomial vector `v(s)` with `v(0) ≠ 0`, and `v(0)` lies in the common kernel.

The converse is exactly the question whether the corank jumps at `0`. ∎

## Part 3: the two-functional computation

Let `π` be as in Part 3 of the claim, over a field `F`. Let `v` span the common kernel of
`1 + π(ac)` and `1 + π(be)`, and let `φ ≠ 0` be a functional with `ker φ = F v`.

**Setting up.**
- A rank-one map with kernel `Fv` has the form `w ↦ φ(w) u`. So `1 + π(ac) = u φ` and
  `1 + π(be) = u' φ`, with `u, u' ≠ 0`.
- **`c0 = 1`.** The `bc` and `ae` blocks vanish. The other two blocks have common kernel `Fv`.
- **Twisted kernel.** The `ρ`-blocks of `M_π(s)` are `0, u φ (sA - 1), u' φ (sB - 1), 0`, with
  `A = π(a)` and `B = π(b)`. So `ct > 0` iff the two functionals `φ(sA - 1)` and `φ(sB - 1)` on
  `F(s)^2` are linearly dependent over `F(s)`.

**Step A (an invariant line is impossible).** Suppose `Fv` is invariant under `A` and `B`.
- From `(1 + π(ac)) v = 0` we get `π(c) v = -A^(-1) v ∈ F v`. Likewise `π(e) v = -B^(-1) v ∈ F v`.
- So `Fv` is a 1-dimensional subrepresentation `λ`. On it `λ(σ_ρ) = 0` for all four `ρ`: the
  `bc` and `ae` sums vanish identically, and `λ(ac) = λ(be) = -1`.
- Remark R1 of `artin-2x2-dead-joins-sigma1-iff-k-q-odd-family-proof` now applies:
  - `y = λ(bc) = -λ(b)/λ(a)` satisfies `λ(ae) = y^(-1)`.
  - `S_q(y) = 0` gives `y^q = 1`, and `S_p(y^(-1)) = 0` gives `y^p = 1`, so `y = 1`.
  - Then `q = p = 0` in `F`. This contradicts `gcd(q, p) = 1`.

**Step B (the case `A` scalar).** Here `φ(sA - 1) = (sα - 1) φ`. Dependence would need
`φ(sB - 1) = s φB - φ` to be proportional to `φ`, that is `φ B ∈ F φ`, that is `B v ∈ F v`. This
is excluded by Step A.

**Step C (the case `A` not scalar).**
- The centraliser of a non-scalar `2 x 2` matrix is `F[A]`, so `B = β + γ A`.
- By Step A, `v` is not an eigenvector of `A`, so `φ` and `φA` are independent.
- In the basis `(φ, φA)`:
  - `φ(sA - 1)` has coordinates `(-1, s)`;
  - `φ(sB - 1)` has coordinates `(sβ - 1, sγ)`.
- The determinant is `-sγ - s(sβ - 1) = -s(sβ + γ - 1)`. It vanishes identically iff
  `β = 0` and `γ = 1`, that is `B = A`.

**Step D (`B = A` is impossible).**
- `B = A` gives `π(bc) = π(ac)`. That matrix has eigenvalue `-1`, because `1 + π(ac)` is
  singular.
- So `S_q(-1) = 0`, which forces `q` even. This holds in every characteristic: in
  characteristic 2 it reads `S_q(1) = q = 0`.
- Likewise `π(ae) = π(be)` forces `p` even. This contradicts `gcd(q, p) = 1`.

Hence `ct(π) = 0`. The determinant `-s(sβ + γ - 1)` also shows where the corank jumps: at
`s = 0`, which gives the level-0 witness, and at `s = (1 - γ)/β`. ∎

## Part 2: the explicit witnesses

`verify_example.py` checks both representations with sympy, independently of the search code
(output in `verify_example.log`). It verifies:
- the six Artin relations over `F_5`;
- the four `π(σ_ρ)`;
- the rank of their stack, which is `1`, so `c0 = 1`;
- the gcd of all nonzero `2 x 2` minors of `M_π(s)` over `F_5[s]`, which is nonzero. So
  `ct = 0`.

The gcds are `s(s - 1)` for `(2, 3, 2, 4)` and `s^2` for `(2, 3, 2, 5)`.

Both representations have the shape of Part 3:
- `π(σ_bc) = π(σ_ae) = 0`;
- `1 + π(ac)` and `1 + π(be)` have rank one and the same kernel.

For `(2, 3, 2, 4)`:
- `π(bc)` has order 3 with trace `-1`, so its eigenvalues are the primitive cube roots of unity.
- `π(ae)` has order 4 with trace `0`, so its eigenvalues are `±i`.
- `π(ac)` and `π(be)` are reflections.
- The characteristic 5 does not divide any label.

For `(2, 3, 2, 5)`, `π(ae)` is unipotent of order 5, so this example is specific to
characteristic 5.

**Characteristic 0 (numerical, supporting only).** `char0_witness.py` solves the Part 3 ansatz
over `C`. It sets `π(ac)` and `π(be)` to reflections with common `(-1)`-eigenvector `e_1`,
`π(b) ∈ C[π(a)]`, and `[π(c), π(e)] = 0`, and prescribes the spectra of `π(bc)` and `π(ae)`.
- For `(2, 3, 2, 4)` and `(2, 3, 2, 5)` it finds solutions with relation defect about
  `10^(-14)` (`char0_witness.log`).
- For `p = 4`, the runs with prescribed eigenvalues `-1, -1` for `π(ae)` fail the relations,
  with defect `>= 9`. The spectrum then does not force `π(ae)` to be diagonalisable, so these
  runs are discarded.
- The stacked `σ` has smallest singular value exactly `0`.
- The smallest singular value of `M_π(s)` at a random `s` is between `0.39` and `2.0`.

Part 3 proves `ct = 0` for all of them. The numerics only show that such representations exist
over `C`. For the claim, the exact `F_5` witness for `(2, 3, 2, 4)` suffices.

## Part 4: twists and cyclic inductions

- **Twists.** `σ_ρ ∈ Z[H]` is unchanged by `π ↦ π_ω`, and `π_ω(p_ρ) = ω π(p_ρ)`. So
  `M_(π_ω)(s) = M_π(ωs)`, and the generic corank is the same.
- **Cyclic inductions.** Put `G_N = χ^(-1)(N Z)`. After extending scalars to contain the `N`-th
  roots of unity, which changes no rank:
  - `Ind_(G_N)^G Res π ≅ ⊕_(ω^N = 1) π_ω`;
  - `M` of a direct sum is block diagonal, so `ct` is additive;
  - so `ct(Ind) = N · ct(π) = 0`, while `c0(Ind) = N · c0(π) > 0`. ∎

## Remark: the two-functional criterion without commuting `p`-vertices

The computation of Part 3 needs neither the 2x2 join nor `[A, B] = 1`. Suppose a 2-dimensional
`π` has:
- all cross sums zero except two, `π(σ_1) = u φ` and `π(σ_2) = u' φ`, with a common kernel
  `Fv = ker φ`;
- `p`-vertices `P_1` and `P_2` for these two cross edges.

Choose a dual basis `(φ, ψ)` and write `φ π(P_1) = α_1 φ + α_2 ψ` and `φ π(P_2) = δ_1 φ + δ_2 ψ`.
The determinant of the two twisted functionals is `s [ s(α_1 δ_2 - α_2 δ_1) - δ_2 + α_2 ]`. So:

```
ct(π) > 0  ⟺  φ π(P_1) = φ π(P_2),  or  F v is invariant under both π(P_1) and π(P_2).
```

## Part 5: `G_5`

Each of the three checks below is independent of the search code.

**The 2-dimensional witness.** `verify_candidate2.py` works over `F_5` (output in
`verify_candidate2.log`). It verifies:
- the eight Artin relations;
- the sums `σ_ab = σ_ae = 0`;
- `σ_ac = [[2,1],[1,3]]` and `σ_db = [[2,1],[0,0]]`, which have common kernel spanned by
  `(1, -2)`, so `c0 = 1`;
- the gcd of the nonzero `2 x 2` minors, which is `s(s - 2) ≠ 0`, so `ct = 0`.

The anatomy fits the remark above:
- `π(ab)` has order 3;
- `π(ae)` is unipotent of order 5, since `e = 2` is scalar, so the witness uses characteristic 5;
- `π(ac)` has order 10 and `π(db)` is a reflection.

`candidate_anatomy.py` lists all 52 such witnesses over `F_5` (`candidate_anatomy_l5.log`). Over
`F_7` the search finds no 2-dimensional representation with all four cross sums singular
(`candidate_anatomy_l7.log`).

**The twisted witness.** `verify_perm.py` works with sympy over `Q(s)` (output in
`verify_perm.log`). For the `S_6` representation of the claim it verifies:
- the eight Artin relations, as permutation matrices;
- rank 5 for the stacked `σ`;
- rank 5 for the twisted stack over `Q(s)`;
- that `e_5 - e_1` is killed identically in `s`.

This is the certificate of the claim's framework: `ct > 0`, so `[χ] ∉ Σ^1(G_5)`. ∎

The `S_6` representation was found by `perm_search.py`, which searches all homomorphisms
`G -> S_n`, with `a` up to conjugacy. Before testing any cross edge exactly, it filters by the
rank at three random points of `F_1000003`.
- **Calibration** (`perm_calib.log`): on `(2, 3, 2, 4)` it finds the known `S_6` twisted
  witnesses, 392 of 99392 homomorphisms, and none for `n <= 5`.
- **On `G_5`**: there are no homomorphisms with all cross sums singular for `n <= 4`. For
  `n = 5` there are 766 homomorphisms, 38 with `c0 > 0` and none twisted. For `n = 6` there are
  23580 homomorphisms, 217 with `c0 > 0` and 12 twisted (`perm_candidate_n6.log`).

## Where the census stands (data, not used above)

`calib2.py` records `c0pos` and `ctpos` in `calib2.log`, over `F_3` and `F_5` plus the
`(2,2,2,2)`, `(2,2,2,3)` and `(2,2,2,5)` rows over `F_7`.

The 5-vertex search `census2.py` (three seeds) covers two-block, non-star dead cuts of circuit
rank `>= 3`, over `F_3` and `F_5`. It gave 25 NONMEMBER, 8 SILENT and 1 CANDIDATE.
- The CANDIDATE is `G_5`, which Part 5 settles as a non-member.
- The SILENT instances are not decided by this search, since membership needs a `Z[H]`
  identity.
