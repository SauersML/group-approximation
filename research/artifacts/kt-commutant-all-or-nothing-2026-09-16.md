# Kun--Thom commutant collapse is all-or-nothing: worked example, check log, scope

Companion to the claim `kt-compressor-commutant-collapse-is-all-or-nothing`
and its direct proof `kt-compressor-commutant-collapse-all-or-nothing-proof`
(2026-09-16). The proof lives in the route. This file records a worked
instance of the subring dichotomy lemma, the computational sanity check, and
the exact scope of the statement.

## 1. Worked instance of the subring dichotomy lemma (d = 3)

Take `f_- = x_1 x_2^(-1) + x_1^2 x_2 x_3^(-1)`, so the support is
`{(1,-1,0), (2,1,-1)}`. Suppose `f_-` lies in a compressor-stable subring `S`
with `R_+ <= S <= R`.

1. The first exponent is negative in coordinate 2. The cyclic `P in A_3` with
   `P e_2 = e_1`, `P e_1 = e_3`, `P e_3 = e_2` acts by
   `P m = (m_2, m_3, m_1)`. The support becomes `{(-1,0,1), (1,-1,2)}`.
2. `M = 2`, `K = 5`, `psi = (25, 5, 1)`. The values are `psi(-1,0,1) = -24`
   and `psi(1,-1,2) = 22`. The unique minimizer is `(-1,0,1)`.
3. `L` has rows `(25,5,1)`, `(1,0,0)`, `(0,1,0)`, and `det L = 1`. The images
   are `L(-1,0,1) = (-24,-1,0)` and `L(1,-1,2) = (22,1,-1)`.
4. `n_1 = max(0, -22) = 0` and `n = (0,2,2)`. The shifted exponents are
   `(-24,1,2)` and `(22,3,1)`. The second lies in `N^3`. Hence
   `x_1^(-24) x_2 x_3^2 in S`.
5. Multiplying by `x_1^23` gives `v = (-1,1,2)`. Then
   `L' = I + E_21 + 2 E_31` satisfies `L' v = (-1,0,0)`, so
   `x_1^(-1) in S`, and then `S = R`.

These numbers were re-verified with the helper functions of the experiment
script.

## 2. Computational sanity check

The script is
`experiments/kt-commutant-all-or-nothing-2026-09-16/subring_lemma_check.py`.
It is pure Python, single-threaded, runs in about a second, and uses seed
`20260916`. It draws 3000 random exponent supports for each `d = 3, 4, 5`:
sizes 1 to 6, entries in `[-R, R]` with `R <= 4`, and every exponent outside
`N^d`. Each run of Steps 1-5 asserts:

- `P` is an even permutation matrix;
- `psi` is injective on the support and induces the lexicographic order;
- the minimizer has negative first coordinate and negative `psi`;
- `L` is nonnegative with determinant 1;
- every shifted exponent other than the minimizer lies in `N^d`;
- the isolated exponent has negative first coordinate and nonnegative tail;
- `L'` is nonnegative unimodular with `L' v = -e_1`.

Output, saved in `output.txt`:

```text
all checks passed: 9000 random supports, d in {3,4,5}
```

The check tests only the combinatorics. The algebraic steps are proved in the
route.

## 3. Scope and non-scope

**What is new relative to the graph.**

- `relative-wall-commutant-growth` (invariance form) gives, for every
  infranormal pair, "wall for some compressor iff `C_0` is not
  `Ad pi(G)`-invariant". Here, only for the Theorem E pair:
  - (CCR) for ONE strict monomial compressor already forces invariance;
  - ONE non-polynomial root, or ONE nonzero monomial torus element, decides;
  - in the wall case the `SL_d(Z)`-stabilizer of `C_0` is exactly `A_d`.
- The target's torus reduction tests normalization of `sigma(Lambda)' cap M`
  by the finitely many balanced monomial diagonals. The present criterion
  tests a single element, and it is phrased for `sigma(Gamma)' cap M`.
- `kt-centralizer-normalization-hs`, Attempts 2026-08-18 item 1, calls
  one-compressor (CCR) "strictly weaker than the normalization question in
  the header". As a universal statement over models of a general infranormal
  pair this is a formal remark. At the Theorem E pair, with monomial
  compressors, the two coincide model by model, so neither can be proved or
  refuted without the other.

**Consequence for `kt-canonical-hs-normalization-fails`.** In any model with a
non-normalized `Gamma`-commutant, the saturation `Gamma^sat` (a commutation
stabilizer of a countable subfamily of `C_0`) meets each root group only in
its polynomial part. It contains no strict monomial compressor and no nonzero
monomial torus element. So one-compressor subgroups `<Gamma,t>` never occur
as saturations, although they can still serve as intermediate subgroups `K`
in that node's converse direction.

**Not covered.**

- Compressors `g in P_Gamma` outside `N_G(Gamma) SL_d(N)`, for example
  products `u L` with `u in E \ Gamma`. For these, (CCR)_g follows from
  normalization, but the converse was not proved here.
- Which alternative occurs for trace-faithful matrix-ultraproduct models.
  That is still exactly the open (AC) question, now in the single-root form
  "does `sigma(e_12(x_1^(-1)))` commute with `sigma(Gamma)' cap M`?".
- Any analytic or approximation input. The argument uses no trace, no
  property (T) and no microstates, and it holds for homomorphisms into
  arbitrary groups. This is why it cannot decide (AC). By
  `relative-wall-commutant-growth` and `kun-thom-clifford-cover-weakly-sofic`,
  walls exist for some target group.
