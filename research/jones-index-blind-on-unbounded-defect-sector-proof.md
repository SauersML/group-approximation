---
rg: 2
id: jones-index-blind-on-unbounded-defect-sector-proof
kind: route
title: Every proper conditional expectation has Pimsner-Popa index at least 2, and the pinching index of P' <= P is 2 exactly when P' != P
target: jones-index-blind-on-unbounded-defect-sector
requires:
  - bounded-multiplicity-kazhdan-sectors-miss-leavitt-cover-defect
  - kazhdan-kernel-isotypic-sectors-extend-within-kernel-closure
artifacts:
  - research/artifacts/rnorm-jones-index-2026-09-12.md
---

The complete proof is below. Artifact Sections 2--4 repeat it with context.

**Inputs.** The two required claims supply only the objects: `H_inf`, `W_rho`,
`A_rho`, and the nested pair `P' = W_rho(u)^* P W_rho(u) <= P` (after relabeling),
with `Q = P - P'`. The argument itself is elementary operator theory.

**Correction.** This supersedes the proof landed in 939a37611.
- Its Step 1 claimed that a weighted diagonal realizes `Ind(E) = int f dmu` for
  every `f >= 1`, so that there is no gap in `(1,2)`. That is false by Lemma 1.
  The smallest counterexample: for `C <= C^2` with `E(a,b) = ta + (1-t)b`, the
  best constant is `lambda = min(t, 1-t) <= 1/2`.
- Its Step 3 dichotomy ("quantization iff subfactor iff bounded multiplicity") is
  withdrawn.

**Lemma 1 (free gap).** Let `N <= M` be a unital inclusion of von Neumann algebras
and `E : M -> N` a conditional expectation (positive, unital, `N`-bimodular).
- If `N != M`, every `lambda` with `E(y) >= lambda y` for all `y >= 0` satisfies
  `lambda <= 1/2`.
- If `N = M`, then `E = id` and `Ind(E) = 1`.

So `Ind(E) in {1} U [2, infinity]`.

*Proof.*
1. Pick `x in M \ N` and write `x = a + ib` with `a, b` self-adjoint. They are not
   both in `N`, so some self-adjoint `a` lies outside `N`.
2. Put `h = a - E(a)`. Then `h = h^*` and `h != 0`, since `a` is not in `N`. Also
   `E(h) = E(a) - E(E(a)) = 0`.
3. Rescale to `||h|| = 1`. The spectrum of `h` lies in `[-1,1]` and contains `1`
   or `-1`; replacing `h` by `-h` if necessary, `1 in spec(h)`.
4. Put `y = 1 + h >= 0`. Then `E(y) = 1`, so `1 - lambda(1+h) >= 0`. The spectral
   point `1` of `h` gives `1 - 2 lambda >= 0`.
5. If `N = M`, then `E` is a projection onto `M`, so `E = id`. Taking `y = 1`
   always gives `lambda <= 1`. ∎

**Lemma 2 (pinching).** Let `0 != P' <= P` be projections in a von Neumann algebra
`B`, with `Q = P - P'`. Put `M = PBP` (unit `P`), `N = P'BP' + QBQ`, and
`E_P(x) = P'xP' + QxQ`.
- `E_P` is a conditional expectation onto `N`.
- `Ind(E_P) = 1` if `Q = 0`.
- `Ind(E_P) = 2` if `Q != 0` and `P'BQ != 0`.

For `B = B(H_inf)`, `P'BQ != 0` whenever `P' != 0` and `Q != 0`.

*Proof.*
1. `E_P` is idempotent, positive and unital. For `n = P'aP' + QbQ` in `N`,
   `E_P(nx) = n E_P(x)`, and likewise on the right.
2. If `Q = 0`, then `N = M` and Lemma 1 applies.
3. If `Q != 0` and `P'BQ != 0`, then `N != M`, so `lambda <= 1/2` by Lemma 1.
4. For `x >= 0` in `M`, `(P' - Q) x (P' - Q) >= 0` gives
   `P'xQ + QxP' <= P'xP' + QxQ`. Hence `x = E_P(x) + P'xQ + QxP' <= 2 E_P(x)`, so
   `lambda = 1/2`. ∎

**Step 3 (consequence).** Apply Lemma 2 on `H_inf` with `B = B(H_inf)`: index
`< 2` holds iff `P' = P`, i.e. iff `W_rho(u)^* P W_rho(u) = P` on that sector.
- "Below `2` forces `1`" is Lemma 1, which uses no (T), no factoriality and no
  Jones quantization.
- Lemma 1 holds for amenable hosts as well.
- So the surviving shape reduces verbatim to proving `P' = P`, and the index
  supplies no step toward it.

**Literature.** Pimsner--Popa, *Entropy and index for subfactors*, Ann. Sci. ENS
19 (1986), introduced the constant `lambda(E)`. Lemmas 1 and 2 are proved here in
full and do not rely on that citation. Jones, *Index for subfactors*, Invent.
Math. 72 (1983), is cited only for the remark that the finer quantization in
`[2,4)` needs subfactors. It is not used.

**No root established.** The target is a no-leverage statement. `cairn why` must
show `nonsofic-hyperbolic-group` and `relative-normalization-modulo-kazhdan-kernel`
OPEN.
