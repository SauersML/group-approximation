# Independent review: three projections are a universal test for Kaplansky's quasitrace problem

Reviewer lane `reviewer`, 2026-09-12. The coordinator requested an adversarial review of commit 8b7b1fa7:
- `stw01-three-projection-algebra-quasitraces-are-traces`;
- the route `stw01-problem-i-via-three-projection-algebra`;
- the proof artifact `research/artifacts/stw01-three-projection-universal-test-2026-09-12.md`.

The focus was the dilation (Step 4) and the pullback (Step 5), and checking the two cited statements against the primary sources.

## Verdict

| item | verdict |
| --- | --- |
| Steps 0–3 (non-additivity reduced to `τ(y + βq) ≠ τ(y) + βτ(q)`) | **PASS** |
| Step 4 (the 2×2 dilation) | **PASS** |
| Step 5 (amplification, restriction, pullback) | **PASS** |
| sharpness and group-surjection remarks | **PASS** |
| (I1), (I2), (I3), (I4) as quoted through Gow | **match Gow v2 verbatim** |
| (I3), (I4) against the primary sources | **NOT VERIFIED**: primaries inaccessible from MSI (§4) |

The reduction is correct as mathematics, given its literature inputs. Its trust surfaces are:
- Wright 1975 (a type II_1 AW*-factor with a faithful state is W*);
- Fehlker's collection of properties of the canonical quasitrace (Gow Theorem 2.22);
- the Blackadar–Handelman equivalence behind Gow Theorem A;
- Blackadar–Handelman Corollary II.1.10.

The last one can be removed (§3).

## 1. Steps 0–3

- **Step 0.**
  - Additivity and homogeneity on `M_+` give linearity on `M_sa`, because `(x+x')_+ + x_− + x'_− = (x+x')_− + x_+ + x'_+` and `τ` is additive on positives.
  - `τ(x + iy) = τ(x) + iτ(y)` then gives linearity on `M`, so `τ` is a faithful state and (I4) applies.
- **Step 1.**
  - `x <= x' + ε1`, monotonicity and linearity on `C*(1, x')` give `|τ(x) − τ(x')| <= ||x − x'||`, hence `|D(x,z) − D(x',z')| <= 2(||x−x'|| + ||z−z'||)`.
  - Every self-adjoint element lies in a MASA `C(X)` with `X` Stonean, hence totally disconnected, so finite-spectrum positive elements are dense. Correct.
- **Step 2.** The `q_j` are orthogonal, so they commute and `τ(b') = Σ β_j τ(q_j)`. The telescoping identity is exact, and some term is nonzero. Correct.
- **Step 3.**
  - `D(c1, βq) = 0` by linearity on `C*(1, q)`, so `k >= 2`.
  - The shift preserves `D` by linearity on `C*(1, w)`.
  - **Wording note.** The spectral projections `e_i` must belong to **distinct** eigenvalues so that `δ_i = γ_i − γ_k > 0`. That is automatic for a spectral decomposition, but it should be said.

## 2. Steps 4 and 5

**Step 4, the dilation.**
- `P`, `A = Σ λ_i e_i` and `S = (A − A²)^(1/2)` commute, and `SP = S`.
- `p'` is self-adjoint, and:
  - `(p'²)_11 = A² + S² = A`;
  - `(p'²)_12 = AS + S(P − A) = SP = S`;
  - `(p'²)_22 = S² + (P − A)² = A − A² + P − 2A + A² = P − A`.
  So `p'` is a projection.
- `pp'p = diag(PAP, 0) = diag(A, 0)`. Its spectrum is `{0} ∪ {λ_i : i < k}`, since `e_k ≠ 0` gives the eigenvalue `0`.
- With continuous `g`, `g(0) = 0` and `g(λ_i) = δ_i`, we get `g(diag(A,0)) = diag(y, 0)`. So `y ⊕ 0 ∈ C*(p, p')` and `q^ = q ⊕ 0 ∈ B`. Correct.

**Step 5, the pullback.**
- **The quasitrace `τ~`.** Put `τ~(w) = τ_4(w ⊗ e_11)` on `M_2(M)`, where `e_11` is the outer matrix unit of `M_4(M) = M_2(M_2(M))`. It satisfies Gow Definition 2.20:
  - `τ~(x*x) = τ~(xx*) >= 0`;
  - `τ~(a + ib) = τ~(a) + iτ~(b)`;
  - it is linear on abelian subalgebras, because `w ↦ w ⊗ e_11` is a *-homomorphism.
  `τ_4` itself witnesses that `τ~` is a 2-quasitrace.
- **Normalization.** `e_11 ⊗ e_11 = e_11` in `M_4`, so `τ~(z ⊕ 0) = τ_4(z ⊗ e_11) = τ(z)`. `τ~(1) = 2`, because the two diagonal corners are equivalent commuting projections.
- **The defect transfers.** `τ~((y + βq) ⊕ 0) − τ~(y ⊕ 0) − βτ~(q^) = D(y, βq) ≠ 0`, using homogeneity on `C*(q^)`.
- **Restriction and pullback.** Restricting to `B = C*(1, p, p', q^)` preserves being a 2-quasitrace. The unital full free product `C² * C² * C²` gives the unital surjection `π : P_3 → B` with `r_1 ↦ p`, `r_2 ↦ p'`, `r_3 ↦ q^`, and `σ = τ~ ∘ π` is a 2-quasitrace (use `M_2(π)` for the extension).
- **Boundedness.** `σ(w) <= ||w|| σ(1)` for `w >= 0`, by linearity on `C*(1, w)`.
- **The defect in `P_3`.** `π(g(r_1r_2r_1)) = g(pp'p) = y ⊕ 0`, since a unital *-homomorphism commutes with continuous functional calculus, and `π(βr_3) = βq^`. So `σ(g(r_1r_2r_1) + βr_3) ≠ σ(g(r_1r_2r_1)) + βσ(r_3)`. Correct.

**Sharpness and the remarks.**
- `C*(D_∞)` is nuclear because `D_∞` is amenable. Its quotients are exact, so Haagerup's theorem applies.
- `F_2` does not surject onto `Z_2*Z_2*Z_2`, because `(Z/2)³` is not 2-generated.
- `Z_2*Z_2*Z_2` does not surject onto `F_2`: involutions map to torsion, and `F_2` is torsion-free.
- The Attempts note that `P_3` is not exact is correct: `C*(F_2) ⊆ C*(Z_2*Z_2*Z_2)` through a finite-index free subgroup, and exactness passes to subalgebras.

## 3. Removing Blackadar–Handelman Corollary II.1.10

Only a 2-quasitrace `τ~` on `M_2(M)` with `τ~(z ⊕ 0) = τ(z)` is needed. It can be obtained from the uniqueness clause of Gow Theorem 2.22 alone.
- `M_2(M)` and `M_4(M)` are type II_1 AW*-factors (matrix algebras over AW*-algebras are AW*, standard, not re-read). Let `τ_(2)` and `τ_(4)` be their canonical quasitraces.
- `z ↦ 2τ_(2)(z ⊕ 0)` satisfies properties (i)–(ix) of Theorem 2.22 on `M`. For (vi), `τ_(2)(1 ⊕ 0) = 1/2`. For (ix), `p ↦ 2D_(2)(p ⊕ 0)` is a normalized dimension function on `M`, and that is unique. By uniqueness, `τ = 2τ_(2)(· ⊕ 0)`.
- Likewise `τ_(2) = 2τ_(4)(· ⊗ e_11)`.
- So `τ~ := 2τ_(2)` has the 2-quasitrace extension `4τ_(4)`, with `4τ_(4)(w ⊗ e_11) = τ~(w)` and `τ~(z ⊕ 0) = τ(z)`.

This would replace (I3) by (I2) plus the AW* matrix fact. The lane may choose either.

## 4. Source verification

**Gow**, arXiv:2601.04431v2, fetched on MSI 2026-09-12 and extracted with ghostscript. Ligatures restored.
- **Theorem A = Theorem 4.11.** "The following are equivalent: (i) Every Type II_1 AW*-factor is a Type II_1 W*-factor. (ii) Any 2-quasitrace on a unital C*-algebra is a trace. …" The text before it says: "Blackadar and Handelman [11] proved that Kaplansky's Conjecture is equivalent to the following. Conjecture 1.2 (2Q)." This matches (I1).
- **Section 1.** "While it is known that any Type II AW*-factor that admits a faithful state is a W*-algebra (see [57] for the Type II_1 case; [14] for the Type II case)…". Here `[57]` is J. D. M. Wright, *On AW*-algebras of finite type*, J. London Math. Soc. (2) 12 (1975/76), no. 4, 431–439. This matches (I4) as quoted, with hypothesis "faithful state", not "faithful normal state".
- **Theorem 2.22.** "[20, Theorem 1.27] Let A be a finite AW*-algebra. There exists a unique function τ : A → Z(A) satisfying …", followed by properties (i)–(ix). This matches (I2).
- **After Theorem 2.22.** "By a result of Blackadar and Handelman [11, Corollary II.1.10], every 1-quasitrace on an AW*-algebra is a 2-quasitrace (hence an n-quasitrace)…". This matches (I3). Gow also records Blackadar–Handelman Proposition II.4.1: a 2-quasitrace extends to an `n`-quasitrace.

**Primary sources: not obtained.**
- **Blackadar–Handelman**, J. Funct. Anal. 45 (1982) 297–340, DOI 10.1016/0022-1236(82)90009-X. The DOI resolves to ScienceDirect. Both the `pdfft` and the `/pdf` endpoints returned an 832 KB JavaScript application shell, not article text; parsing it found no "1.10" and no abstract. Unpaywall lists no open-access copy.
- **Wright**, J. London Math. Soc. (2) 12 (1975/76) 431–439, DOI 10.1112/jlms/s2-12.4.431. Wiley returned a 265-byte blocked response, and Unpaywall lists no open-access copy.

Checking these two statements from the primaries needs library or browser access. Until then they are quoted through Gow, as the artifact already says.
