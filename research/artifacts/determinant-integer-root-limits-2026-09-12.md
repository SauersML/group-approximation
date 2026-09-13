# Integer-matrix spectral limits are exactly the Galois-balanced Serre class

Lane `ex-determinant-monster`, 2026-09-12. Written proofs, no machine
verification, unreviewed. Uses A. Smith, arXiv:2111.12660v2, Theorem 1.5,
quoted verbatim in `research/artifacts/determinant-spectral-atoms-2026-09-12.md`
Section 0 (below: [SA]), and
`research/artifacts/determinant-conjecture-serre-class-2026-09-11.md` (below: [SC]).

## 1. Definitions

For a monic `P ∈ Z[x]`, `μ_P` is the uniform probability measure on its roots,
with multiplicity.

- **IR (integer root limits).** `μ` is in `IR` if there are `C > 0` and monic
  `P_k ∈ Z[x]` whose roots are all real and lie in `[−C, C]`, with `μ_(P_k) → μ`
  weakly. Equivalently, `μ` is a weak limit of normalized eigenvalue
  distributions of integer matrices with real spectrum in `[−C, C]`: their
  characteristic polynomials are monic integral, and companion matrices realize
  every such `P`.
- **S (Serre class).** Compactly supported probability measures with
  `∫_(Q≠0) log|Q| dμ ≥ 0` for every nonzero `Q ∈ Z[x]` ([SA] Section 1).
- **GB (Galois balanced).** Every atom of `μ` at an algebraic number is a
  totally real algebraic integer, and all its conjugates carry the same mass.
- **S'(Σ) (Smith class).** Probability measures on a compact `Σ ⊂ R` with
  `∫_Σ log|Q| dμ ≥ 0` for every nonzero `Q ∈ Z[x]`, the integral running over
  zeros of `Q` too. Such measures have no atoms at algebraic numbers.

## 2. Theorem

**Theorem.** A compactly supported probability measure `μ` on `R` lies in `IR`
if and only if it lies in `S ∩ GB`.

### 2.1 IR ⊆ S

This is [SC] Theorem 2 with "symmetric integer matrix" replaced by "monic
integer polynomial with real roots". The only arithmetic input there is that,
for nonzero `Q ∈ Z[x]`,

```text
∏_(P(λ)=0, Q(λ)≠0) Q(λ)      (with multiplicity)
```

is a nonzero integer. It is, up to sign, the lowest nonzero coefficient of the
characteristic polynomial of `Q(B)`, where `B` is the companion matrix of `P`,
an integer matrix. The rest of that proof, portmanteau at the zero set of `Q`
and monotone convergence of `log max(|Q|, δ)`, is unchanged.

### 2.2 IR ⊆ GB

Let `μ_k = μ_(P_k) → μ` as in the definition, and let `α` be algebraic, with
primitive irreducible minimal polynomial `M ∈ Z[x]` of degree `d`.

1. **Factor.** Write `P_k = M^(e_k) S_k` with `M ∤ S_k`. If `M` is not monic, or
   has a non-real root, then `e_k = 0`: by Gauss's lemma a primitive factor of
   a monic integer polynomial is monic, and `P_k` has only real roots. Put
   `c_k = e_k d / deg P_k`, so `μ_k = c_k ν_M + (1 − c_k) μ_(S_k)`, where
   `ν_M` is uniform on the roots of `M`.
2. **Resultant.** `S_k` is monic and coprime to `M`, so
   `∏_(S_k(β)=0) M(β) = ±Res(S_k, M)` is a nonzero integer. With
   `B = max(1, sup_[−C,C] |M|)`, the mean of `log|M|` over the roots of `S_k` is
   at least `0` and each term is at most `log B`. So for `0 < δ < 1`

   ```text
   μ_(S_k)({|M| < δ}) ≤ log B / log(1/δ) =: ε(δ).
   ```
3. **Neighbourhoods.** For small `δ`, `{x ∈ [−C,C] : |M(x)| < δ}` is a disjoint
   union of small open intervals `U_i(δ)`, one around each real root `α_i` of
   `M` in `[−C, C]`, shrinking to `α_i` as `δ → 0`. Then
   `c_k/d ≤ μ_k(U_i(δ)) ≤ c_k/d + ε(δ)`.
4. **Limit.** By the portmanteau theorem, for `δ' < δ`,

   ```text
   limsup_k c_k/d ≤ μ(closure U_i(δ')) ≤ μ(U_i(δ)) ≤ liminf_k c_k/d + ε(δ).
   ```

   Letting `δ, δ' → 0`: `c_k → c` and `μ({α_i}) = c/d` for every real root
   `α_i` of `M` in `[−C, C]`.
5. **Conclusion.** If `α` is not an algebraic integer, or has a non-real
   conjugate, then `c_k = 0` and `μ({α}) = 0`. Otherwise all conjugates lie in
   `[−C, C]` whenever `c > 0`, and they carry the same mass `c/d`. ∎

### 2.3 S ∩ GB ⊆ IR

Let `μ ∈ S ∩ GB` be supported in `[−C, C]`. Put `Σ = [−R, R]` with
`R > max(C, 2)`, so `cap(Σ) = R/2 > 1`.

**Step 1 (decomposition).** By GB, `μ = Σ_O w_O ν_O + μ'`, a countable sum over
totally real Galois orbits `O ⊂ Σ` of algebraic integers, `ν_O` uniform on `O`,
and `μ'` without atoms at algebraic numbers. Write `M_O` for the minimal
polynomial of `O`, and `W_F = Σ_(O ∉ F) w_O` for a finite set `F` of orbits.

**Step 2 (μ' obeys Smith's inequalities).** Fix nonzero `Q_0 ∈ Z[x]`, a finite
set `F` of orbits, and `k ≥ 1`, and put `Q = Q_0^k ∏_(O∈F) M_O`.
- For an orbit `O ∉ F` on which `Q` does not vanish, the orbit term
  `(1/|O|) Σ_(α∈O) log|Q(α)| = log|N(Q(α))| / |O|` is `≥ 0`, since `Q(α)` is a
  nonzero algebraic integer, and at most `log ||Q||_Σ`.
- `μ'` has no atoms at zeros of `Q`, so its part of the Serre integral is
  `∫ log|Q| dμ'`.
- The Serre inequality for `Q` therefore gives

  ```text
  k ∫ log|Q_0| dμ' + Σ_(O∈F) ∫ log|M_O| dμ'
     ≥ −W_F · ( k·max(0, log||Q_0||_Σ) + Σ_(O∈F) max(0, log||M_O||_Σ) ).
  ```
- Each `∫ log|M_O| dμ'` is finite, being at least `−log||M_O||_Σ` by the Serre
  inequality for `Q = M_O`. Divide by `k` and let `k → ∞`:
  `∫ log|Q_0| dμ' ≥ −W_F max(0, log||Q_0||_Σ)`.
- Let `F` exhaust the orbits, so `W_F → 0`: `∫ log|Q_0| dμ' ≥ 0`.

**Step 3 (Smith).** If `μ' ≠ 0`, then `μ'' = μ'/μ'(R)` is a probability measure
on `Σ` obeying condition (1) of Smith's Theorem 1.5. `Σ` is compact with one
component and capacity above `1`. So there are distinct irreducible monic
`R_j ∈ Z[x]` with all roots in `Σ` and `μ_(R_j) → μ''`.

**Step 4 (rational mixing).** Choose finite sets `F_N` exhausting the orbits,
positive rationals `r_(O,N)` for `O ∈ F_N` and `r'_N ≥ 0` summing to `1`, with
`r_(O,N) → w_O` and `r'_N → μ'(R)`, and indices `j_N → ∞`. The measure

```text
μ_N = Σ_(O∈F_N) r_(O,N) ν_O + r'_N μ_(R_(j_N))
```

is `μ_P` for a monic integer polynomial with all roots in `Σ`: if the weights are
`p_i / D` on irreducible `P_i`, take `P = ∏ P_i^(e_i)` with
`e_i = p_i L / deg P_i` and `L` a common multiple of the degrees. Then
`μ_N → μ` weakly. ∎

## 3. The Serre class is strictly larger

[SA] Examples 4.1 and 4.2 give

```text
μ_1 = ½ δ_(1/2) + ½ arcsine[−4,4],      μ_2 = 0.3 δ_(φ²) + 0.1 δ_(φ^(−2)) + 0.6 arcsine[−6,6],
```

both in `S` and neither in `GB`, hence neither in `IR`. So the converse posed as
`serre-class-measures-are-integral-spectral-limits` fails, already for integer
matrices with real spectrum and so for symmetric ones. The theorem of Section 2
is the correct converse: add balance, and drop symmetry.

## 4. Consequences for groups

For a group `G`:
- `ISA_Z(G)`: every self-adjoint `A ∈ M_n(Z[G])` has `μ_A ∈ IR`.
- `GB(G)`: every eigenvalue of every such `A` is a totally real algebraic
  integer, and conjugate eigenvalues have equal von Neumann multiplicity.
- `Det(G)`: Lück's determinant conjecture for `G`, equivalently `μ_A ∈ S` for
  all `A` ([SC] Theorem 1).

**Corollary.** `ISA_Z(G) ⟺ Det(G) ∧ GB(G)`.

*Proof.* `μ_A ∈ GB` for all `A` is `GB(G)`. Apply the Theorem to each `μ_A`. ∎

- **Sofic groups** have all three: Elek--Szabó for `Det`, Thom
  (arXiv:math/0701294v3, Theorem 1.1) for `GB`, and sofic models of `A` are
  integer matrices.
- **`Det(G)` alone** forces algebraic eigenvalues of multiplicity at most
  `n / deg` ([SA] Corollary 2). It does not force `GB` one measure at a time
  (Section 3). Whether `Det` for all groups implies `GB` for all groups is not
  settled here.
- **Symmetric approximants.** `integral-group-ring-spectra-are-integral-limits`
  implies `ISA_Z(G)`. The converse would need totally real orbits realized by
  symmetric integer matrices with negligible extra spectrum; not settled here.

## 5. Thom's question

After Theorem 5.4, Thom writes: "It would be very interesting to characterize the
continuous parts of the spectral distribution function intrinsically."

- **Thom's integer operators sit inside IR.** Definition 5.1 uses normal integer
  matrices. Sections 2.1 and 2.2 go through verbatim for monic integer
  polynomials with complex roots in a compact set, when the limit is supported
  on `R`: Serre's product is still a nonzero integer, and in Step 2.2.1 a
  non-real conjugate forces `c_k → 0`, because the limit gives no mass near
  non-real points. So spectral measures of self-adjoint integer operators lie in
  `S ∩ GB = IR`.
- **The answer for IR.** Write `μ = Σ_O w_O ν_O + μ'` as in Step 1, with balanced
  totally real orbit atoms. Then `μ ∈ IR` iff

  ```text
  ∫_R log|Q| dμ' ≥ 0     for every nonzero Q ∈ Z[x].
  ```

  - Necessity is Step 2.
  - Sufficiency: for `Q ≠ 0`, the Serre integral of `μ` is a nonnegative sum of
    orbit terms plus `∫ log|Q| dμ' ≥ 0`, so `μ ∈ S ∩ GB`.

  By [SA] Theorem 1 such a `μ'` has no atoms at all, so it is the continuous part
  of the distribution function. This is the intrinsic characterization for
  limits of integer matrices with real spectrum, through Smith's inequalities.
- **Gap.** For Thom's class itself, sufficiency needs normal integer
  approximants. The last paragraph of Section 4 records that this realization
  is not settled.
