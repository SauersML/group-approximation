# Referee report (gq-referee-a, proof-gap lens): infinitely q-divisible DVR matrices are torsion

**Reviewed:** lane gq-infinite-primes, read on origin/main.
- `infinitely-q-divisible-dvr-matrices-are-torsion` with its route `-proof` (4cff6464a);
- `infinite-prime-localizations-embed-in-no-fg-linear-group` with its route `-proof` (39b37d26f).

**Verdict: PASS for both.** No gaps found.

## 1. The DVR lemma
- **Step 1.** `y = I + π^s X`, so `y^q = I + Σ_i C(q,i) π^{si} X^i`.
  - For `0 < i < q`, `q | C(q,i)`, and `v(q) = e ≥ 1`, which is finite since the characteristic is 0.
    So these terms lie in `π^{s+1}`.
  - The term `i = q` lies in `π^{sq}`, and `sq ≥ 2s ≥ s+1`.
  - So `y^q ∈ Γ_{s+1}`. Correct.
- **Step 2.**
  - Unipotents in characteristic `q` die at `q^{e_0} ≥ N`. So `ḡ = s_j^{q^j}` is semisimple.
  - `q`-power roots are unique in characteristic `q`, so the `μ_j` form a compatible system in
    fields of degree `≤ N` over `k`, which stabilize at a finite `k'`.
  - `∩_j k'^{q^j}` is perfect. Algebraic subextensions of a finitely generated field are finite, so a
    transcendental element would give an infinite purely inseparable tower inside `k'`. Hence the
    intersection is algebraic over `F_q`, so it is finite.
  - So every `λ` is a root of unity of order prime to `q`, and `ḡ^M = I`.
  - Correct.
- **Step 3.** `h̄_j^M` is unipotent, so `y_j = h_j^{M q^{e_0}} ∈ Γ_1`, and `y_j^{q^{j−e_0}} = g^M`. By
  Step 1, `g^M ∈ Γ_{1+j−e_0}` for every `j`, so `g^M = I`. Correct.

## 2. `Z[1/P]` embeds in no finitely generated linear group
- **Characteristic 0, (a).** Noether normalization and clearing denominators give `D` with
  `A[1/D]` integral over the UFD `R = Z[1/D][x]`. A unit `1/q` with `q ∤ D` would be in `R`, which is
  false. Correct.
- **Characteristic 0, (b).** Correct.
  - The Gauss valuation ring `R_(q)` is a DVR containing `R`, with residue field `F_q(x)`.
  - The integral closure in the finite separable `K = Frac(A)` is Dedekind. Localizing it at a prime
    over `q` gives a DVR `O ⊇ A`, with `q ∈ m_O` and finitely generated residue field.
- **Characteristic 0, (c).** Correct. `g` and the `h_j` lie in `GL_N(A) ⊆ GL_N(O)`, because `A`
  contains the entries of the generators' inverses. So the lemma applies.
- **Characteristic p, the setup.**
  - `g' = g^{p^{e_0}}` is semisimple of infinite order, so some eigenvalue `λ` is not a root of unity.
    Hence `λ` is transcendental over `F_p`.
  - The `λ`-adic valuation of `F_p(t_2..t_d)(λ)` extends to a discrete valuation `w` of `F_0 = K(λ)`
    with `w(λ) = c ≥ 1`.
- **Characteristic p, the contradiction.**
  - `[F_0(β_j) : F_0] ≤ [K(β_j) : K] ≤ N`, since `λ = β_j^{q^j} ∈ K(β_j)`.
  - So `e(w_j/w) ≤ N`, the value group lies in `(1/N!)Z`, and `q^j | c·N!` for every `j`. That is
    impossible, even for `q = p`. Correct.
- **Consequence 2 (products).** Correct. Nonzero subgroups of a rank-one torsion-free group meet
  nontrivially, so finitely many nonzero kernels cannot intersect trivially.
