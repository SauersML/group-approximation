# Atoms of integral spectral measures under the determinant conjecture

Lane `ex-determinant-monster`, 2026-09-12. Written proofs, no machine
verification, unreviewed. Continues
`research/artifacts/determinant-conjecture-serre-class-2026-09-11.md`
(below: [SC]).

## 0. Sources read in this session

PDFs fetched from arXiv on MSI and read page by page.

- **A. Smith**, *Algebraic integers with conjugates in a prescribed
  distribution*, arXiv:2111.12660v2 (16 Mar 2024), page 4.

  > **Theorem 1.5.** Take `Σ` to be a compact subset of `R` with at most
  > countably many components. We assume that `Σ` has capacity strictly larger
  > than 1 (see Definition 2.1). Then, for any Borel probability measure `μ`
  > with support contained in `Σ`, the following two conditions are
  > equivalent:
  > (1) For every nonzero integer polynomial `Q`, `∫_Σ log|Q(x)| dμ(x) ≥ 0`.
  > (2) There is an infinite sequence of distinct irreducible monic integer
  > polynomials `R_1, R_2, ...` such that the support of `μ_(R_k)` is
  > contained in `Σ` for every `k` and such that `μ_(R_1), μ_(R_2), ...` has
  > weak* limit `μ`.

  Here `μ_P` is the uniform measure on the roots of `P` (Definition 1.4), and
  the integral in (1) runs over all of `Σ`, zeros of `Q` included. Smith
  attributes (2) ⇒ (1) to Serre.

- **A. Thom**, *Sofic groups and diophantine approximation*,
  arXiv:math/0701294v3 (29 Jan 2007), pages 1, 8--12.

  > **Theorem 1.1.** Let `Γ` be a sofic group and `A ∈ M_n(ZΓ)`. [...]
  > (i) All eigenvalues of the `λ(A)` are algebraic integers.
  > (ii) If `α ∈ C` is an eigenvalue of the operator `λ(A)`, then all its
  > Galois conjugates are also eigenvalues and the corresponding eigenspaces
  > have the same von Neumann dimension.

  > **Definition 5.1.** [...] A normal operator `a ∈ M` is called integer, if
  > its spectral measure can be approximated weakly by the spectral measures
  > of uniformly operator-norm bounded sequence of normal integer matrices.

  > **Theorem 5.4.** Let `(M,τ)` be a finite von Neumann algebra and `A = A*`
  > an integer operator in `M`. The distribution function of the spectral
  > measure of `A` is a sum of (i) a step function `R^a_A` with jumps at a
  > full set of conjugates of totally real integer algebraic integers, and
  > (ii) a continuous function `R^c_A` which is the uniform limit of
  > distributions of convex combinations of measures `μ_(α_i)`, where `α_i` is
  > a totally real algebraic integer.

  Directly after it: "It would be very interesting to characterize the
  continuous parts of the spectral distribution function intrinsically."

  > **Theorem 6.1.** [...] (ii) If `A = A*`, then either `||A|| ≥ 2`, or
  > `||A|| = 2cos(π/q)`, for some natural number `q ∈ N`. Moreover, in this
  > case the spectral measure is completely atomic and the atoms occur at
  > positions `2cos(πp/q)`, for natural numbers `p ∈ N`.

  > **Corollary 6.5.** [...] `A = A* ∈ M` an integer operator. Either,
  > (i) `||A|| = 1` and `A^2` is a projection, or (ii) `||A|| ≥ sqrt 2`.

  Introduced with: "an easy corollary of the quantization theorem, for which
  we do not know any elementary proof."

- **W. Lück**, *Lehmer's problem for arbitrary groups*, arXiv:1901.00827v2
  (16 Sep 2020), page 5, Remark 4.2 (Status of the Determinant Conjecture).
  The class `D` of groups satisfying the conjecture is closed under
  (1) amenable quotients (`H ⊴ G`, `H ∈ D`, `G/H` amenable), (2) directed
  colimits with not necessarily injective structure maps, (3) inverse limits,
  (4) subgroups, (5) quotients with finite kernel, and (6) contains the sofic
  groups. The paper adds: "One expects that there exists non-sofic groups but
  no example is known." No hyperlinear or other non-approximation case is
  listed.

## 1. Notation

`S` is the **Serre class**: compactly supported probability measures `μ` on
`R` with `∫_(Q≠0) log|Q| dμ ≥ 0` for every nonzero `Q ∈ Z[x]`. For a group
`G` and self-adjoint `A ∈ M_n(Z[G])`, `μ_A` is the spectral measure of `A` for
the normalized trace `(1/n) Tr ⊗ τ`, so
`μ_A({λ}) = dim_(N(G)) ker(r_A − λ) / n`. By [SC] Theorem 1
(`determinant-conjecture-iff-serre-class-spectra`), `G` satisfies Lück's
determinant conjecture iff `μ_A ∈ S` for all such `A`, and for every nonzero
`Q ∈ Z[x]`

```text
log det_(N(G)) r_(Q(A)) = n · ∫_(Q≠0) log|Q| dμ_A.          (FC)
```

`deg(x) = [Q(x):Q]`, with `deg(x) = ∞` for transcendental `x`.

## 2. Theorem 1: atoms of Serre-class measures

**Theorem 1.** Let `μ ∈ S`. Then `μ({x}) ≤ 1/deg(x)` for every `x ∈ R`. In
particular every atom of `μ` is algebraic.

*Proof.* Let `μ` be supported in `[−C, C]` with `C ≥ 1`, and let
`w = μ({x}) > 0`; then `|x| ≤ C`. Fix an integer `N ≥ 1` with `N < deg(x)`.

1. **Box principle.** For an integer `H ≥ 1`, the `(H+1)^(N+1)` vectors
   `a ∈ {0,...,H}^(N+1)` give values `L(a) = Σ_(i≤N) a_i x^i` in an interval of
   length `H s`, `s = Σ_(i≤N) |x|^i ≤ (N+1) C^N`. Cutting it into
   `(H+1)^(N+1) − 1 ≥ H^(N+1)` equal pieces, two distinct vectors land in one
   piece. Their difference is a nonzero `Q ∈ Z[x]` with `deg Q ≤ N`, all
   coefficients of absolute value at most `H`, and `|Q(x)| ≤ s H^(−N)`.
2. **`Q(x) ≠ 0`,** because `deg Q < deg(x)`.
3. **Bound on the support.** On `[−C, C]`, `|Q| ≤ B_H := (N+1) H C^N`, and
   `B_H ≥ 1`.
4. **Estimate.** The atom at `x` lies in `{Q ≠ 0}` and contributes
   `w log|Q(x)| ≤ w log s − w N log H`. The rest of `{Q ≠ 0}` has mass at
   most `1 − w` and integrand at most `log B_H ≥ 0`. So

   ```text
   0 ≤ ∫_(Q≠0) log|Q| dμ ≤ −(w(N+1) − 1) log H + w log s + (1−w) log((N+1)C^N).
   ```
5. **Conclusion.** Letting `H → ∞` forces `w(N+1) ≤ 1`. If `deg(x) = d` is
   finite, take `N = d − 1`: `w ≤ 1/d`. If `x` is transcendental, `N` is
   arbitrary, so `w = 0`. ∎

**Sharpness.** The uniform measure on a Galois orbit of `d` totally real
algebraic integers lies in `S` ([SC] Theorem 5) and has mass exactly `1/d` at
each conjugate. So `1/deg(x)` is the best one-variable bound.

## 3. Corollary: heavy eigenvalues are determinant counterexamples

**Corollary 2.** Let `G` be any group, `A ∈ M_n(Z[G])` self-adjoint, `λ ∈ R`,
and `m = dim_(N(G)) ker(r_A − λ)`. Suppose `m > n / deg(λ)`, which for
transcendental `λ` means `m > 0`. Then there is a nonzero `Q ∈ Z[x]` with

```text
det_(N(G)) r_(Q(A)) < 1.
```

Explicitly: take `N = deg(λ) − 1` (any `N` with `(N+1) m > n` if `λ` is
transcendental), `C = max(1, ||A||)`, and `H` with

```text
(w(N+1) − 1) · log H  >  log((N+1) C^N),        w = m/n,
```

and let `Q` be the box-principle polynomial of Theorem 1 at `x = λ`.

*Proof.* `μ_A` has the atom `w = m/n > 1/deg(λ)` at `λ`. Step 4 of Theorem 1
gives `∫_(Q≠0) log|Q| dμ_A < 0` for this `H`, and (FC) turns it into
`log det r_(Q(A)) < 0`. ∎

**Consequence.** If `G` satisfies the determinant conjecture, then every
eigenvalue of every self-adjoint `A ∈ M_n(Z[G])` is algebraic, and

```text
dim_(N(G)) ker(r_A − λ)  ≤  n / deg(λ).
```

This is an approximation-free half of Thom's Theorem 1.1 for self-adjoint
integral matrices: algebraicity, with the multiplicity bound that Galois
balance would give. It does not give integrality or balance (Section 4).

**Literature check (bounded).** Thom 2007 proves algebraicity for sofic groups
through sofic approximation. Lück 2020, Remark 4.2 lists no implication from
the determinant conjecture to eigenvalues. The repository's
`galois-invariance-implies-algebraic-eigenvalues` derives algebraicity from
invariance under automorphisms of `C`. The derivation from the Serre
inequalities alone was not found in these sources; nothing wider was searched.

## 4. What the Serre class does not force

Let `ω_R` be the arcsine (equilibrium) measure of `[−R, R]`, of capacity
`R/2`. Write `ζ = (R/2)(u + 1/u)` with `|u| ≥ 1`. Its potential is

```text
U_R(ζ) = ∫ log|ζ − t| dω_R(t) = log(R|u|/2) ≥ log(max(R, |ζ|)/2).
```

So for nonzero `Q = c ∏_j (t − z_j) ∈ Z[t]`:

```text
I_R(Q) := ∫ log|Q| dω_R = log|c| + Σ_j U_R(z_j) ≥ deg(Q) · log(R/2).     (P)
```

**Example 4.1 (a rational non-integral atom).**
`μ = ½ δ_(1/2) + ½ ω_R` with `R ≥ 4` lies in `S`.

*Proof.* Let `Q ≠ 0`.
- If `Q(1/2) = 0`, then `∫_(Q≠0) log|Q| dμ = ½ I_R(Q) ≥ 0` by (P).
- Otherwise `2^(deg Q) Q(1/2)` is a nonzero integer, so
  `log|Q(1/2)| ≥ −deg(Q) log 2`, and
  `∫_(Q≠0) log|Q| dμ ≥ ½ deg(Q) (log(R/2) − log 2) = ½ deg(Q) log(R/4) ≥ 0`. ∎

**Example 4.2 (Galois-unequal atoms).** With `α = φ^2 = (3+√5)/2`,
`α' = φ^(−2)`, the measure `μ = 0.3 δ_α + 0.1 δ_(α') + 0.6 ω_6` lies in `S`.

*Proof.* For `|z| ≤ 3` and any `ζ`, `3 + |ζ| ≤ 2 max(6, |ζ|)`, so
`log|z − ζ| ≤ log(3 + |ζ|) ≤ 2 log 2 + log(max(6,|ζ|)/2) ≤ 2 log 2 + U_6(ζ)`.
Hence `log|Q(z)| ≤ I_6(Q) + 2 deg(Q) log 2` for `|z| ≤ 3`. Let `Q ≠ 0`.
- If `Q(α) = 0`, then `Q(α') = 0` and the value is `0.6 I_6(Q) ≥ 0`.
- Otherwise put `u = log|Q(α)|`, `v = log|Q(α')|`. Then
  `u + v = log|N(Q(α))| ≥ 0` and `v ≤ I_6(Q) + 2 deg(Q) log 2`. So

  ```text
  0.3u + 0.1v + 0.6 I_6 = 0.1(u+v) + 0.2u + 0.6 I_6
                       ≥ −0.2 v + 0.6 I_6 ≥ 0.4 I_6 − 0.4 deg(Q) log 2
                       ≥ 0.4 deg(Q) log(3/2) ≥ 0,
  ```

  using `I_6(Q) ≥ deg(Q) log 3` from (P). ∎

**Reading.** Over any group, the determinant conjecture read one measure at a
time forces algebraic atoms with `μ({λ}) ≤ 1/deg λ` (Theorem 1), and nothing
more about atoms. Integrality of eigenvalues and equal conjugate
multiplicities, which sofic groups have (Thom, Theorem 1.1), are extra
structure. The next landing of this lane shows, through Smith's Theorem 1.5,
that this extra structure is exactly what separates the Serre class from
limits of integer-matrix spectra.
