---
rg: 2
id: kt-compressor-commutant-collapse-all-or-nothing-proof
kind: route
title: Saturate the Gamma-commutant and apply the compressor-stable subring dichotomy
target: kt-compressor-commutant-collapse-is-all-or-nothing
requires: []
artifacts:
  - research/artifacts/kt-commutant-all-or-nothing-2026-09-16.md
---

The proof is self-contained, and every step is elementary algebra. Notation
is as in the target. `e_kl(f)=I_r+f E_kl` and `U_kl(R)={e_kl(f) : f in R}`.
`[a,b]=a b a^(-1) b^(-1)`. `C_U(X)` is the centralizer of a subset `X` of `U`.

**Convention.** `SL_d(Z)` acts on `R` by `beta_L(x^n)=x^(Ln)`, so
`beta_(LL')=beta_L beta_(L')`. In `G`, `L u L^(-1)` is `beta_L` applied
entrywise, so `L e_kl(f) L^(-1)=e_kl(beta_L f)`. If a source uses a transposed
or inverted convention, replace `L` by the matrix of its exponent map. Every
statement below refers only to the set of exponent maps preserving `N^d`, and
that set does not depend on the convention.

## 1. Saturation

Put

```text
N_pi     = {g in G : pi(g) C_0 pi(g)^(-1) = C_0},
Gamma^sat = {g in G : pi(g) c = c pi(g) for all c in C_0}.
```

Both are subgroups of `G`.

**(G1)** For every `g in G`,
`C_U(pi(g Gamma g^(-1)))=pi(g) C_0 pi(g)^(-1)`. This follows by conjugating
the defining commutation relations. Hence condition (1) of the target is the
statement `t in N_pi`, and (2) is `P_Gamma subset N_pi`.

**(G2)** `Gamma <= Gamma^sat <= N_pi` and `C_0=C_U(pi(Gamma^sat))`.

- The first inclusion holds by definition of `C_0`.
- If `pi(g)` commutes with `C_0`, then conjugation by `pi(g)` fixes `C_0`
  pointwise, which gives the second inclusion.
- `C_U(pi(Gamma^sat))` is contained in `C_U(pi(Gamma))=C_0`, because
  `Gamma <= Gamma^sat`.
- `C_0` is contained in `C_U(pi(Gamma^sat))` by definition of `Gamma^sat`.

**(G3)** `N_pi=N_G(Gamma^sat)`.

- Let `g in N_pi`, `k in Gamma^sat` and `c in C_0`. Then
  `pi(g)^(-1) c pi(g) in C_0`, so it commutes with `pi(k)`. Conjugating back,
  `pi(g k g^(-1))` commutes with `c`. So `g Gamma^sat g^(-1) <= Gamma^sat`.
  The same holds for `g^(-1)`.
- Conversely, suppose `g` normalizes `Gamma^sat`. Then
  `pi(g) C_0 pi(g)^(-1)=C_U(pi(g Gamma^sat g^(-1)))=C_U(pi(Gamma^sat))=C_0`,
  by (G2).

**(G4)** `A_d <= N_pi`. Each `P in A_d` permutes the variables, so
`beta_P(R_+)=R_+`, `P Gamma P^(-1)=Gamma`, and (G1) gives `P in N_pi`.

**(G5)** Every compressor preserves the saturation: if `g in P_Gamma`, then
`g Gamma^sat g^(-1) <= Gamma^sat`.

- By (G1), `pi(g) C_0 pi(g)^(-1)=C_U(pi(g Gamma g^(-1)))`.
- Since `g Gamma g^(-1) <= Gamma`, this contains `C_0`.
- For `k in Gamma^sat`, `pi(g k g^(-1))` commutes with
  `pi(g) C_0 pi(g)^(-1)`, and therefore with `C_0`.

In particular every `L in SL_d(N)` lies in `P_Gamma`, because
`L Gamma L^(-1)=EL_r(beta_L R_+) <= Gamma`, so `L` preserves `Gamma^sat`.

## 2. The root subring of the saturation

For `k != l` put `S^kl={f in R : e_kl(f) in Gamma^sat}`. Each `S^kl` is an
additive subgroup of `R` containing `R_+`, because
`e_kl(f)e_kl(g)=e_kl(f+g)` and `U_kl(R_+) <= Gamma`.

**(R1) All the `S^kl` coincide.**

- For `i != j` let `w_ij=e_ij(1)e_ji(-1)e_ij(1)`. It lies in
  `EL_r(F_q) <= Gamma <= Gamma^sat` and is a signed permutation matrix for the
  transposition `(i j)`.
- Products of these realize every permutation `p` of `{1,...,r}`, and for such
  a product `w e_12(f) w^(-1)=e_(p(1)p(2))(+-f)`.
- `Gamma^sat` is a group and each `S^kl` is closed under negation, so
  `S^12 subset S^kl`. By symmetry the two are equal.

Write `S` for the common value.

**(R2) `S` is a subring.** It contains `1`. Take `f,g in S`. Since `r>=3`,
the Steinberg relation `[e_13(f),e_32(g)]=e_12(fg)` exhibits `e_12(fg)` as a
commutator of two elements of `Gamma^sat`.

**(R3) `S` is compressor-stable.** For `L in SL_d(N)` and `f in S`, (G5) gives
`e_12(beta_L f)=L e_12(f) L^(-1) in Gamma^sat`, so `beta_L(S) subset S`.

**(R4) If `L in SL_d(Z)` normalizes `Gamma^sat`, then `beta_L(S)=S`.** The
automorphism `beta_L` of `R` maps `U_12(R)` onto itself. So conjugation by `L`
maps `Gamma^sat cap U_12(R)` onto itself.

**(R5) If `S=R`, then `E <= Gamma^sat`.** By (R1), `Gamma^sat` then contains
every `e_kl(f)` with `f in R`, and these generate `E`.

## 3. The subring dichotomy lemma

**Lemma.** Let `d>=3`. Let `S` be a subring with `R_+ <= S <= R` and
`beta_L(S) subset S` for every `L in SL_d(N)`. Then `S=R_+` or `S=R`.

*Proof.* Suppose `f in S \ R_+`. Write `f=f_+ + f_-`, where `f_+` collects
the monomials with exponent in `N^d`. Then `f_- = f - f_+` lies in `S` and is
nonzero. Every exponent in its support lies in `Z^d \ N^d`. Monomials with
distinct exponents never cancel, so only supports matter below.

*Step 1 (a negative first coordinate).* Pick a monomial of `f_-` and a
coordinate `k` where its exponent is negative. Since `A_d` is transitive on
`{1,...,d}` for `d>=3`, there is `P in A_d <= SL_d(N)` with `P e_k=e_1`. Put
`g=beta_P(f_-)`. Then `g in S`, and
`supp g={m^(1),...,m^(s)} subset Z^d \ N^d` contains an exponent with negative
first coordinate. Coefficients `c_j in F_q^x` are attached to the `m^(j)`.

*Step 2 (a lexicographic functional).* Let `M=max_j ||m^(j)||_inf >= 1`,
`K=2M+1`, and `psi(m)=sum_(k=1)^d K^(d-k) m_k`.

- **`psi` orders the box lexicographically.** Take `m != m'` with
  `||m||_inf, ||m'||_inf <= M`. Put `delta=m-m'` and let `k_0` be its first
  nonzero coordinate. Every coordinate satisfies `|delta_k| <= 2M = K-1`, so
  `|sum_(k>k_0) K^(d-k) delta_k| <= K^(d-k_0)-1 < K^(d-k_0)`. Hence
  `psi(delta)` is nonzero with the sign of `delta_(k_0)`.
- **A unique negative minimizer.** Let `m^(j_0)` be the lexicographic minimum
  of `supp g`. It is the unique minimizer of `psi` on the support. Its first
  coordinate is at most the negative first coordinate from Step 1, so it is
  negative. Applying the same estimate to `m^(j_0)` itself gives
  `psi(m^(j_0)) <= -K^(d-1)+(K^(d-1)-1)/2 < 0`.

*Step 3 (a compressor with first row `psi`).* Let `L` be the `d x d` matrix
with rows `psi, e_1^*, e_2^*, ..., e_(d-1)^*`. Expanding along the last column,
`det L=(-1)^(d+1)`.

- If `d` is even, swap rows 2 and 3, which exist since `d>=3`. The new
  determinant is `+1`.
- All entries are nonnegative integers, so `L in SL_d(N)`.
- `L m=(psi(m), m')`, where `m'` is a permutation of `(m_1,...,m_(d-1))`. So
  for `j >= 1` the coordinates `2..d` of `L m^(j)` are at least `-M`.

`beta_L(g)=sum_j c_j x^(L m^(j))` lies in `S`, with pairwise distinct
exponents.

*Step 4 (isolate one monomial).* Let `n=(n_1,M,...,M)` with
`n_1=max(0, max_(j != j_0) -psi(m^(j)))`. Then `x^n` lies in `R_+ <= S`, so
`x^n beta_L(g) in S`.

- For `j != j_0`, the exponent `L m^(j)+n` has first coordinate
  `psi(m^(j))+n_1 >= 0` and all other coordinates `>= 0`. So these monomials
  lie in `R_+`.
- For `j_0`: `n_1` is the maximum of `0` and of the numbers
  `-psi(m^(j))`, `j != j_0`. Each of these is `< -psi(m^(j_0))` by uniqueness
  of the minimizer, and `0 < -psi(m^(j_0))` by Step 2. So
  `n_1 < -psi(m^(j_0))`.
- The first coordinate `-a` of `m^* = L m^(j_0)+n` is therefore negative, and
  its other coordinates `b_2,...,b_d` are `>= 0`.

Subtracting the `R_+` part and dividing by `c_(j_0)` gives `x^(m^*) in S`.

*Step 5 (reach `x_1^(-1)`).* Multiplying by `x_1^(a-1) in R_+` gives
`x^v in S` with `v=(-1,b_2,...,b_d)`. Let `L'=I+sum_(k>=2) b_k E_(k1)`. It is
lower unitriangular with nonnegative entries, so `L' in SL_d(N)`, and
`L' v=v+v_1(0,b_2,...,b_d)=(-1,0,...,0)`. Hence `x_1^(-1)=beta_(L')(x^v)`
lies in `S`.

Transitivity of `A_d` gives `x_k^(-1) in S` for every `k`. A subring
containing `R_+` and every `x_k^(-1)` is `R`. `QED`

The combinatorics of Steps 1-5 (the order property of `psi`,
`det L=1`, nonnegativity, the isolated exponent, and `L' v=-e_1`) were checked
on 9000 random supports for `d=3,4,5` by
`experiments/kt-commutant-all-or-nothing-2026-09-16/subring_lemma_check.py`.
The check is a sanity test only; the proof above does not depend on it.

## 4. The equivalences

Apply the Lemma to the root subring `S` of Section 2. It is a subring by (R2),
contains `R_+`, and is compressor-stable by (R3). Hence

```text
S = R_+   or   S = R.                                            (D)
```

**(1) => (6).** By (G1), (1) says `t in N_pi`. Also `t in SL_d(Z) \ A_d`.

**(6) => (5).** Let `L in (SL_d(Z) cap N_pi) \ A_d`.

- By (G3) and (R4), `beta_L(S)=S`.
- Suppose `S=R_+`. Then `beta_L(R_+)=R_+`. This ring has monomial basis
  `{x^(Ln) : n in N^d}` and also `{x^n : n in N^d}`, so `L N^d=N^d`.
- Then `L` restricts to a linear bijection of the real cone `R_(>=0)^d` onto
  itself, so it permutes the extremal rays. Hence `L e_i=lambda_i e_(p(i))`
  for a permutation `p` and integers `lambda_i >= 1`.
- Since `L^(-1) e_(p(i))=lambda_i^(-1) e_i` is integral, every `lambda_i=1`.
  So `L` is a permutation matrix, and `det L=1` puts it in `A_d`. This is a
  contradiction.
- So `S != R_+`, which gives `f in S \ R_+`, that is, (5).

**(5) => (4).**

- If `pi(e_12(f))` commutes with `C_0` for some `f in R \ R_+`, then
  `f in S \ R_+`. By (D), `S=R`.
- By (R5), `E <= Gamma^sat`. By (G2),
  `C_0=C_U(pi(Gamma^sat)) subset C_U(pi(E)) subset C_U(pi(Gamma))=C_0`.

**(4) => (3).** For `g in G`, `g E g^(-1)=E`, so
`pi(g) C_U(pi(E)) pi(g)^(-1)=C_U(pi(E))`.

**(3) => (2).** Apply (G1) to each `g in G`.

**(2) => (1).** `I+E_12 in SL_d(N) \ A_d` lies in `P_Gamma`.

**(3) => (7) => (6).** (7) is immediate from (3). If the stabilizer has finite
index in the infinite group `SL_d(Z)`, it is infinite, so it is not contained
in the finite group `A_d`.

**(3) => (8) => (5).**

- `h=diag(x^m,x^(-m),1,...,1)` lies in `E` by the Whitehead lemma: `diag(u,u^(-1))` is a product of elementary matrices for every unit `u`. So (3) gives (8).
- Conversely, let `h in N_pi`. By (G3), `h` normalizes `Gamma^sat`. Now
  `h e_13(1) h^(-1)=e_13(x^m)` and `h e_31(1) h^(-1)=e_31(x^(-m))`, and
  `r>=3` makes index 3 available. So `x^m` and `x^(-m)` both lie in
  `S^13=S^31=S`.
- For `m != 0` one of `m,-m` lies outside `N^d`, so `S != R_+`. This is (5).

**The `Gamma_1` form of (5).**

- `Gamma_1=EL_r(R_1)` with `R_1=F_q[x_1^(+-1),x_2,...,x_d]`. Let
  `H=<Gamma, e_12(x_1^(-1))>`. By the arguments (R1) and (R2) inside `H`, the
  set `{f in R_1 : e_12(f) in H}` is a subring of `R_1`. It contains `R_+` and
  `x_1^(-1)`, so it equals `R_1`. By (R1), `H=Gamma_1`.
- If `e_12(x_1^(-1)) in Gamma^sat`, then `Gamma_1 <= Gamma^sat`, and
  `C_0 subset C_U(pi(Gamma_1)) subset C_0`.
- Conversely, if `C_U(pi(Gamma_1))=C_0`, then `pi(e_12(x_1^(-1)))` commutes
  with `C_0`.

Taken together, all eight conditions are equivalent.

## 5. The wall alternative

Assume the conditions fail.

Terminology only, not used below: failure of (2) is the same as a relative
wall for some compressor, by `relative-wall-commutant-growth`.

- **Every strict compressor grows the commutant.** Since (6) fails,
  `SL_d(Z) cap N_pi` is contained in `A_d`. By (G4) it equals `A_d`. So every
  `L in SL_d(N) \ A_d` lies outside `N_pi`, and by (G1) and the automatic
  inclusion `C_0 subset C_U(pi(L Gamma L^(-1)))` the inclusion is strict.
- **No non-polynomial root commutes with `C_0`.** Since (5) fails, `S=R_+`.
  By (R1), `Gamma^sat cap U_kl(R)=U_kl(R_+)` for all `k != l`. Equivalently,
  `pi(e_kl(f))` does not commute with `C_0` for every `f in R \ R_+`.
- **No monomial torus element normalizes `C_0`.** This is the failure of (8).

This proves the wall alternative. `QED`

**The von Neumann algebra reading.** For `U=U(M)` and `X` a subset of `U`,
`C_U(X)` is the unitary group of `X' cap M`. Each element of `M` is a linear
combination of (four) unitaries of `M`. So an element commutes with `C_U(X)`
iff it commutes with `X' cap M`, and a unitary `v` satisfies
`v C_U(X) v^* = C_U(X)` iff `v (X' cap M) v^* = X' cap M`, because `Ad v` is a
`*`-automorphism of `M`. Every condition above therefore transfers verbatim
to the relative commutants.
