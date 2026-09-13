# Induced projective absorption breaks base-entropy classification

Date: 2026-09-12. Lane `ex-bernoulli-negative`. Handwritten proofs, no computation. Unreviewed.

**CORRECTION (same day).** Theorem E below is a valid implication with an impossible hypothesis. The
additive lifted p-adic trace `t_p: K_0(F_p[G]) -> Z_p` of `lifted-trace-detects-finite-subgroup-projectives`
takes the value `rho = sum dim(Q_i)/|F_i|` on the summand, while absorption forces `t_p = 0`. So no group
satisfies the hypothesis, and Target T3 of Section 4 is false (`finite-subgroup-induced-absorption-conserves-entropy`).
Section 1 (Corollary D) stands. The lesson: the entropy that co-induced Ornstein isomorphisms add is `log p`
times the lifted trace, and module isomorphisms conserve the lifted trace. The mod-`p` filter of Section 3 is
the reduction of this trace and is far weaker.
Part 1 is `research/artifacts/bernoulli-negative-coinduced-ornstein-2026-09-12.md` (Theorem C and the
notation `Coind`). "Theorem 1.1" is Seward's equal-entropy theorem
(`bernoulli-shifts-with-equal-base-entropy-are-isomorphic`). `X_h` is the Bernoulli class of base entropy `h`.

## 1. Corollary D: a co-induced shift adds `H(Y)/|F|`

**Lemma T (entropy tuning).** Let `q_1, ..., q_j > 0` with `r = 1 - sum q_i > 0`, and
`h >= H(q_1, ..., q_j, r)`. Some probability vector has atoms `q_1, ..., q_j` and further atoms of total mass
`r`, with entropy exactly `h`.

*Proof.* Splitting `r` into `N` equal atoms gives entropy `H(q, r) + r log N`. Choose `N` with
`r log N >= h - H(q, r)`. The vectors `(q, r u, r(1-u)/(N-1), ..., r(1-u)/(N-1))`, `u in [1/N, 1]`, have
entropy depending continuously on `u`, from `H(q, r) + r log N` to `H(q, r)`. Take an intermediate value. QED.

**Corollary D.** Let `F <= G` be finite with `|F| >= 2`, `(Y, nu)` an F-space with `H(Y) < ∞`, and `(K, kappa)`
with `0 < H(K) < ∞`. Then `Coind(Y) × K^G ≅ M^G` for every base `M` with `H(M) = H(K) + H(Y)/|F|`.
(For `|F| = 1`, `Coind(Y) = Y^G` and this is Theorem 1.1 for `Y × K`.)

*Proof.* Put `h_K = H(K)` and `h* = h_K + H(Y)/|F|`. `H(Y) < ∞` means `nu` is purely atomic; fix an atom `y_0`.
- **Tuning `K`.** Choose `delta in (0, 1/2)` with `H_2(delta) + delta log 2 < h_K`, then `eps in (0, delta)` so
  small that `(1 - 3 eps)^(|F|-1) >= 1/2` and `H_2(3 eps) + 3 eps log 2 < h*`. By Lemma T there is `K'` with
  atoms `k_0` of mass `1 - delta`, `k_1` of mass `eps`, and entropy `h_K`, since
  `H(1 - delta, eps, delta - eps) <= H_2(delta) + delta log 2`. By Theorem 1.1, `K'^G ≅ K^G`.
- **The free orbit in `Y_2 = Y × K'^F`.** `F` acts diagonally, by the shift on `K'^F`. Let `k*(1_F) = k_1` and
  `k*(f) = k_0` for `f != 1`. For `f != 1`, `(f.k*)(f) = k*(1_F) = k_1 != k*(f)`, so the orbit
  `P = { f.(y_0, k*) }` is free with `|F|` points, each of mass `c = nu(y_0) eps (1 - delta)^(|F|-1) <= eps`.
- **Tuning `M`.** Put `beta = 1 - 3 eps` and `mu_a = c / beta^(|F|-1) <= 2 eps`. Then
  `r = 1 - beta - mu_a >= eps > 0` and `H(beta, mu_a, r) <= H_2(3 eps) + 3 eps log 2 < h*`. By Lemma T there
  is `M` with atoms `b` of mass `beta`, `a` of mass `mu_a`, and entropy `h*`. In `Y_1 = M^F`, the pattern
  `m*` with `m*(1_F) = a` and `m*(f) = b` otherwise has a free orbit whose points have mass `c`.
- **Theorem C.** Identify `f.(y_0, k*)` with `f.m*`. This is an `F`-equivariant bijection of free orbits with
  equal point masses. `H(Y_2) = H(Y) + |F| h_K = |F| h* = H(M^F)`. Theorem C gives
  `Coind(Y × K'^F) ≅ Coind(M^F)`, that is `Coind(Y) × K'^G ≅ M^G`. Theorem 1.1 replaces `K'` by `K` and `M` by
  any base of entropy `h*`. QED.

## 2. Theorem E

For a finite subgroup `F <= G` and a finite-dimensional `F_p[F]`-module `Q`, put
`Ind(Q) = F_p[G] ⊗_(F_p[F]) Q` and `X_Q = Hom(Q, F_p)` with `(f.xi)(q) = xi(f^-1 q)` and uniform measure,
so `H(X_Q) = dim(Q) log p`.

**Duality for induced modules.** For `chi in Hom(Ind(Q), F_p)` put `x(t)(q) = chi(t ⊗ q)`. Then
`x(tf)(q) = chi(t ⊗ fq) = (f^-1 . x(t))(q)`, and `(g.chi)(t ⊗ q) = chi(g^-1 t ⊗ q)` gives `(g.x)(t) = x(g^-1 t)`.
As a vector space `Ind(Q) = ⊕_(r in R) r ⊗ Q`, so `chi ↦ x` is a topological group isomorphism
`X_(Ind(Q)) -> Coind(X_Q)` carrying Haar measure to the product measure.

**Theorem E.** Let `G` be countable, `p` prime, `n >= 1`, `F_1, ..., F_r <= G` finite, and `Q_i` finite-dimensional
`F_p[F_i]`-modules, not all zero, with

    F_p[G]^n ≅ F_p[G]^n ⊕ Ind(Q_1) ⊕ ... ⊕ Ind(Q_r).

Put `rho = sum_i dim(Q_i)/|F_i| > 0`. Then `X_(n log p) ≅ X_(n log p + rho log p)` over `G`, so base entropy fails
to classify Bernoulli shifts over `G` and over every countable group containing `G`.

*Proof.* Dualizing (Part 1 of `stable-finiteness-algebraic-bernoulli-absorption-proof` for the duality
conventions) gives `(F_p^n)^G ≅ (F_p^n)^G × prod_i Coind(X_(Q_i))`. Apply Corollary D (or Theorem 1.1 when
`|F_i| = 1`) to `Coind(X_(Q_1)) × (F_p^n)^G`, whose Bernoulli part has entropy `n log p > 0`; the result is a
Bernoulli shift of entropy `n log p + dim(Q_1) log p/|F_1|`. Repeat for `i = 2, ..., r`. The right side becomes
`X_(n log p + rho log p)`. Supergroups: `bernoulli-entropy-counterexample-constraints` (d). QED.

## 3. Necessary conditions on the hypothesis

- **Stable finiteness.** The summand is nonzero projective, so `M_n(F_p[G])` is not directly finite and `G` is
  not surjunctive (`stable-finiteness-failure-refutes-surjunctivity`). The Rokhlin supremum is at most
  `n log p` (`bernoulli-entropy-counterexample-constraints` (b)).
- **Sofic quotients.** Let `phi: G -> H` with `H` sofic, so `F_p[H]` is stably finite (Elek–Szabó). Applying
  `F_p[H] ⊗_(F_p[G]) -` kills the summand, and `F_p[H] ⊗_(F_p[F_i]) Q_i` is induced from
  `F_p[phi(F_i)] ⊗_(F_p[F_i]) Q_i`, the coinvariants of `ker(phi) ∩ F_i` on `Q_i`. These must vanish. For `H = 1`:
  **no `Q_i` has a trivial quotient**. Permutation modules `F_p[G/F]` never occur.
- **Mod-p trace.** If `p` does not divide any `|F_i|`, write `Q_i` as the image of an idempotent matrix `e_i` over
  `F_p[F_i]`. The coefficient of `1` in its trace is `dim(Q_i)/|F_i|` in `F_p`, since the regular trace of `e_i` is
  `dim Q_i`. The Hattori–Stallings rank of the summand is `0`, because `tr(AB) = tr(BA)` for the one-sided
  inverse pair. So **`rho ≡ 0 mod p`**: the entropy gain `rho log p` is invisible to the Kaplansky trace mod `p`.

## 4. The target over the binary Leavitt unit group

`L = L_(F_2)(1,2)`, `U = L^x`, matrix units `e_(u,v) = s_u t_v` at level 2 (`research/artifacts/rokhlin-entropy-self-copy-dichotomy-2026-09-12.md`,
Lemma 2.2). Let `c = e_(00,01) + e_(01,10) + e_(10,00) + e_(11,11)`, the permutation unit of a 3-cycle, of order 3.
Put `e_c = c + c²`. Then `e_c² = c² + c⁴ = e_c`, its augmentation is `0`, and `Q = F_2[<c>] e_c ≅ F_4` has
dimension 2 and no trivial quotient. `rho = 2/3 ≡ 0 mod 2`.

**Target T3.** For some `n >= 1`, `F_2[U]^n ≅ F_2[U]^n ⊕ F_2[U](c + c²)` as left modules, equivalently
`I_n ⊕ 0 ~ I_n ⊕ e_c` (Murray–von Neumann) in `M_(n+1)(F_2[U])`. Theorem E would then give
`X_(n log 2) ≅ X_(n log 2 + (2/3) log 2)` over `U`.

- In the quotient `L`, the relation holds with `n = 1` for every nonzero idempotent, because the monoid of
  projectives of `L` is `{0, [L]}` with `[L] + [L] = [L]`, and `c + c² != 0` in `L` since `c != 1`.
- The gap is the lifting gap of `leavitt-unit-group-algebra-not-directly-finite`: a relation in a quotient says
  nothing about `F_2[U]` (`direct-finiteness-not-inherited-by-quotients`).
- The trivial-module analogue `F_2[U](1 + c + c²)` has augmentation `1` and is excluded by Section 3.
