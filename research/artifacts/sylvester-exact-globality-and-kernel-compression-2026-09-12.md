# Exact globality and kernel compressions for Sylvester rank functions on the binary Leavitt unit group algebra

Lane `w7-sylv-global`, 2026-09-12. Targets: `sylvester-leavitt-kazhdan-fixed-ideals-are-global` and
`sylvester-near-minimal-leavitt-defects-are-multiplicative`. Verifier: `w4-vf-linear-b`.

Sources on main:
- [CA] = `research/artifacts/sylvester-class-a-defect-chain-2026-09-12.md` (Lemmas 1.1, 1.2, 2.1, Corollary 2.3,
  Proposition 3.1, Theorem 4.1, Section 5);
- [DG] = `research/artifacts/two-root-defect-descent-gap-2026-09-12.md` (Fact 1.2, Lemma 3.0, Proposition 4.1);
- [AUD] = `research/artifacts/rank-gate-axiom-audit-2026-09-12.md` (Consequence 3.2, Proposition 4.1).

## 0. Summary

**Both lemmas are proved on paper from the Sylvester axioms alone** (class (A); verified PASS by `w4-vf-linear-b`,
Section 39 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`, ae0a4005ef, with one sentence of
Remarks 2.4 corrected forward).
1. **Submodularity** (Lemma 1.1): `rho([A; B; C]) + rho(B) <= rho([A; B]) + rho([B; C])`, by one (S4) step.
2. **Exact globality** (Theorem 2.3), with constant `1`. The loss `1/m` in [CA] Proposition 3.1(3) disappears
   because, by submodularity, "adding the rows of `M'` does not raise the rank of `M W` for any `W`" is transitive and
   closed under stacking. No Kazhdan property is used.
3. **Kernel compressions** (Lemma 3.1): if `P` commutes with a subring `C` and `rho(P) < 1`, then
   `sigma(A) = (rho([P_n; A]) - n rho(P)) / (1 - rho(P))` is a Sylvester rank function on `C`. It is the rank on the
   kernel corner, built with no idempotent and no annihilator.
4. **Near-minimal multiplicativity** (Theorem 3.4). With the triangular count
   `rho([P; T]) + rho(PT) <= rho(P) + rho(T)` for commuting `P`, `T`, the regular proof of [DG] Proposition 4.1 goes
   through. At an exact minimizer the defects are exactly multiplicative and both corners are again minimizers
   (Corollary 3.5).

**What it decides and what it does not.**
- Neither lemma decides a gate. Both hold for every Sylvester rank function, and their numbers match the firewall
  profile (Section 4.2).
- The Sylvester No branch `sylvester-rank-functions-on-leavitt-units-kill-two-root-defect` now needs one input, a
  Sylvester-form strict deficit (`sylvester-disjoint-cylinder-defects-strictly-submultiplicative`, OPEN), and no
  regularity. So `sylvester-rank-functions-on-leavitt-units-are-regular` is off the submultiplicativity route.
- **Leads checked.** Weakly finite corners (Theorem W, defect triviality) and pullbacks through weakly finite images
  (U1b) are not needed, since Lemma 3.1 gives kernel corners for every rank function. Property (T) is not the
  mechanism.
- **First premise the firewall models break:** strict submultiplicativity itself (Section 4.2).

## 1. Submodularity and the containment calculus

Axioms (S1)–(S4) and the notation `X A := (X (x) I_m) A` are as in [CA] Section 1. Deleting rows does not raise
`rho`, and `rho([M; 0]) = rho(M)`, both by (S2).

**Lemma 1.1 (submodularity on stacked rows).** For matrices `A`, `B`, `C` over `S` with `n` columns each,
`rho([A; B; C]) + rho(B) <= rho([A; B]) + rho([B; C])`.

*Proof.* By (S3) the right side is `rho(diag([A; B], [B; C]))`. Multiply on the right by the invertible
`[[I_n, 0], [I_n, I_n]]`: the row blocks become `[A, 0]`, `[B, 0]`, `[B, B]`, `[C, C]`. Subtract the second row block
from the third, giving `[0, B]`, and permute the row blocks to `[A, 0]`, `[B, 0]`, `[C, C]`, `[0, B]`. This is
`[[ [A; B; C], [0; 0; C] ], [0, B]]`, and (S4) bounds its rank below by `rho([A; B; C]) + rho(B)`. QED

In a regular rank ring, `rho` of a stack is the rank of the sum of the row modules, and Lemma 1.1 is the modular
inequality `dim(a + b + c) + dim b <= dim(a + b) + dim(b + c)`.

**Definition 1.2.** Fix `psi` on `S`. For columns `M` (`k x 1`) and `M'` (`k' x 1`) over `S`, write `M ≼ M'` if
`psi([M W; M' W]) = psi(M W)` for every matrix `W` over `S`, and `M ≈ M'` if `M ≼ M'` and `M' ≼ M`. For a faithful
regular rank ring this is containment of kernels, `ker M <= ker M'`.

**Lemma 1.3.**
1. `M ≼ Y M` for every matrix `Y` over `S` with `k` columns.
2. If `U` is invertible, then `M ≼ M'` iff `M ≼ U M'`.
3. If `M ≼ M'`, then `M v ≼ M' v` for every `v` in `S`.
4. (Transitivity) `M ≼ M'` and `M' ≼ M''` give `M ≼ M''`.
5. (Stacking) `M ≼ M_1` and `M ≼ M_2` give `M ≼ [M_1; M_2]`.
6. `M ≼ M'` gives `psi(M' W) <= psi(M W)` for every `W`.

*Proof.*
1. `[M W; (Y M) W] = [I; Y (x) I_m] · M W` has rank at most `psi(M W)`, and deleting rows gives the reverse bound.
2. `[M W; U M' W] = diag(I, U (x) I_m) · [M W; M' W]`.
3. `(M v) W = M (v W)` with `v W := (v I_m) W`; apply the definition to `v W`.
4. Lemma 1.1 with `(A, B, C) = (M W, M' W, M'' W)` gives `psi([M W; M' W; M'' W]) + psi(M' W) <= psi(M W) + psi(M' W)`.
   So `psi([M W; M'' W]) <= psi([M W; M' W; M'' W]) <= psi(M W) <= psi([M W; M'' W])`.
5. Lemma 1.1 with `(A, B, C) = (M_1 W, M W, M_2 W)` gives `psi([M_1 W; M W; M_2 W]) + psi(M W) <= 2 psi(M W)`; permute
   the rows.
6. Delete the rows of `M W`. QED

## 2. Exact globality

Setting of [CA] Section 3: `K` a field, `G` generated by `g_1, ..., g_r`, `B = K[G]`, `X = (g_i - 1)^T`,
`Gamma = <S>` finitely generated, `X_S = (s - 1 : s in S)^T`, `P_Gamma = { g in G : g Gamma g^-1 <= Gamma }`.

**Lemma 2.1.** For every Sylvester rank function `psi` on `B` and every `h` in `P_Gamma`, `X_S ≈ X_S h^-1`.

*Proof.* Each `h s h^-1` lies in `Gamma`, so by [CA] Lemma 2.1(1) for `Gamma` there is `Y_h` over `K[Gamma]` with
`X_(hSh^-1) = Y_h X_S`. Also `X_(hSh^-1) = (h I_k) X_S h^-1`. Lemma 1.3(1),(2) give `X_S ≼ X_S h^-1`. The first step
of the proof of [CA] Proposition 3.1(2), which uses only `h` in `P_Gamma` (the Frobenius inequality with
`psi(Y_h X_S) = psi(X_S)`), gives `psi(X_S h^-1 W) = psi(X_S W)` for every `W`. So
`psi([X_S h^-1 W; X_S W]) = psi(X_S W) = psi(X_S h^-1 W)`, that is `X_S h^-1 ≼ X_S`. QED

**Lemma 2.2.** If `<P_Gamma> = G`, then `X_S ≈ X_S h` for every `h` in `G`.

*Proof.* Let `H = { h : X_S ≈ X_S h }`, which contains `1`. For `h`, `k` in `H`, Lemma 1.3(3) turns `X_S ≈ X_S h`
into `X_S k ≈ X_S h k`, and transitivity with `X_S ≈ X_S k` gives `h k` in `H`. Translating `X_S ≈ X_S h` by `h^-1`
gives `h^-1` in `H`. So `H` is a subgroup. It contains `P_Gamma^-1` by Lemma 2.1, and `P_Gamma^-1` generates `G`. QED

**Theorem 2.3 (exact globality).** Suppose `<P_Gamma> = G` and `Gamma` normally generates `G`. Let `psi` be a
Sylvester rank function on `B` with `psi(X Z) = psi(Z)` for every `Z`. Then `psi(X_S Z) = psi(Z)` for every `Z`.

*Proof.* By [CA] Proposition 3.1(1), `X = Y Sigma` with `Sigma = [X_S h_1; ...; X_S h_m]`. Lemma 2.2 and Lemma 1.3(5)
give `X_S ≼ Sigma`, and Lemma 1.3(1),(4) give `X_S ≼ X`. So
`psi(Z) = psi(X Z) <= psi([X_S Z; X Z]) = psi(X_S Z) <= psi(Z)`. QED

**Remarks 2.4.**
- **Where [CA] stopped.** [CA] Section 5.1 asked for the general implication "`psi(M_1 W) = psi(M_2 W)` for all `W`
  gives `psi([M_1; M_2] W) = psi(M_1 W)`". That implication is not proved here, and it is not needed. The containment
  `X_S ≼ X_S h^-1` comes from the exact identity `Y_h X_S = (h I) X_S h^-1`, and equal ranks are used only for the
  reverse containment, once the forward one is known.
- **No Kazhdan property.** The name of the target comes from the regular statement. The proof uses only generation
  by the compression semigroup and normal generation.
- **Calibration: the compression hypothesis cannot be dropped.** Take `G = A_5` over `F_2` and `psi` the normalized
  rank on the 4-dimensional sum-zero submodule `V` of the 5-point permutation module.
  - `V` is irreducible and nontrivial, so `X` acts injectively and `psi(X Z) = psi(Z)`.
  - `Gamma = A_4` normally generates `A_5`, but it is self-normalizing, so `P_Gamma = A_4`.
  - `Fix(A_4)` on `V` is spanned by `(1,1,1,1,0)`, so `psi(X_S) = 3/4 < 1`, and exact globality fails.
  - Normal generation alone gives a `1/m` bound only at `Z = 1`. `F_2[A_5]` maps onto `End(V) = M_4(F_2)`, so some
    `Z` acts on `V` as a projection onto `Fix(A_4)`. Then `psi(Z) = 1/4` but `psi(X_S Z) = 0`, so the `1/m` bound for
    general `Z` ([CA] Proposition 3.1(3)) also needs the compression hypothesis. (Correction from `w4-vf-linear-b`,
    Section 39 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`.)
- **Consequence for [CA] Theorem 4.1.** Its corner model `tau` has `tau(X) = 1` (step 1 of Theorem 3.4). So the
  lower descent constant `c_0/m_0` improves to `c_*^Syl`.

**Corollary 2.5 (Leavitt instance).** Let `R = L_(F_2)(1,2)`, `G = R^x`, and let `psi` be fixed-point-free
(`psi(X Z) = psi(Z)` for all `Z`), for example `psi = rho_omega` for a non-augmentation `rho` ([CA] Corollary 2.3).
For every proper cylinder `B` and every matrix `Z`, `psi(iota_B(X) Z) = psi(Z)`.

*Proof.* `Gamma_0 = iota_0(R^x)` has `<P_(Gamma_0)> = G` and normally generates `G` ([CA] Section 3, Application).
For a proper cylinder `B`, `Gamma_B = u Gamma_0 u^-1` with `u` in `V` ([DG] Fact 1.2), so `P_(Gamma_B) =
u P_(Gamma_0) u^-1` generates `G`, and `Gamma_B` normally generates `G`. Now `iota_B(X) = X_(S_B)` for the generating
set `S_B = iota_B({g_i})` of `Gamma_B`, and Theorem 2.3 applies. QED

## 3. Kernel compressions and near-minimal multiplicativity

**Lemma 3.1 (kernel compression).** Let `C` be a unital subring of `S`, and `P` in `S` with `c P = P c` for every
`c` in `C`. Let `rho` be a Sylvester rank function on `S` with `rho(P) < 1`, and write `P_n = P I_n`. For a matrix `A`
over `C` with `n` columns put `sigma(A) := (rho([P_n; A]) - n rho(P)) / (1 - rho(P))`. Then `sigma` is a Sylvester
matrix rank function on `C`.

*Proof.* `sigma >= 0` by deleting rows.
- (S1) `rho([P_n; 0]) = n rho(P)` gives `sigma(0) = 0`, and `rho([P; 1]) = 1` gives `sigma(1) = 1`.
- (S3) `[P_(n+q); A (+) B]` is a row permutation of `[P_n; A] (+) [P_q; B]`.
- (S4) `[P_(n+q); [[A, D], [0, B]]]` is a row permutation of `[[ [P_n; A], [0; D] ], [0, [P_q; B]]]`.
- (S2), right factor. For `A` (`m x n`) and `B` (`n x p`) over `C`, `[P_p; A B] = diag(I_p, A) · [P_p; B]`, so
  `sigma(A B) <= sigma(B)`.
- (S2), left factor. Apply Lemma 1.1 to the `(n+p)`-column matrices `A' = [A, 0]`, `B' = [P_n, 0]` and
  `C' = [[I_n, -B], [0, P_p]]`.
  - `rho(B') = n rho(P)` and `rho([A'; B']) = rho([P_n; A])`.
  - Since `P_n B = B P_p`, the row operation `B' -> B' - P_n [I_n, -B] - B [0, P_p]` turns `B'` into `0`. So
    `rho([B'; C']) = rho(C')`, and the column operation adding `(column block 1)·B` to column block 2 gives
    `rho(C') = rho(diag(I_n, P_p)) = n + p rho(P)`.
  - In `[A'; B'; C']` the same operation removes `B'`. Then `A' -> A' - A [I_n, -B]` gives `[0, A B]`, and the same
    column operation leaves the rows `[0, A B]`, `[I_n, 0]`, `[0, P_p]`. So `rho([A'; B'; C']) = n + rho([P_p; A B])`.
  - Lemma 1.1 gives `n + rho([P_p; A B]) + n rho(P) <= rho([P_n; A]) + n + p rho(P)`, which is
    `sigma(A B) <= sigma(A)`. QED

Checks: `P = 0` gives `sigma = rho` on `C`. In a faithful regular rank ring with `K` the right annihilator of `P`,
`rho([P_n; A]) = n rho(P) + rk(A on K^n)`, so `sigma` is the kernel corner of [DG] Proposition 4.1 (sketch).

**Lemma 3.2 (triangular count).** If `P T = T P` in `S`, then `rho([P; T]) + rho(P T) <= rho(P) + rho(T)`.

*Proof.* Multiply `diag(P, T)` on the right by `[[1, 0], [1, 1]]`, giving the rows `[P, 0]` and `[T, T]`. Append a
zero row and add `T·(row 1) - P·(row 2)` to it, giving `[T P - P T, -P T] = [0, -P T]`. The matrix
`[[ [P; T], [0; T] ], [0, -P T]]` still has rank `rho(P) + rho(T)`, and (S4) bounds it below by
`rho([P; T]) + rho(P T)`. QED

**Setting 3.3.** `R`, `G = R^x`, `D_A` and `E = D_1000` are as in [CA] Section 4, and
`c_*^Syl := inf rho_omega(E)` over non-augmentation `rho`, which is at least `c_0 > 0`. A fixed-point-free `psi` is
non-augmentation with `psi_omega = psi`, so `c_*^Syl` is also the infimum of `psi(E)` over fixed-point-free `psi`.
For such `psi` and pairwise disjoint proper cylinders `A_1, ..., A_k` with proper union,
`f(k) := psi(D_(A_1) ... D_(A_k))` depends only on `k` ([CA] Theorem 4.1), and `delta := f(1) = psi(E) <= 1/2`.

**Theorem 3.4 (near-minimal multiplicativity).** Let `psi` be fixed-point-free with `delta <= (1 + eps) c_*^Syl`.
Then for every `k >= 1`:
- (a) `f(k+1) >= c_*^Syl f(k)`;
- (b) `f(k+1) <= delta - c_*^Syl (1 - f(k))`;
- (c) `|f(k+1) - delta f(k)| <= eps delta` and `|f(k) - delta^k| <= 2 eps delta`.

*Proof.* Take a `(k+1)`-tuple as in Setting 3.3, and put `P = D_(A_1) ... D_(A_k)`, `B = A_(k+1)`,
`C = iota_B(F_2[R^x])` and `T = iota_B(E) = D_(B1000)`. `C` commutes with `P` ([DG] Fact 1.2).
`(A_1, ..., A_k, B1000)` is again a tuple with proper union, so `psi(P T) = f(k+1)`. By [CA] Theorem 4.1,
`0 < f(k) <= 1/2`.
1. **Range corner.** `tau(A) := psi(iota_B(A) P_n) / f(k)` is a Sylvester rank function on `F_2[R^x]` ([CA]
   Lemma 1.2, pulled back along `iota_B`). For `Z` with `n` columns, `iota_B(X Z) = iota_B(X) iota_B(Z)`, and
   Corollary 2.5 applied to `iota_B(Z) P_n` gives `tau(X Z) = tau(Z)`. So `tau` is fixed-point-free, and
   `f(k+1)/f(k) = tau(E) >= c_*^Syl`. This is (a).
2. **Kernel corner.** `sigma(A) := (psi([P_n; iota_B(A)]) - n f(k)) / (1 - f(k))` is a Sylvester rank function on
   `F_2[R^x]` (Lemma 3.1, pulled back along `iota_B`). It is fixed-point-free. For `Z` of size `m x n`,
   `[P_n; iota_B(X Z)] = diag(I_n, iota_B(X) (x) I_m) · [P_n; iota_B(Z)]` gives `<=`. Corollary 2.5 and a row
   permutation give `psi([P_n; iota_B(Z)]) = psi(iota_B(X) [P_n; iota_B(Z)]) = psi([(iota_B(X) (x) I_n) P_n;
   iota_B(X Z)])`, and the left factor `diag(iota_B(X) (x) I_n, I)` bounds this by `psi([P_n; iota_B(X Z)])`. So
   `sigma(E) >= c_*^Syl`, that is `psi([P; T]) >= f(k) + c_*^Syl (1 - f(k))`.
3. **Count.** Lemma 3.2 for the commuting `P` and `T` gives `psi([P; T]) + f(k+1) <= f(k) + delta`. With step 2
   this is (b).
4. **Recursion.** Since `delta - c_*^Syl <= eps c_*^Syl <= eps delta`, (a) gives
   `f(k+1) - delta f(k) >= -(delta - c_*^Syl) f(k) >= -eps delta`, and (b) gives
   `f(k+1) - delta f(k) <= (delta - c_*^Syl)(1 - f(k)) <= eps delta`. With `f(1) = delta` and `delta <= 1/2`,
   `|f(k) - delta^k| <= eps delta (1 + delta + delta^2 + ...) <= 2 eps delta`. QED

**Corollary 3.5 (minimizers).** Suppose a non-augmentation Sylvester rank function on `F_2[R^x]` exists. Then some
fixed-point-free `psi_*` has `psi_*(E) = c_*^Syl`. For it, `f(k) = (c_*^Syl)^k`, `tau(E) = sigma(E) = c_*^Syl`
(both corners are minimizers), and Lemma 3.2 is an equality at `(P, T)`.

*Proof.* The Sylvester matrix rank functions on a ring form a closed subset of a product of compact intervals, since
each axiom involves finitely many coordinates. Fixed-point-freeness is closed, so `psi -> psi(E)` attains its
infimum. At `eps = 0`, (a) and (b) give `f(k+1) = c_*^Syl f(k)`, so `tau(E) = c_*^Syl`. Step 3 then forces
`sigma(E) <= c_*^Syl`, so `sigma(E) = c_*^Syl`, and the count is an equality. QED

## 4. What it gives, and where the firewalls bite

**4.1 The Sylvester No branch.** Let `sylvester-disjoint-cylinder-defects-strictly-submultiplicative` be the claim
that there is `theta < 1` with `rho_omega(D_A D_B) <= theta rho_omega(D_A) rho_omega(D_B)` for every non-augmentation
`rho` and all disjoint proper `A`, `B` with proper union. Suppose it holds and a non-augmentation `rho` exists.
- A fixed-point-free `psi` with `delta <= (1 + eps) c_*^Syl` exists by the definition of an infimum; compactness is
  not needed.
- Theorem 3.4 gives `delta^2 - 2 eps delta <= f(2) <= theta delta^2`, so `(1 - theta) delta <= 2 eps`. That is
  impossible for `eps < (1 - theta) c_0 / 2`.
- So the augmentation rank is the only Sylvester rank function, and it kills `D`. This is [AUD] Consequence 3.2 with
  class-(A) inputs: route `sylvester-rank-triviality-via-strict-defect-submultiplicativity`.

Scope of that route:
- No regular envelope, weakly finite corner, pullback through weakly finite images (U1b) or matrix approximation is
  used.
- The deficit claim implies the model form `leavitt-disjoint-cylinder-defects-strictly-submultiplicative` for tuples
  with proper union: a fixed-point-free model's rank function is its own augmentation quotient.
- The deficit claim is equivalent to the target, which makes it vacuous. Its use is as the local, quantitative form
  a proof would aim at.

**4.2 Firewalls: the first premise they break.**
- **Premises used in Sections 2–3.**
  - The Sylvester axioms.
  - For `R^x`: perfection (`omega = omega^2`), a compression semigroup of `Gamma_0` generating `R^x`, normal
    generation (simplicity), `V`-transitivity on tuples with proper union, square-zero `N_12`, and the gap `c_0`.
- **Why no firewall model contradicts them.** The listed models (sofic subgroups containing both frames, locally
  finite HNN data, Fock, `UT_4`, commuting witnesses, graphs of locally finite groups, halving) are weakly finite with
  `D != 0`. None is a non-augmentation rank function on all of `F_2[R^x]`, which would decide
  `binary-leavitt-units-carry-nonaugmentation-rank-function`. They model subgroups or relaxed relations, where the
  generation premises of Theorem 2.3 are unavailable. For example, the Fock compressors miss the Toeplitz relation by
  `1/4`, so the Fock model is not a representation of `R^x`.
- **What they do test: the numbers.**
  - The sofic-subgroup firewall (`sofic-subgroups-carry-independent-cylinder-defects`) and the graph-of-locally-finite-groups
    firewall realize the independent profile `rk(D_A D_B) = (3/8)^2`, and halving gives `theta = 1`.
  - In an independent profile with factor ranks `p` and `t`, `rk([P; T]) = p + t - pt` and `rk(PT) = pt`, so Lemma
    3.2 is an equality. Compressing at `P` leaves the factor on `B` unchanged, so `tau(E) = sigma(E) = delta`.
  - These are exactly the conclusions of Corollary 3.5. Nothing proved here separates a minimizer from the firewall
    profile.
- **First premise broken.** Any decision along this chain needs a premise that is false at the independent profile.
  The first is the strict deficit at a minimizer, that is `theta < 1` in Sylvester form. By
  `sofic-subgroups-carry-independent-cylinder-defects`, a relation-only proof of it must use a nonsofic subgroup
  containing both frames; otherwise it needs a global input.

**4.3 Nodes.**
- `sylvester-rank-functions-are-submodular-on-stacked-rows` (Lemmas 1.1, 1.3) and its `-proof` route.
- `sylvester-rank-functions-compress-to-commuting-kernels` (Lemmas 3.1, 3.2) and its `-proof` route.
- The targets, established on paper: `sylvester-leavitt-kazhdan-fixed-ideals-global-proof` (Section 2) and
  `sylvester-near-minimal-leavitt-defects-multiplicative-proof` (Section 3).
- The open claim `sylvester-disjoint-cylinder-defects-strictly-submultiplicative` and the route
  `sylvester-rank-triviality-via-strict-defect-submultiplicativity` (Section 4.1).
