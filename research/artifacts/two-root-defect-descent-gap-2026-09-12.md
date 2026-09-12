# The two-root defect gap, and why the nested descent cannot close the gate

Lane `w4-gate-descent`, 2026-09-12, family R4. Supports
`leavitt-rank-model-defect-gap-on-fixed-point-free-quotients`,
`nested-two-root-defect-pieces-decay-geometrically-both-ways`,
`near-minimal-defect-models-have-multiplicative-cylinder-defects`,
`leavitt-disjoint-cylinder-defects-strictly-submultiplicative`, and an Attempts entry on
`rank-models-of-el3-satisfy-the-two-root-identities`. It continues Remark 1.4 and Section 3 of
`research/artifacts/two-root-defect-piece-and-fd-representations-2026-09-12.md`.

## 0. Summary

* **Section 2 (established): a defect gap.** There is a constant `c_0 > 0` such that every
  characteristic-two rank model `sigma` of `R^x` satisfies

  ```text
  c_0 · rk(1-f)  <=  rk((1-f) D_A)  <=  rk(1-f) / 2 ,
  ```

  where `fM = Fix_r(sigma(R^x))` and `D_A` is the two-root product of any proper cylinder pair.
  So on the fixed-point-free quotient model the normalized defect lies in `[c_0, 1/2]`. The lower
  bound comes from compactness, corner locality, perfection and four-generation. Property (T),
  globality and the compressor collision are not used. `c_0` is not explicit.
* **Section 3 (established): the descent is geometric in both directions.** On a fixed-point-free
  model, the ranks `f(k) = rk(D_(A_1) ... D_(A_k))` for pairwise disjoint cylinders satisfy
  `c_* f(k) <= f(k+1) <= f(k)/2`, where `c_* >= c_0` is the infimum of the normalized defect over
  nontrivial fixed-point-free models. This proves the uniform descent bound Remark 1.4 asked for,
  with `c = c_*`. It also kills the payoff attached to it: the nested pieces at least halve at every
  step, so they contain no principal right ideal of positive rank, and there is no limit corner.
* **Section 4 (established): near-minimal models look like tensor products.** If
  `delta = rk(D_A) <= (1+eps) c_*` on a fixed-point-free model, then `|f(k) - delta^k| <= 2 eps delta`
  for every `k`. The range and kernel corner models of a disjoint defect are both exactly borderline,
  so neither restriction lowers the defect.
* **Section 5 (open): where it stops.** Closing the gate along this line needs an operation on
  fixed-point-free models that lowers the normalized defect by a fixed factor. One sufficient input
  is strict submultiplicativity `rk(D_A D_B) <= theta rk(D_A) rk(D_B)` with `theta < 1`. Honest
  tensor configurations attain `theta = 1`, so any proof must use the Leavitt relations.
* **Calibration.** In the Toeplitz group `H = EL_3(A_X)` the honest model `EL_3(phi)` is
  fixed-point-free with defect `0`. So the analogue of Section 2 fails there, at corner locality,
  as it must.

## 1. Setting and standard facts

Notation follows the defect-piece artifact.
* `R = L_(F_2)(1,2)`, with `R^x = EL_3(R)` through the code `(0, 10, 11)`.
* `iota_P(g) = S[P] g T[P] + (1 - S[P]T[P])`.
* `sigma : R^x -> M^x` is a homomorphism into the units of a rank ultraproduct `M` over a field of
  characteristic two. `M` is von Neumann regular with a faithful rank function `rk`, normalized by
  `rk(1) = 1`, and a nonzero corner `eMe` is again a rank ultraproduct after renormalizing.
* For a proper cylinder `A` (a nonempty prefix):
  * `N^A_ab = sigma(iota_A(x_ab(1))) - 1`;
  * `D_A = N^A_23 N^A_12`.
* `fM = Fix_r(sigma(R^x))`, with `sigma(g) f = f` for every `g`.
* `sigma` is *fixed-point-free* when `f = 0`.

**Fact 1.1 (rank calculus).** Let `M` be a regular ring with a faithful rank function.
* (a) If `x = x z x`, then the right annihilator of `x` is `(1 - zx)M`, and its rank is `1 - rk(x)`.
* (b) Principal right ideals form a modular lattice on which `rk` is a dimension function:
  `rk(I cap J) + rk(I + J) = rk(I) + rk(J)`. Hence
  `rk(I_1 cap ... cap I_m) >= rk(I_1) + ... + rk(I_m) - (m - 1)`.
* (c) If `q` is idempotent, `T q = q T q`, and `(qTq)^2 = 0`, then `rk(Tq) <= rk(q)/2`.
* (d) Suppose `x` is an element with right annihilator `K`. For every principal right ideal `J`
  containing `K`, `rk(xJ) = rk(J) - rk(K)`.

*Proof.* (a) and (b) are standard: principal right ideals are direct summands, and the rank is the
dimension function on finitely generated projectives (Goodearl, *Von Neumann Regular Rings*,
Chapter 16). (c) In `qMq`, renormalized, `qTq` is square-zero, so its image lies in its kernel, and
rank-nullity gives `2 rk(qTq) <= rk(q)`. (d) `0 -> K -> J -> xJ -> 0` is exact, and ranks add over
exact sequences of summands. QED

**Fact 1.2 (commuting and transitivity).**
* For disjoint proper cylinders `A` and `B`, `iota_A(R^x)` and `iota_B(R^x)` commute, because
  `S[A] a T[A] · S[B] b T[B] = 0`. So the `N^A`, `N^B`, `D_A`, `D_B` commute.
* Thompson's `V` sits in `R^x` as prefix-replacement units. Take two `k`-tuples `(A_i)` and `(B_i)`
  of pairwise disjoint cylinders, each with proper union. Split both complements into the same
  number of cylinders `C_j` and `C'_j`. Then `u = sum_i S[B_i]T[A_i] + sum_j S[C'_j]T[C_j]` lies in
  `V`, and `u iota_(A_i)(g) u^-1 = iota_(B_i)(g)` for all `g` and `i`.
* Hence the rank of any product of `D_(A_1), ..., D_(A_k)` depends only on `k`, for configurations
  with proper union. For `k = 1` this is one number `delta(sigma) = rk(D_A)`.

**Fact 1.3 (square zero).** In characteristic two `iota_A(x_ab(1))` is an involution, so
`(N^A_ab)^2 = 0`.

## 2. The defect gap

**Lemma 2.1 (the fixed-point-free quotient).** Suppose `f != 1`. Then:
* `sigma_W(g) = (1-f) sigma(g) (1-f)` is a homomorphism `R^x -> ((1-f)M(1-f))^x`;
* `sigma_W` is fixed-point-free, and nontrivial exactly when `sigma` is;
* its defect at a proper cylinder `A` is `(1-f) D_A`.

*Proof.*
* **Homomorphism.** `(1-f) sigma(g) f = 0`, so `sigma_W` is multiplicative, as in Theorem 1.2 of
  the defect-piece artifact.
* **No fixed vectors.** Let `x` in `(1-f)M` satisfy `sigma_W(g) x = x` for every `g`. Put
  `c(g) = sigma(g) x - x = f sigma(g) x`, which lies in `fM`. Since `sigma(g)` fixes `fM`
  pointwise, `c(gh) = c(g) + sigma(g) c(h) = c(g) + c(h)`. So `c` is a homomorphism into the
  additive group `fM`, which is abelian, and `c = 0` because `R^x` is perfect
  (`leavitt-gl-equals-el-and-perfect-unit-group`). Then `x` lies in `fM cap (1-f)M = 0`.
* **Nontrivial.** If `sigma_W` is trivial, then `sigma(g) - 1` lies in `fM(1-f)`, where
  `(1+a)(1+b) = 1+a+b`. So `sigma` lands in an abelian group, and perfection makes it trivial.
* **Defect.** `N^A_ab f = 0`, so `(1-f) N^A_ab (1-f) = (1-f) N^A_ab`, and
  `(1-f)N^A_23 (1-f) N^A_12 = (1-f) D_A`. QED

**Lemma 2.2 (displacement).** Let `g_1, ..., g_4` generate `R^x`
(`binary-leavitt-unit-group-four-generated`). If `sigma` is fixed-point-free, then
`sum_i rk(sigma(g_i) - 1) >= 1`, so `max_i rk(sigma(g_i) - 1) >= 1/4`.

*Proof.* A vector fixed by the generators is fixed by the group, so `Fix_r(sigma(R^x))` is the
intersection of the right annihilators of `sigma(g_i) - 1`. By Fact 1.1(a) and (b) its rank is at
least `1 - sum_i rk(sigma(g_i) - 1)`, and it is `0`. QED

**Lemma 2.3 (compactness).** For every `eta > 0` there is `c(eta) > 0` such that every
characteristic-two rank model with `max_i rk(sigma(g_i) - 1) >= eta` has `rk(D_1000) >= c(eta)`.

*Proof.* Suppose models `sigma_n : R^x -> M_n^x` have `max_i rk(sigma_n(g_i) - 1) >= eta` and
`rk(D_1000^(n)) < 1/n`. Passing to a subsequence, one index `i` attains the maximum for all `n`.
* **Finite stages.** Enumerate `R^x = {h_1, h_2, ...}`, with `g_i`, `x' = iota_1000(x_12(1))` and
  `y' = iota_1000(x_23(1))` among the first terms. Relations and ranks in `M_n` are ultralimits of
  finite-stage values. So for each `n` there are invertible matrices `X_n(h_j)`, `j <= n`, of size
  `k_n`, over a field of characteristic two, such that:
  * every relation `h_a h_b = h_c` with `a, b, c <= n` holds up to normalized rank `1/n`;
  * the normalized ranks of `X_n(g_i) - 1` and of `(X_n(y') - 1)(X_n(x') - 1)` are within `1/n`
    of their values in `M_n`.

  A matrix of normalized rank at least `1 - eps` differs from an invertible matrix by normalized
  rank at most `eps`, so invertibility costs nothing.
* **One field.** Finitely many entries generate a finitely generated field of characteristic two.
  It embeds into `Omega`, the algebraic closure of `F_2(t_1, t_2, ...)`, and rank does not change.
* **The limit model.** Along a nonprincipal ultrafilter, `sigma'(h) = [(X_n(h))]` is a
  homomorphism from `R^x` into the units of a rank ultraproduct over `Omega`.
  * Its corner product on `[1000]` has rank `0`.
  * So it is trivial by `two-root-identity-is-corner-local-for-leavitt-rank-models`, (3) implies (1).
  * But `rk(sigma'(g_i) - 1) >= eta`, a contradiction. QED

**Theorem 2.4 (defect gap).** Put `c_0 = c(1/4)`. For every characteristic-two rank model `sigma`
of `R^x` and every proper cylinder `A`:

```text
c_0 · rk(1-f)  <=  rk((1-f) D_A)  <=  min( rk(D_A), rk(1-f)/2 ) ,        rk(D_A) <= rk(1-f) .
```

In particular:
* a nontrivial fixed-point-free model has normalized defect in `[c_0, 1/2]`;
* so `c_0 <= 1/2` whenever a nontrivial model exists.

*Proof.* If `f = 1` everything vanishes, so suppose not.
* **Lower bound.** `sigma_W` is nontrivial and fixed-point-free (Lemma 2.1). In the renormalized
  corner its displacement is at least `1/4` (Lemma 2.2), so its defect at `[1000]` has normalized
  rank at least `c_0` (Lemma 2.3). By Fact 1.2 the same holds at every proper cylinder. Un-normalizing
  gives `rk((1-f)D_A) >= c_0 rk(1-f)`.
* **Upper bounds.**
  * `(1-f) N^A_12` is square-zero in `(1-f)M(1-f)` (Fact 1.3 and `N^A_12 f = 0`), so
    `rk((1-f) D_A) <= rk((1-f) N^A_12) <= rk(1-f)/2`.
  * `D_A = D_A (1-f)`, so `rk(D_A) <= rk(1-f)`. QED

**Remark 2.5 (what is used).**
* **Used:**
  * corner locality, which is where "R has no rank model" enters;
  * perfection;
  * four-generation;
  * the corner-ring fact.
* **Not used:** property (T) of `Gamma`, globality, and the compressor collision `q sigma(u) q != 0`.
* **Why the constant is inexplicit:** it comes from compactness. A quantitative corner locality
  would make it explicit.

**Remark 2.6 (calibration: the Toeplitz group).** Take `H = EL_3(A_X)` from Section 2 of the
defect-piece artifact, and the honest model `EL_3(phi)`.
* **Fixed-point-free:** a fixed vector `v` has `E_ab phi(1) v = 0` for all `a != b`, so `v = 0`.
* **Defect:** it is `E_23 E_12 = 0`.

So the analogue of Theorem 2.4 fails for `H`, and it fails at Lemma 2.3, because corner locality
fails when the coefficient ring has a rank model. The upper bound `1/2` holds there too.

## 3. The descent is geometric in both directions

Throughout this section `sigma` is nontrivial and fixed-point-free, normalized so that
`rk(1) = 1`. Let `c_*` be the infimum of `rk(D_1000)` over nontrivial fixed-point-free models. By
Theorem 2.4, `c_0 <= c_* <= 1/2`.

**Lemma 3.0 (globality on cylinders).** For every proper cylinder `A`,
`Fix_r(sigma(iota_A(R^x))) = Fix_r(sigma(R^x))`.

*Proof.*
* **A = 0.** This is `leavitt-rank-models-kazhdan-fixed-ideals-are-global` in degree `(1,0)`,
  because `iota_0(R^x)` equals the nine-leaf `EL_alpha(R)` as a set (Section 52 of
  `research/artifacts/gk-vf-linear-verification-2026-09-12.md`).
* **Other A.** Fact 1.2 gives `u` in `V` with `u iota_0(g) u^-1 = iota_A(g)`. So the fixed ideal of
  `sigma(iota_A(R^x))` is `sigma(u) fM = fM`. QED

**Theorem 3.1 (two-sided descent).** Let `A_1, ..., A_(k+1)` be pairwise disjoint proper cylinders
with proper union. Put `f(k) = rk(D_(A_1) ... D_(A_k))` and `f(0) = 1`. Then

```text
c_* f(k)  <=  f(k+1)  <=  f(k) / 2 ,        hence        c_*^k  <=  f(k)  <=  2^-k .
```

*Proof.* Put `Q_k = D_(A_1) ... D_(A_k) M = q_k M` and `B = A_(k+1)`. By Fact 1.2 each
`sigma(iota_B(g))` and each `N^B_ab` commutes with every `D_(A_i)`. So `Q_k` is invariant under
them, and `X q_k = q_k X q_k` for each such element `X`.
* **Upper bound.** `(q_k N^B_12 q_k)^2 = q_k (N^B_12)^2 q_k = 0` (Fact 1.3). By Fact 1.1(c),
  `rk(N^B_12 q_k) <= f(k)/2`. Then `f(k+1) = rk(D_B q_k) <= rk(N^B_12 q_k)`.
* **Lower bound.**
  * **The corner model.** `tau(g) = q_k sigma(iota_B(g)) q_k` is a homomorphism
    `R^x -> (q_k M q_k)^x` (Lemma 1.1 of the defect-piece artifact).
  * **Fixed-point-free.** A vector of `Q_k` fixed by `tau` is fixed by `sigma(iota_B(R^x))`, hence
    by `sigma(R^x)` (Lemma 3.0), hence it is `0`.
  * **Nontrivial,** because `f(k) > 0` by induction.
  * **Its defect.** The `[1000]` defect of `tau` is `D_(B1000) q_k`. Its rank is
    `rk(D_(B1000) D_(A_1) ... D_(A_k))`, which equals `f(k+1)` by Fact 1.2.
  * **Conclusion.** Normalizing by `rk(q_k) = f(k)` gives `f(k+1) >= c_* f(k)`. QED

**Corollary 3.2 (the nested pieces of Remark 1.4).** Let `sigma` be any nontrivial model, and let
`Q = Q_1 ⊇ Q_2 ⊇ ...` be the nested defect pieces of Remark 1.4 of the defect-piece artifact, of
ranks `delta_k`.
1. `Q_k = D_(A_k) ... D_(A_1) M` with `A_j = 0^(j-1) 1000`. These cylinders are pairwise disjoint,
   with proper union.
2. `delta_(k+1) <= delta_k / 2`. So `delta_k <= 2^(1-k) delta_1`, and every principal right ideal
   inside all the `Q_k` has rank `0`.
3. On the fixed-point-free quotient, `(1-f) Q_k` has rank `rk(1-f) f_W(k)`, with
   `c_* <= f_W(k+1) / f_W(k) <= 1/2`. In `sigma` itself,
   `c_*^k rk(1-f) <= delta_k <= 2^(1-k) rk(1-f)`.

*Proof.*
1. By Lemma 1.1 of the defect-piece artifact, `(sigma(gamma) - 1) q = q (sigma(gamma) - 1) q` for
   `gamma` in `Gamma`. So `q D_(0P') q = D_(0P') q`, and its image is `D_(0P') D_1000 M`. The iterated
   model `tau_(Q_k) o iota_0` has cylinder pairs `iota_(0^k P)`, so the next piece uses
   `A_(k+1) = 0^k 1000`.
2. The upper bound in Theorem 3.1 uses only commutation and square zero, so it holds in `sigma`
   directly.
3. Each `D` kills `f`, so `(1-f) D_(A_k) ... D_(A_1)` is the product of the defects of `sigma_W`.
   Apply Theorem 3.1 to `sigma_W`. Then `delta_k >= rk((1-f) Q_k)`, and `delta_1 <= rk(1-f)`. QED

**Remark 3.3 (the payoff attached to Remark 1.4 is dead).**
* **The hope.** Remark 1.4, and the family plan built on it, hoped that a uniform bound
  `delta_(k+1) >= c · delta_k`, together with `R ~= R^2`, would give a unital approximately
  multiplicative map from `R` into a limit corner.
* **What holds.** Theorem 3.1 proves that bound on the fixed-point-free quotient, with `c = c_*`.
  Corollary 3.2(2) shows that in every model the limit corner has rank `0`.
* **Why this is no contradiction.** A per-step ratio between `c_*` and `1/2` is consistent for every
  `c_* <= 1/2`. The descent bound is a theorem, not a contradiction. A contradiction needs an upper
  bound that the lower bound `c_*` cannot meet.

## 4. Near-minimal models look like tensor products

**Proposition 4.1.** Let `sigma` be nontrivial and fixed-point-free with
`delta = rk(D_1000) <= (1+eps) c_*`, and let `A_1, ..., A_(k+1)` be as in Theorem 3.1. Then

```text
| f(k+1) - delta f(k) |  <=  eps delta ,        hence        | f(k) - delta^k |  <=  2 eps delta   (k >= 1).
```

*Proof.* Put `B = A_(k+1)` and `P = D_(A_1) ... D_(A_k)`. Let `K = kM` be the right annihilator of
`P`; it has rank `1 - f(k)`.
* **Lower bound.** Theorem 3.1 gives `f(k+1) >= c_* f(k) >= delta f(k)/(1+eps)`, so
  `delta f(k) - f(k+1) <= eps delta`.
* **Kernel corner.** `P` commutes with `sigma(iota_B(R^x))`, so `K` is invariant, and
  `k sigma(iota_B(.)) k` is a model on `kMk`.
  * It is fixed-point-free by Lemma 3.0.
  * It is nontrivial because `rk(k) >= 1/2`.
  * So `rk(D_(B1000) k) >= c_* (1 - f(k))`.
* **Triangular count.** `T = D_(B1000)` maps `K` into `K`. Put `J = TM + K`.
  * `TM` surjects onto `J/K` with kernel containing `TK`, so `rk(TM) >= rk(TK) + rk(J) - rk(K)`.
  * By Fact 1.1(d), `rk(J) - rk(K) = rk(PJ) = rk(PTM) = rk(TPM) = f(k+1)`.
  * With `rk(TM) = delta`, this gives `delta >= c_*(1 - f(k)) + f(k+1)`.
* **Upper bound.**
  `f(k+1) <= delta - c_*(1 - f(k)) <= (eps delta + delta f(k))/(1+eps) <= delta f(k) + eps delta`.
* **Iterate.** `|f(k) - delta^k| <= eps delta (1 + delta + delta^2 + ...) <= 2 eps delta`, since
  `delta <= 1/2`. QED

**Remark 4.2 (both restrictions are borderline).**
* **The two restrictions.** A commuting defect offers two: the range corner `Q_k` and the kernel
  corner `K`.
* **Their defects.** At a near-minimal model, the restricted models have normalized defects
  `f(k+1)/f(k)` and `rk(D_(B1000) k)/(1 - f(k))`. Both are within `O(eps)` of `delta`.
* **The pattern.** The ranks `f(k) = delta^k + O(eps delta)` are those of a tensor product of `k`
  independent factors, each of defect `delta`.
* **Consequence.** No iterate of range and kernel restrictions lowers the defect by a fixed factor.

## 5. Where it stops

**What is proved.** Sections 2 to 4 settle the descent step that Remark 1.4 left open.
* **Gap.** It exists: `c_* >= c_0 > 0`.
* **Descent.** The descent is geometric, with per-step ratio in `[c_*, 1/2]`.
* **No limit corner.** No positive-rank limit corner exists.
* **Near-minimal models.** At near-minimal defect, disjoint cylinder defects multiply like independent
  tensor factors.

**What a contradiction needs.** Any one of the following.
* **Strict submultiplicativity** (`leavitt-disjoint-cylinder-defects-strictly-submultiplicative`,
  open). This is a `theta < 1` with `rk(D_A D_B) <= theta rk(D_A) rk(D_B)` on nontrivial
  fixed-point-free models.
  * With Proposition 4.1 at `eps < 1/theta - 1`, it excludes near-minimal models.
  * So no nontrivial fixed-point-free model exists.
  * By Lemma 2.1 every model is then trivial, and `R^x` is not `F_2`-linear sofic.
* **A shrinking operation.** Any construction taking a nontrivial fixed-point-free model `sigma` to
  another whose normalized defect is at most `theta · delta(sigma)`, with `theta < 1`. Range and
  kernel restrictions of commuting defects are not such operations (Remark 4.2).
* **An explicit gap above an explicit ceiling.** A quantitative corner locality whose constant
  exceeds the best upper bound on fixed-point-free defects. The only explicit ceiling known is
  `1/2`, from square zero, and the gap constant cannot exceed it when models exist.

**Inputs not yet used.**
* **Halving.**
  * Inserting `1 = s_0 t_0 + s_1 t_1` gives
    `iota_A(x_12(1)) = (1 + S[A00]T[A100]) (1 + S[A01]T[A101])`: two commuting transvections on
    disjoint child pairs.
  * So `N^A_12 = a + b + ab`, with `a` and `b` commuting and square-zero, and similarly
    `N^A_23 = c + d + cd`.
  * Hence `D_A` expands into two child-triple defects `ca` and `db`, plus cross terms `cb` and `da`
    on four disjoint cylinders, plus higher products.
  * This is the natural relation between cylinder defects at different depths, and the natural
    source of a strict deficit. I found no bound from it.
* **The compressor collision** `q sigma(u) q != 0` and property (T) of `Gamma`. Neither enters
  Sections 2 to 4, and I found no way to turn either into an upper bound.

**Calibration.**
* **The gap needs corner locality.** The Toeplitz group `H` has fixed-point-free models with
  defect `0` (Remark 2.6), so Section 2 fails there.
* **What a proof must exclude.** Independent tensor factors realize `theta = 1`: if two commuting
  groups act through `rho_1 (x) rho_2`, then `rk(D_1 (x) D_2) = rk(D_1) rk(D_2)`. A proof of strict
  submultiplicativity must therefore show that the cylinder subgroups of `R^x`, which are
  `V`-conjugate inside a simple group, cannot act as independent tensor factors in a rank model.
