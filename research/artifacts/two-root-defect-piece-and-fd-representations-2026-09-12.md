# The two-root defect piece, and what the absence of finite-dimensional representations buys

Lane `w3-gate-bridge-b`, 2026-09-12. Supports the Cairn claim
`leavitt-two-root-defect-piece-carries-a-nontrivial-rank-model` and the Attempts entry on
`rank-models-of-el3-satisfy-the-two-root-identities`. It continues Section 3 of
`research/artifacts/two-root-identity-nonsofic-mechanism-2026-09-12.md`.

## 0. Summary

* **Section 1 (established).** Take a nontrivial characteristic-two rank model of `R^x`. The
  defect piece `Q = im(N'_23 N'_12)` of the corner pair on `[1000]` is invariant under the nine-leaf
  Kazhdan subgroup `Gamma`, and never pointwise fixed by it.
  * `Gamma` acts on `Q` by a nontrivial, injective rank model of `R^x`, of normalized rank
    `delta = rk(N'_23 N'_12)`.
  * Every corner-pair product inside `Gamma` compresses nontrivially onto `Q`.
  * A compressor carrying the pair into `Gamma` compresses nontrivially onto `Q`.

  So the fixed case of step 1 of the mechanism artifact is closed, and the invariant case
  reproduces the whole problem on a corner.
* **Section 2 (next landing).** A calibration for input (ii): a finitely generated Kazhdan group
  with no nontrivial finite-dimensional representation, whose rank model violates the two-root
  identity and has a diffuse relative commutant.
* **Section 3 (next landing).** Where input (ii) can still enter.

Notation as in the mechanism artifact.
* `R = L_(F_2)(1,2)`, with prefix isometries `S[p]`, `T[p]`.
* `iota_P(g) = S[P] g T[P] + (1 - S[P]T[P])`, an injective endomorphism of `R^x`.
* `Gamma = iota_0(R^x)`, the units supported on `[0]`.
* `x' = iota_1000(x_12(1))`, `y' = iota_1000(x_23(1))`.
* `sigma : R^x -> M^x` is a homomorphism into the units of a rank ultraproduct `M` over a field
  of characteristic two.
* `N'_12 = sigma(x') - 1`, `N'_23 = sigma(y') - 1`, `P = N'_23 N'_12`.

`M` is von Neumann regular with a faithful rank function, so `PM = qM` for an idempotent `q`,
with `rk(q) = rk(P)`. A corner `eMe` with `e != 0` is again a rank ultraproduct after
renormalizing, because idempotents lift at finite stages.

## 1. The defect piece carries a nontrivial rank model

**Lemma 1.1 (invariant corners).** Let `sigma : G -> M^x` be a homomorphism, `S <= G` a subgroup,
and `q` an idempotent with `sigma(s) qM = qM` for every `s` in `S`. Then
`sigma(s) q = q sigma(s) q`, and `tau_q(s) = q sigma(s) q` is a homomorphism `S -> (qMq)^x`.

*Proof.* `sigma(s) q` lies in `qM`, so `sigma(s) q = q sigma(s) q`. For `s, t` in `S`,
`q sigma(s) q sigma(t) q = q sigma(s) sigma(t) q`, since `sigma(t) q = q sigma(t) q`. Also
`tau_q(1) = q`, and `tau_q(s^-1)` inverts `tau_q(s)`. QED

**Fixed right ideals.** For a subgroup `S` write `Fix_r(sigma(S)) = {x in M : sigma(s) x = x for
all s in S}`. For finitely generated `S` this is `eM` for an idempotent `e` with
`sigma(s) e = e` (Lemma 1 of `research/artifacts/rank-row-compression-audit-2026-09-12.md`). By
`leavitt-rank-models-kazhdan-fixed-ideals-are-global` in degree `(1,0)`,
`Fix_r(sigma(Gamma)) = Fix_r(sigma(R^x))`.

**Theorem 1.2.** Let `sigma` be a nontrivial characteristic-two rank model of `R^x`, and `q` an
idempotent with `qM = PM`.

1. `qM` is `sigma(Gamma)`-invariant, and `tau_Q(gamma) = q sigma(gamma) q` is a homomorphism
   `Gamma -> (qMq)^x`.
2. `tau_Q` is nontrivial. So `tau_Q o iota_0` is an injective rank model of `R^x` on the corner
   `qMq`, of normalized rank `rk(q) = rk(P) > 0`.
3. For every prefix `P'`, with `N^(0P')_ab = sigma(iota_(0P')(x_ab(1))) - 1`,

   ```text
   rk( q N^(0P')_23 N^(0P')_12 q ) > 0 .
   ```

4. `qM` is not contained in `Fix_r(sigma(Gamma))`.

*Proof.*

1. `x'` and `y'` are supported on `[1000]`, which is disjoint from `[0]`, so they commute with
   `Gamma`. Hence `P` commutes with `sigma(Gamma)`, and `sigma(gamma) PM = P sigma(gamma) M = PM`.
   Apply Lemma 1.1.
2. Suppose `tau_Q` is trivial, that is, `q sigma(gamma) q = q` for all `gamma` in `Gamma`.
   * **Fixed.** By Lemma 1.1, `sigma(gamma) q = q`, so `qM` lies in `Fix_r(sigma(Gamma))`. By
     globality it lies in `Fix_r(sigma(R^x)) = fM`, where `sigma(g) f = f` for every `g`. So
     `P = fP`.
   * **Quotient model.** Put `sigma_W(g) = (1-f) sigma(g) (1-f)`. From `sigma(g) f = f` we get
     `(1-f) sigma(g) f = 0`, so `sigma_W` is a homomorphism into `((1-f)M(1-f))^x`. If `f = 1`
     then `sigma` is trivial, a contradiction. Otherwise `(1-f)M(1-f)` is a rank ultraproduct
     over the same field.
   * **Its corner product vanishes.** `N'_23 f = (sigma(y') - 1) f = 0`, so
     `(1-f) N'_23 (1-f) = (1-f) N'_23`, and

     ```text
     (sigma_W(y') - (1-f)) (sigma_W(x') - (1-f)) = (1-f) N'_23 N'_12 (1-f) = (1-f) f P (1-f) = 0 .
     ```

     By `two-root-identity-is-corner-local-for-leavitt-rank-models` ((3) implies (1), prefix
     `1000`), `sigma_W` is trivial: `(1-f) sigma(g) (1-f) = 1-f` for every `g`.
   * **Square-zero rest.** Now `sigma(g) = f + f sigma(g) (1-f) + (1-f) = 1 + f sigma(g) (1-f)`.
     The elements `1 + a` with `a` in `fM(1-f)` form an abelian group, because
     `(1+a)(1+b) = 1 + a + b`. So `sigma` factors through the abelianization of `R^x`, which is
     trivial (`leavitt-gl-equals-el-and-perfect-unit-group`). So `sigma` is trivial, a
     contradiction.

   Hence `tau_Q` is nontrivial. `tau_Q o iota_0` is a nontrivial homomorphism
   `R^x -> (qMq)^x`, so it is injective because `R^x` is simple
   (`binary-leavitt-unit-group-is-simple`).
3. **Composing corners.** `iota_0 o iota_P' = iota_(0P')`:

   ```text
   iota_0(iota_P'(g)) = S[0P'] g T[0P'] + S[0]T[0] - S[0P']T[0P'] + 1 - S[0]T[0]
                      = S[0P'] g T[0P'] + (1 - S[0P']T[0P']) .
   ```

   So the `P'`-corner pair of the model `tau_Q o iota_0` is `iota_(0P')` of the unit pair, which
   lies in `Gamma`. By Lemma 1.1, `(sigma(gamma) - 1) q = q (sigma(gamma) - 1) q` for `gamma` in
   `Gamma`, so that model's corner product is
   `q N^(0P')_23 q N^(0P')_12 q = q N^(0P')_23 N^(0P')_12 q`. The model is nontrivial by (2), so
   corner locality ((1) versus (3)) makes this product nonzero.
4. This is (2). QED

**Corollary 1.3 (compressor collision).** Suppose `u` in `R^x` conjugates `(x', y')` to
`iota_(0P')` of the unit pair for some prefix `P'`. An example is a prefix replacement taking
`[1000]` onto `[0P']`, such as the configuration's compressor onto `[0001]`. Then
`q sigma(u) q != 0`.

*Proof.* The conjugated pair has product `sigma(u) P sigma(u)^-1`, so Theorem 1.2(3) gives
`q sigma(u) P sigma(u)^-1 q != 0`. Since `P = qP`, this equals
`q sigma(u) q P sigma(u)^-1 q`, so `q sigma(u) q != 0`. QED

**Remark 1.4 (what changes, and where it stops).**
* **Fixed case closed.** Step 1 of Section 3 of the mechanism artifact records that `Q` is
  invariant but not fixed, and that globality only reaches fixed objects. Theorem 1.2 shows the
  fixed case is impossible in a nontrivial model. Globality has therefore already been used in
  full.
* **Self-reproduction.** On `qMq`, `tau_Q o iota_0` has its own configuration and its own defect
  piece `Q_2 = im(q N^(01000)_23 N^(01000)_12 q)`, which lies in `Q`. Iterating gives nested
  corners `Q ⊇ Q_2 ⊇ Q_3 ⊇ ...`, each carrying a nontrivial rank model of `R^x`, with ranks
  `delta >= delta_2 >= ... > 0`.
* **Where it stops.** Nothing proved here gives `delta_(k+1) >= c delta_k` for a uniform `c`, or
  any other bound on the descent. A contradiction along this line must produce such a bound, for
  instance from Corollary 1.3 together with property (T) of `Gamma`.
* **Scope.** Only corner locality uses characteristic two. The rest holds for rank models over any
  field.
