# Two-root certificates separate: the gate lower bounds are matrix-state arguments

Lane `w6-upg-separate`, 2026-09-12. Verifier `w4-vf-linear-b`.

It supports:
- `two-root-gate-lower-bounds-hold-for-matrix-states` (new);
- `commuting-jordan-certificates-flatten-to-minors` (new);
- Attempts entries on `anti-central-weakly-finite-images-carry-rank-functions` (U1b) and on
  `ternary-anti-central-disjoint-defects-have-a-strict-deficit`.

Sources, read at main `70e19044b`:
- [TRI] `research/artifacts/el3-two-root-identities-2026-09-12.md`;
- [RR] `research/artifacts/el3-rank-ring-rigidity-2026-09-12.md`;
- [GATE] `research/artifacts/sylvester-rank-function-two-root-gate-2026-09-12.md`;
- [GAP] `research/artifacts/state-upgrade-rank-condition-gap-2026-09-12.md`;
- [KT] `research/artifacts/state-upgrade-kill-test-2026-09-12.md`;
- [FL] `research/artifacts/separated-triangular-certificates-flatten-2026-09-12.md`;
- [WF] `research/artifacts/weakly-finite-representations-of-ternary-leavitt-units-2026-09-12.md`;
- [C3] `research/artifacts/char-three-defect-gap-and-descent-2026-09-12.md`.

## 0. Summary

**The question.** Does every triangular step in the two-root defect arguments separate, in the sense of
`separated-triangular-steps-flatten-to-minors`? If so, the gate arguments transfer from rank functions to
states. Then decide (U1b) on the weakly finite image `W` of `S_-`, or name the first mixing step.

**Answers.**
1. **Census (Section 1).** [TRI] Theorem A and D.2, [RR] Propositions 6 and 8 and Corollary 9, and the
   push-through identity contain no triangular step. They are ring identities, or minor equivalences
   through invertible block operations. The counting step of [GATE] Theorem 1 is the minor certificate
   `p_1 (+) p_1 ~ p_1`. So they separate, vacuously.
2. **Transfer (Section 2).** These arguments use only the axioms of a *matrix state* ([KT] Section 1):
   normalization, `d(XMY) <= d(M)`, and additivity on block sums. So the two-root criterion holds for
   matrix states (Theorem 2.2), and so does the lower-bound half of [C3]: the gap `c_3 > 0`, compressions,
   sign-sector halves, and Theorems 3.1.2–3.1.4 (Theorem 2.3). A ring carries a matrix state iff it has the
   rank condition, iff it has a `K_0` state. This is the transfer to states in the form the counterexample
   chain uses.
3. **Upper bounds (Section 3).** The one triangular tool in the gate program is the Frobenius–Jordan bound
   `N(xP) <= (1 - 1/m) N(P)` for commuting `x` with `x^m = 0` ([C3] Lemma 1.1.4, used in both `2/3` bounds).
   Its certificate separates on idempotent minors: `f <~ xP` gives `f^((+)m) <~ P^((+)(m-1))` through minors
   (Theorem 3.1). On values of non-idempotents it is a genuine rank-function axiom. A matrix state on
   `F_3[C_3]` gives `x - 1` the value `1` (Example 3.3).
4. **(U1b): not decided.** No argument on main contains a mixing step. The lower bounds are matrix-state
   arguments, and the upper bounds flatten on idempotent minors. So separation neither builds a rank
   function on `W` nor obstructs one. What distinguishes rank functions from states is their values on
   non-idempotents such as `D` and `P_k`, which idempotent-minor flattening does not reach (Section 4.1).
5. **The No branch (Section 4.2).** Outside its target, the route
   `ternary-rank-kill-via-anti-central-defect-deficit` uses only facts that hold for matrix states. If target
   items 1–2 hold for anti-central matrix states, then `S_-` fails the rank condition and the swap corner
   is full, with no (U1). Example 3.3 warns that item 2 is an upper bound, and matrix states can break those.
6. **A ring with the rank condition and no Sylvester rank function.** None is recorded locally (Section 4.3).
   The literature was not re-read here, so any claim about it is unverified.

## 1. Census of certificates

**Conventions.**
- `<~` is the minor order `M = X N Y`, and `M ~ N` means `M <~ N <~ M`. Invertible block operations give `~`.
- A *matrix state* `d` is additive on `(+)`, `<~`-monotone, with `d(I_1) = 1` ([KT] Section 1). Every
  Sylvester matrix rank function is one.
- A triangular step is `A (+) B (+) Z -> [[A, C],[0, B]] (+) Z`. It is the only axiom a rank function has
  beyond a matrix state ([KT] Theorem 2.1(a)).

**Facts for matrix states** (minors and additivity only).
- (M1) All zero matrices are `~`-equivalent, so `d(0) = d(0 (+) 0) = 2 d(0) = 0`, and `d >= 0` since `0 <~ M`.
- (M2) *Subadditivity.* `X + Y = [I I] (X (+) Y) [I I]^T`, so `d(X + Y) <= d(X) + d(Y)`. A matrix is the sum
  of its entries placed at matrix units, and each entry is a minor of it. So `d(M) = 0` iff `d(x) = 0` for
  every entry `x`.
- (M3) *Invariance.* `d(UXV) = d(X)` for invertible `U`, `V`.
- (M4) *Null ideal.* `ker d = {x : d(x) = 0}` is a two-sided ideal, proper since `d(1) = 1`. By (M2),
  `d(X + K) = d(X)` when `K` has entries in `ker d`, so `d` descends to a faithful matrix state on `A/ker d`.
- (M5) *Fields.* Over a field `M ~ I_r (+) 0`, so `d` is the rank.

**1.1 [TRI] Theorem A (matrix units).** Put `N_ij = sigma(x_ij(1)) - 1`. Hypothesis: `N_ij^2 = 0` and
`N_jk N_ij = 0` hold exactly in a ring. The squares come from `D = 0` through
`reversed-root-pair-identity-forces-root-squares-to-vanish`, which uses group relations and units only.
- `sigma(x_ij(1))^(-1) = 1 - N_ij`.
- If `X^2 = Y^2 = YX = 0`, expanding gives `[1 + X, 1 + Y] = 1 + XY`. With `x_ik(1) = [x_ij(1), x_jk(1)]`
  this gives `N_ik = N_ij N_jk`.
- `p_i = N_ij N_ji` is idempotent and independent of `j`, and `p_i p_j = 0`.

Certificate: none. Every step is an identity.

**1.2 [TRI] Theorem D.2 (triviality).** `p_1 = 0` gives `u_1j = u_i1 = 0` and `u_ij = u_i1 u_1j = 0`. The
kernel is normal and contains every root element. Certificate: none.

**1.3 [RR] Proposition 6 (`p = 2`).** In `4 x 4` blocks over `(p_1, p_2, p_3, f)`, commuting with the matrix
units forces `Z = D(E_11 + E_22 + E_33) + C E_13 + P E_14 + Q E_43 + S E_44`. Comparing with the five-term
expansion `n([g,h]) = xy + yx + xyx + yxy + xyxy` forces `D = P = S = Q = 0`. So `n_ij(a) = C(a) E_ij`, and `C`
is a unital ring map. Certificate: none.

**1.4 [RR] Proposition 8 (`p` odd).**
- On `p_1 + f + p_3`, `n` is upper triangular with diagonal `(D, S, D)`, so `n^p = 0` gives `D^p = S^p = 0`.
- The torus element `h = diag(-1,-1,1)` gives `2D + D^2 = 0`, `2S + S^2 = 0` and `2Q + QD + SQ = 0`. Since `D`
  is nilpotent and `2` is a unit, `2 + D` is a unit and `D = 0`. Likewise `S = 0`, and then `Q = 0`.
- `h' = diag(1,-1,-1)` gives `P = 0`, and Weyl transport finishes.

Certificate: none. "Upper triangular" is the shape of a matrix identity here, not a triangular rank step.

**1.5 [RR] Corollary 9.** `psi_ij` is additive, `[1 + X, 1 + Y] = 1 + XY`, and `C(a) = psi_12(a) u_21`.
Certificate: none.

**1.6 Push-through ([GAP] Lemma A.1).** For `A` of size `n x m` and `B` of size `m x n`,

```text
[[I_n, A],[B, I_m]] = [[I_n, 0],[B, I_m]] · [[I_n, 0],[0, I_m - BA]] · [[I_n, A],[0, I_m]]
                    = [[I_n, A],[0, I_m]] · [[I_n - AB, 0],[0, I_m]] · [[I_n, 0],[B, I_m]].
```

So `I_n (+) (I_m - BA) ~ (I_n - AB) (+) I_m` through invertible operations. Certificate: two minor
equivalences, no triangular step. For a matrix state, `n + d(I_m - BA) = d(I_n - AB) + m`.

**1.7 [GATE] Theorem 1, the counting step.** `C : R -> p_1 B p_1` is unital. Put `e_i = C(s_i t_i)`.
- `p_1 = C(t_i) e_i C(s_i)` and `e_i = C(s_i) p_1 C(t_i)`, so `p_1 ~ e_i`.
- `e_0 e_1 = e_1 e_0 = 0` and `e_0 + e_1 = p_1`. So `p_1 <~ e_0 (+) e_1` through `[1 1]`, and
  `e_0 (+) e_1 <~ p_1` through `[e_0; e_1] p_1 [e_0, e_1]`.
- So `p_1 (+) p_1 ~ e_0 (+) e_1 ~ p_1`, and every matrix state has `d(p_1) = 0`.

Certificate: minor steps only. It is also the `K_0` identity `[p_1] = 2[p_1]`.

**1.8 [GATE] Theorem 1, steps 1 and 5.** Step 1 passes to the null quotient, which is (M4) for a matrix
state. Step 5 is D.2 together with the classification of rank functions that kill every `1 - [g]`. For a
matrix state that classification is (M2) with (M5) (Theorem 2.2, step 3).

| argument | triangular steps | axioms used |
|---|---|---|
| [TRI] Theorem A, D.2; [RR] Propositions 6, 8, Corollary 9 | 0 | ring identities |
| push-through | 0 | invertible operations |
| [GATE] Theorem 1, steps 1, 4, 5 | 0 | minors, additivity |
| [C3] Lemmas 1.1.1, 1.1.3, 1.1.5, 1.2, 1.3, 1.4; Fact 1.5 | 0 | minors, additivity |
| [C3] Theorem 2.1.1 (positivity, attainment), 2.1.2, 2.1.3; Theorems 3.1.2–3.1.4 | 0 | the above, compactness |
| [C3] Lemmas 1.1.2, 1.1.4; `c_3 <= 2/3`; Theorem 3.1.1 | Frobenius steps | triangular axiom |

So every triangular step in the two-root defect arguments is a Frobenius step of [C3] Lemma 1.1.2, used only
inside the Jordan bound of Lemma 1.1.4. The [C3] rows are checked in Theorem 2.3.

## 2. The gate lower bounds for matrix states

**Lemma 2.1 (null quotients are weakly finite).** If `d` is a matrix state on `A`, then `A/ker d` is weakly
finite.

*Proof.* Suppose `XY = I_n + K` with the entries of `K` in `ker d`. Then `d(I_n - XY) = 0` by (M2). Push-through
(1.6) with `m = n` gives `n + d(I_n - YX) = 0 + n`. So the entries of `I_n - YX` lie in `ker d`, by (M2). QED

**Theorem 2.2 (two-root criterion for matrix states).** Let `K` be a field of characteristic `p > 0`,
`R = L_K(1,2)` and `Γ = R^x`, identified with `EL_3(R)` as in [WF] Theorem 2. Let `A` be a unital `K`-algebra with a matrix state `d`, let
`rho : Γ -> A^x` be a homomorphism, and put `N_ab = rho(x_ab(1)) - 1` and `D_rho = N_23 N_12`. If `d(D_rho) = 0`, then `d(rho(g) - 1) = 0`
for every `g`. For `A = K[Γ]` with `rho` the inclusion, `d` is the augmentation rank.

*Proof.*
1. `B = A/ker d` is a weakly finite `K`-algebra (Lemma 2.1), and `D_rho = 0` in `B`.
2. `weakly-finite-leavitt-representations-killing-defect-are-trivial` ([WF] Theorem 2) makes `rho` trivial
   modulo `ker d`.
3. On `K[Γ]`, every entry of `X - eps(X)` is a combination of the `[g] - 1`, so `d(X) = d(eps(X))` by (M2).
   Then (M5) gives `d(X) = rk(eps(X))`. QED

Second proof of step 2, with no weak finiteness: in `B` the faithful state `d` kills `p_1` by 1.7, so `p_1 = 0`,
and D.2 finishes.

**Theorem 2.3 (characteristic-three lower bounds for matrix states).** Let `G = L_(F_3)(1,2)^x`, and let
`A_mat` be the set of matrix states `d` on `F_3[G]` with `d(eps_-) = 1`. With `N` replaced by `d` and `A_S` by
`A_mat`, the following statements of [C3] hold.
1. Lemmas 1.1.1, 1.1.3, 1.1.5 and Fact 1.5.
2. Lemma 1.2: if `P` commutes with `phi(A')` and `d(P) > 0`, then `d(phi(X) P)/d(P)` is a matrix state on `A'`.
3. Lemma 1.3: `K_d = {h : d(1 - [h]) = 0}` is a normal subgroup, and `K_d = G` forces `d = rk o eps`.
4. Lemma 1.4: if `d(D_A) = 0` for one prefix `A`, then `d(eps_-) = 0`.
5. Theorem 2.1.1–2.1.3 without the upper bound. `A_mat` is compact. When it is nonempty,
   `c_3^mat = min {d(D) : d in A_mat}` is attained and positive. Every matrix state has
   `d(D eps_-) >= c_3^mat d(eps_-)`. Every `d` in `A_mat` has `d(Q_A) = 1/2` and `d(D_A) >= d(D_A Q_A) >= c_3^mat/2` for every nonempty
   proper prefix `A`.
6. Theorems 3.1.2–3.1.4: `f(k+1) >= d(D_B Q_B P_k) >= c_3^mat h_k`, `h_k >= d(R_+ P_k)/2`, and `h_k = 0`
   forces `f(k+1) = 0`.

Also, `A_mat` is nonempty iff `S_-` has the rank condition, iff the swap corner is not full. And `c_3^mat <= c_3`.

*Proof.* Each item reruns the [C3] proof, which uses nothing beyond (M1)–(M5) outside the excluded bounds.
1. The proofs are `[1 1]` factorizations, the involution `U = [[e, 1-e],[1-e, e]]` with column operations,
   and conjugation by units.
2. `(X (+) Y)'P = X'P (+) Y'P`. Since `P` commutes with `phi(A')`, `(XMY)'P = X'M'PY' <~ M'P`.
3. `1 - [gh] = (1 - [g]) + [g](1 - [h])`, with (M2) and (M3). If `K_d = G`, use Theorem 2.2, step 3.
4. `d o F_3[iota_A]` is a matrix state killing `D`. By Theorem 2.2, `iota_A(G) <= K_d`. `K_d` is normal and not
   contained in `<z>` so `K_d = G` by the second bullet of [C3] Lemma 1.3 (fp-simplicity of `G/<z>`,
   `odd-leavitt-unit-groups-mod-scalars-are-fp-simple`, and perfection), and
   `d(eps_-) = d(2(1 - [z])) = 0`.
5. Matrix states are cut out of `prod_M [0, c(M)]`, where `c(M)` is the column count, by closed conditions,
   since `M <~ I_c`. `d(eps_-) = 1` is closed, and `d -> d(D)` is continuous. Positivity is item 4 with the
   empty prefix. [C3] 2.1.2–2.1.3 use items 1–2, `V`-conjugation and the identity
   `Q_(X\A) eps_- = (1 - Q_A) eps_-`.
6. [C3] 3.1.2–3.1.4 use Theorem 2.1.1, Lemmas 1.1.1, 1.1.3, 1.1.5, 1.2, 1.3 and Fact 1.5 only.

For nonemptiness, `sylvester-rank-functions-iff-no-triangular-certificate` item 2 gives a matrix state on
`S_-` iff `S_-` has the rank condition. Pull it back along `F_3[G] -> S_-`, or restrict in the other
direction. `twisted-leavitt-corner-fullness-equals-absence-of-k0-states` ties this to the corner. Finally,
`A_S` is contained in `A_mat`. QED

**What does not transfer.** Only the upper bounds `c_3 <= 2/3` and [C3] Theorem 3.1.1, `f(k+1) <= (2/3) f(k)`.
Section 3 shows why.

## 3. Upper bounds: separated on idempotents, not on values

**Theorem 3.1 (commuting Jordan certificates flatten).** Let `A` be a unital ring, `x` and `P` square
`n x n` matrices with `xP = Px` and `x^m = 0`, and `f` an idempotent matrix with `f <~ xP`. Then

```text
f^((+)j) <~ P^((+)(j-1)) (+) x^j P        for 1 <= j <= m,        so   f^((+)m) <~ P^((+)(m-1)).
```

*Proof.* Induction on `j`; the case `j = 1` is the hypothesis.
1. **Separated step.** Write `f^((+)(j+1)) = f^((+)j) (+) f`. Take the first diagonal block `x^j P` with
   padding `P^((+)(j-1))`, and the second block `xP` with empty padding. By the induction hypothesis
   (up to a permutation) and `f <~ xP`, `separated-triangular-steps-flatten-to-minors` with corner `P` gives
   `f^((+)(j+1)) <~ [[x^j P, P],[0, xP]] (+) P^((+)(j-1))`.
2. **Frobenius matrix.** Right multiplication by `[[I, 0],[-x^j, I]]` and then left multiplication by
   `[[I, 0],[-x, I]]` give
   `[[x^j P, P],[0, xP]] -> [[0, P],[-x^(j+1) P, xP]] -> [[0, P],[-x^(j+1) P, 0]]`,
   using `P x^j = x^j P`. A permutation and a sign give `P (+) x^(j+1) P`.
3. So `f^((+)(j+1)) <~ P^((+)j) (+) x^(j+1) P`. At `j = m` the last block is `0`, and dropping it is a minor
   step. QED

**Corollary 3.2 (`K_0` reading).** Let `s` be a state on `(K_0(A), [A])`. Put
`rho^s(M) = sup {s[f] : f <~ M, f idempotent}` and `rho_s(M) = inf {s[e] : M <~ e, e idempotent}`. Then
`rho^s(xP) <= (1 - 1/m) rho_s(P)`.

*Proof.* If `P <~ e`, then `f^((+)m) <~ e^((+)(m-1))`. An idempotent minor `f' = X e' Y` of an idempotent `e'`
satisfies `f' = (f'Xe')(e'Yf')`, so `[f'] <= [e']` in `K_0`. Then `m s[f] <= (m-1) s[e]`. QED

- With `P = I_n` this is `nilpotent-jordan-certificates-flatten-to-minors`.
- With `x = N^B_12`, `P = P_k` and `m = 3`, it is [C3] Theorem 3.1.1 on idempotent minors.

**Example 3.3 (a matrix state that breaks the Jordan bound).** Let `R = F_3[C_3] = F_3[u]/(u^3)`, with
`u = x - 1`. For a matrix `M` over `R`, let `d(M) = dim_(F_3) soc(Im M)`, where `Im M` is the column space.
Then `d` is a matrix state and `d(u) = 1`. Every Sylvester rank function has `rk(u) <= 2/3`.

*Proof.*
- `R` is a chain ring, so every finitely generated module is a sum of cyclics `R/(u^i)`, each with a
  one-dimensional socle. So `d(M) = mu(Im M)`, the minimal number of generators, and `d` is additive with
  `d(I_1) = 1`.
- If `M = XNY`, then `Im M ⊆ X(Im N)`. Socle dimension does not increase on submodules, and `mu` does not
  increase on images. So `d(M) <= mu(X Im N) <= mu(Im N) = d(N)`.
- `Im u = (u)` is cyclic, so `d(u) = 1`. The Sylvester bound is [C3] Lemma 1.1.4 with `P = 1`. QED

**What the example shows.**
- Here a matrix state breaks the Jordan bound on a non-regular element, a bound every rank function obeys.
- Theorem 3.1 recovers only the idempotent shadow of that bound, and here the shadow is empty. An idempotent
  `f <~ u` has entries in `(u)`, so `f = f^3 = 0`.

## 4. Where it stops

**4.1 (U1b) is not decided by separation.**
- **What holds on `W`.** Every matrix state on `W` satisfies Theorem 2.3, with `eps_- = 1`. Every state
  satisfies Corollary 3.2. Neither result produces a Sylvester rank function or obstructs one.
- **No mixing step in the surveyed arguments.** Every triangular step in them is a Frobenius step inside a
  commuting Jordan bound, and Theorem 3.1 separates its idempotent-minor form. A mixing step would have to come from an
  argument not yet written. The likeliest source is a proof of the deficit target (4.2).
- **The gap is in values, not steps.** A rank function on `W` must give `D`, `N_12` and `P_k` values that
  satisfy both the lower bounds of Theorem 2.3 and the Jordan upper bounds on those non-idempotents.
  Matrix states supply the first and can break the second (Example 3.3). Flattening reaches only idempotent
  minors.
- **Next test.** Does `D` have a nonzero idempotent minor in `W`? `W`'s states are faithful, so this is the
  same as `rho^s(D) > 0` for any state `s`. If `D` has none, no state bounds `d(D)` from below, and a rank
  function on `W` must choose that value with no input from `K_0`.

**4.2 Consequence for the No branch.**
- **What the route uses.** Outside its target, `ternary-rank-kill-via-anti-central-defect-deficit` uses [C3]
  Theorem 2.1.1 (positivity and attainment), 2.1.2, 3.1.2 and 3.1.4, and the identity
  `eps_- = 2(1 - [z])`. All of these hold on `A_mat` (Theorem 2.3).
- **What follows.** Suppose items 1–2 of `ternary-anti-central-disjoint-defects-have-a-strict-deficit` hold for
  every `d` in `A_mat`, with the compression taken in the matrix-state sense of Theorem 2.3.2. Then the route
  gives `A_mat = ∅`. So `S_-` fails the rank condition, has no `K_0` state, and the swap corner is full
  (`twisted-leavitt-corner-fullness-equals-absence-of-k0-states`, which also gives that `G` is not
  surjunctive). No (U1) is used.
- **The warning.** Item 2 is an upper bound. Matrix states can break upper bounds that rank functions obey
  (Example 3.3), so item 2 on `A_mat` is stronger than on `A_S` and may fail.
- **Where mixing would sit.** If item 2 needs the triangular axiom on non-idempotent values, that is where the
  first mixing step of a No certificate would appear.

**4.3 Rings with the rank condition and no Sylvester rank function.**
- **Local record.** The [KT] Section 1 table lists "rank condition => SMRF" as open. [FL] Section 5 says no such
  ring is known. `rank-condition-rings-carry-sylvester-rank-functions` is OPEN, and its Attempts list the
  literature as not checked.
- **Unverified.** Not re-read here: whether Malcolmson's work on rank functions, Schofield's *Representations
  of Rings over Skew Fields* (Chapter 7) or Jaikin-Zapirain's survey settle the question.
- **Not a counterexample.** Example 3.3 is not such a ring, since `F_3[C_3]` has Sylvester rank functions. It
  only separates matrix states from rank functions.
