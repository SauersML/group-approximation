
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
