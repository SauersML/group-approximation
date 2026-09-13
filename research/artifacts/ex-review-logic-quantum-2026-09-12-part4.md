# EX review, logic and quantum: part 4. Linear rounding over all bounded-exponent groups (ex-ugc-rounding-pgroups) and torsor CFI graphs (ex-kac-quantum-compiler)

Lane `ex-verify-logic-quantum`, 2026-09-13 01:40 CDT.  Index: `ex-review-logic-quantum-2026-09-12.md`.
Tip `7e94231157`.  Artifacts `ugc-rounding-normal-fibres-2026-09-13.md` (part 3) and `-part2-` (part 4)
were not read line by line; the node derivations were re-derived.

## 4.0 Verdicts

| item | verdict |
|---|---|
| `primitive-projective-representations-have-a-trace-gap` (+ `-proof`) | PASS |
| `normal-fibre-galois-games-round-linearly-over-m-groups` (+ `-proof`) | PASS |
| `normal-fibre-galois-games-round-linearly-over-all-groups` (+ `-proof`) | PASS.  The per-group bound is proved; the uniform-in-`m` bound uses CFSG, and the node says so |
| `galois-games-round-linearly-for-bounded-fibre-size` (+ `-proof`) | PASS |
| `abelian-normal-closure-fibres-round-linearly` (+ `-proof`) | PASS |
| `free-rounding-pays-the-number-of-fibre-conjugates` (+ `-proof`) | PASS (upper bound; lower bound up to the factor 3) |
| `torsor-cfi-isomorphism-algebra-is-coset-constraint-algebra` (+ `-proof`) | PASS |

Novelty: not rechecked (web-search budget exhausted).  Each node records a bounded check and claims no novelty
for the trace gap.

## 4.1 The trace gap: PASS

- **Reduction.**
  - With `N/Z` minimal normal above the scalars, primitivity makes `sigma|_N` homogeneous, so
    `V = V_tau (x) W` and `span sigma(N) = End(V_tau) (x) 1` (Burnside).
  - Skolem--Noether gives `sigma(x) = taut(x) (x) pit(x)`.  `pit` is an irreducible projective representation
    of `X/N`: invariant subspaces and blocks lift.
  - If `taut(h)` is scalar, induct on `|X|`, since sections of `X/N` are sections of `X`.
  - Otherwise `|tr sigma(h)|/d <= |tr taut(h)|/dim V_tau`.
- **Symplectic case.**
  - The commutator form on `N/Z` is `X`-invariant.  By minimality its radical is `0` or everything, and
    "everything" would make `sigma(N)` span a commutative `End(V_tau)`.
  - The `U_v` are an orthonormal basis with `tr U_v = 0` for `v != 0`.
  - `g = 1`: `lambda` is a character, `= c(v_0, .)`, so `taut(h)` is a scalar times `U_(v_0)` with `v_0 != 0`,
    and the trace is `0`.
  - `g != 1`: comparing coefficients of `U_u` in `taut(h) U_w = lambda_w U_(gw) taut(h)` gives
    `|c_v| = |c_(v + (g-1)w)|`.  So `|c_0|^2 |Im(g-1)| <= 1` and `|c_0| <= p^(-1/2)`.
- **Tensor case.**
  - The Schur multiplier of `T^s` is `M(T)^s` because `T` is perfect, so `V_tau` is a tensor product of
    factors of dimension `d_0 >= 2`.
  - A nontrivial permutation `pi` has at most `s - 1` cycles, and each cycle contributes one trace of size
    at most `d_0`, so the ratio is `<= 1/d_0`.
  - For `pi = 1`, a non-scalar factor gives the ratio `<= gamma(T)`.
- **`gamma(T) < 1` is a finite maximum.**  Two normalizing unitaries inducing the same automorphism differ by a
  character of the perfect `T` times a commutant scalar.
- **Examples.**  `GL(2,3)` elements of order 8 have trace `zeta_8 + zeta_8^3`.  The standard representation of
  `S_n` has transposition ratio `(n-3)/(n-1)`.

## 4.2 Rounding theorems: PASS

- **The induced-character identity.**  For `rho = Ind_H sigma` and conjugation-invariant `mu`:
  - `lambda_rho = sum_g mu(g) chidot_sigma(g)/d_sigma`;
  - so `1 - lambda_rho = sum_g mu(g)(1 - Re chidot_sigma(g)/d_sigma)`;
  - the summand is `1` off `H`, `0` on `ker sigma`, `>= 1 - cos(2 pi/m)` on nontrivial scalars, and
    `>= 1 - gamma(H) >= 1 - gamma(G)` on non-scalars.
  - Hence `mu(G \ x ker(sigma) x^-1) <= (1 - lambda_rho)/c(G,m)` for every conjugate.
- **Good kernels.**  `K cap (intersection of good ker rho) = {e}`.  This uses only `phi = 0` on `K \ {e}`, so
  it holds for every `K`.  Also `ker Ind_H sigma` is the core of `ker sigma`.
- **Halving chain.**  `|N_i|` divides `k` and drops by a factor `>= q`, so `t <= log_q k`, and a union bound
  gives the mass.
- **Normal `K`.**  `L cap K = {e}` gives `L cap xKx^-1 = {e}`, so free-subgroup rounding applies.  For solvable
  `G`, `min(1 - cos(2 pi/m), 1 - 2^(-1/2)) = 1 - cos(2 pi/m)` when `m >= 8`.
- **M-groups.**  Linear `theta` gives the constant `1 - cos(2 pi/m)`.  Nilpotent groups are M-groups
  (classical).
- **Bounded fibre size.**
  - The `K`-core `intersection over b in K of b L_i b^-1` is normalized by `K`, omits `a`, and costs at most
    `k` conjugates.
  - `KL` is a subgroup, and permutable rounding (part 5 of `galois-games-round-through-free-subgroups`,
    re-derived in part 2 §2.6) gives the value.
- **Abelian normal closure.**
  - Clifford gives `rho = Ind_I psi` with `psi|_A = e theta`.
  - If `A cap xHx^-1 < A`, Mackey would put distinct extensions of a character into `psi|_A`.  So `A <= H`,
    and every conjugate of `ker sigma` is normal in a conjugate of `H` containing `A >= K`.
- **Free rounding pays `r`.**
  - Run the chain on each `K_j cap L`, for at most `r log_q k` steps in all.
  - The wreath example has `c = 1` (2-group, `m = 4`), an upper bound `3N eps` and a lower bound
    `(N-1) eps`.  So `r` is necessary up to the constant 3.

## 4.3 Torsor CFI isomorphism algebras: PASS

- **Blocks.**  `v^2` is killed by distinct vertex colours, so cross-context entries vanish.
- **Shift.**
  - Colour agreement from `(k,alpha)` to `(k,alpha')` forces `beta' = (beta alpha^-1) alpha'`.
  - Row `alpha'` then gives `u_(alpha,beta) <= u_(alpha', g alpha')`, and symmetry gives equality.
  - Squareness `|R_k| = |R'_k|` gives `g R_k = R'_k`.
- **Cross-context relation.**  `alpha_i^-1 alpha'_i = alpha_i^-1 g_i^-1 g'_i alpha'_i` iff `g_i = g'_i`.
- **Not a group dual.**
  - `Delta(p^k_g) = sum_h p^k_h (x) p^k_(g h^-1)` and `ev_g * ev_(g') = ev_(g'g)` give `C(L_k^op)`.
  - A nonabelian `L_k` is not cocommutative, and Hopf subalgebras of a group algebra are.
- **Credit.**  Over `F_2` this is Roberson--Schmidt Thm 3.8 / 6.7, checked at source in part 2 §2.4.
