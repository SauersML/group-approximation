---
rg: 2
id: higman-bounded-derived-length-tower-chain-proof
kind: route
title: Tower invariants carry a k-th derived commutator of the opposite pair through k alternating b- and d-conjugations to a nonzero exponent sum, reducing derived length k to k - 1
target: higman-bounded-derived-length-edge-images-collapse
requires:
  - virtually-metabelian-edge-images-collapse-higman-quotients
  - nilpotent-edge-images-collapse-higman-quotients
  - higman-derived-length-three-edge-images-collapse
artifacts:
  - experiments/higman-two-sided-ladder-2026-09-18/tower.py
  - experiments/higman-two-sided-ladder-2026-09-18/tower-output.txt
  - experiments/higman-two-sided-ladder-2026-09-18/ladder4.py
  - experiments/higman-two-sided-ladder-2026-09-18/ladder4-output.txt
---

Conventions: `x^y = y^-1 x y` and `[x,y] = x^-1 y^-1 x y`.

We use the notation of `higman-derived-length-three-edge-collapse-proof`. Let `Q = H4/R`, fix `m >= 1`, and put

```text
alpha = a^m,  gamma = c^m,  P = 2^m,  N_j = 2^(P^j) (j >= 0),  A = <alpha, gamma> <= Q.
```

Let `Phi` be the free group on `alpha, gamma`. The following are taken from Steps 1–2 of that proof:
- the substitutions `iota_b`, `iota_d`;
- **Lemma 1**: `ev(iota_b(w)) = b^-1 ev(w) b` when `w` has `alpha`-exponent sum 0 and all `gamma`-letters
  are at `alpha`-height `>= 0`, and mirrored for `d`;
- **Lemma 3** (separation): if `delta != 0` is supported on `[h_1, ∞)` with `||delta||_1 < N_(h_1)`, then
  `sum_h delta_h N_h != 0`.

For `k >= 2`, let `T(k)` be the statement: *for every quotient `Q` and every `m >= 1`, `A^(k) = 1`
implies `Q = 1`.* `T(2)` is item 1 of `virtually-metabelian-edge-images-collapse-higman-quotients`, and
`T(3)` is item 1 of `higman-derived-length-three-edge-images-collapse`.

## Step 1 (tower invariants)

Fix a **flavour**, `d` or `b`.
- **Kinds.** In flavour `d`, the `alpha`-letters have kind 0 and the `gamma`-letters have kind 1. In
  flavour `b` it is the other way round.
- **Height.** The *height* of a kind-0 letter is the net exponent of the kind-1 letters before it. So
  it is the `gamma`-height in flavour `d` and the `alpha`-height in flavour `b`.
- **Level.** A letter `x` of kind `r mod 2` gets a *type* `tau_r(x)` for each level `r >= -1` of that
  parity:

  ```text
  tau_(-1)(x) = *                                   (x of kind 1)
  tau_0(x)    = height of x                         (x of kind 0)
  tau_r(x)    = ( tau_(r-2)(x), Pi_(r-1)(x) )        (r >= 1)
  Pi_(r-1)(x) = sum over earlier letters y of kind (r-1) mod 2 of eps_y [tau_(r-1)(y)]
  S_r(u)      = sum over letters x of kind r mod 2 of eps_x [tau_r(x)]
  ```

  Here `Pi_(r-1)(x)` and `S_r(u)` are finite formal `Z`-combinations of types.
- **Small levels.** `S^d_0` is the count `E^d` of the `k = 3` proof. `S^d_1` is its count `S`: the
  type of a `gamma`-letter is `(*, kappa)`. `S^d_2` is the order-2 count of `ladder4.py`.

**Invariance.** Inserting an adjacent pair `x x^-1` changes nothing. The two letters have the same
kind and the same types, since nothing lies between them. So they cancel in every `S_r`, and in every
`Pi` of every later letter. Hence `S_r` is a function on `Phi`. A block `x^N` of equal letters
contributes `N eps [tau]`, since all its letters have the same types.

**Norm bound.** Every `Pi_j(x)` and every `S_j(u)` is a signed count of letters of `u`, so its
`l1`-norm is at most `|u|`.

## Step 2 (one step through `iota_d`)

Let `v` be a word whose `alpha`-letters all have `gamma`-height `>= 0`, and put `u = iota_d(v)`. Define
a map `sigma` from `d`-types of `v` to `b`-types, together with a weight `wt`:
- **Level 0.** `sigma(h) = *` and `wt(h) = N_h` (these are heights, the types of `alpha`-letters).
- **Level 1.** For a `gamma`-type `(*, sum_h c_h [h])`, `sigma` is the integer `sum_h c_h N_h`, and
  `wt = 1`.
- **Level `j >= 2`.** `sigma((tau, Pi)) = (sigma(tau), sigma_*(Pi))`. Here
  `sigma_*(sum_t c_t [t]) = sum_t c_t wt(t) [sigma(t)]`. On `alpha`-types, `wt(t) = N_(h(t))`, where
  `h(t)` is the height at the bottom of the nest. On `gamma`-types, `wt = 1`.

**Lemma A.** For every letter `x` of `v` and every copy `x'` of `x` in `u`,
`tau^b_r(x') = sigma(tau^d_(r+1)(x))`. Hence `S^b_r(iota_d(v)) = sigma_*(S^d_(r+1)(v))` for all `r >= 0`.

*Proof.* In `u`, each `gamma`-letter of `v` is kept, and each `alpha`-letter at `gamma`-height `h`
becomes `N_h` adjacent copies. Kind `j mod 2` in flavour `d` is kind `(j-1) mod 2` in flavour `b`. We
induct on `r`.
- **`r = -1`.** Both sides are `*`.
- **`r = 0`.** The `alpha`-height of a `gamma`-letter `l` in `u` is
  `sum over earlier alpha-letters of eps N_h = sigma(tau^d_1(l))`.
- **`r >= 1`.** The letters of the other kind before `x'` in `u` are the copies of the letters of the
  other kind before `x` in `v`. Copies of `x` itself have the kind of `x`, so they do not enter.
  - An `alpha`-letter `y` contributes `N_(h(y))` copies, each of type `sigma(tau^d_r(y))` by induction.
    A `gamma`-letter contributes one.
  - So `Pi^b_(r-1)(x') = sigma_*(Pi^d_r(x))`.
  - With the induction hypothesis for `tau_(r-2)`, this gives `tau^b_r(x') = sigma(tau^d_(r+1)(x))`.
- **Sums.** Summing `eps_x` times the number of copies gives the formula for `S^b_r`. ∎

`tower.py` (`one_step_check`) confirms Lemma A on 128 random words for `r = 0..3`, with `P = 2`,
comparing both sides as exact nested formal sums. `ladder4.py` confirms the case `r = 1` separately.

**Lemma B (injectivity).** Suppose every `alpha`-letter of `v` has `gamma`-height `>= h_*`, where
`N_(h_*) > 2|v|`. Then:
- **(I_j)** `sigma` is injective on the level-`j` `gamma`-types occurring in `v`, and on the occurring
  level-`j` `alpha`-types of any fixed height;
- **(II_j)** `sigma_*` is injective on formal sums of occurring level-`j` types of `l1`-norm `<= |v|`.

*Proof.* We induct on `j`. All coefficient differences below have `l1`-norm at most `2|v| < N_(h_*)`.
- **`j = 0`.** (I_0) is trivial. For (II_0), `sigma_*(sum c_h [h]) = (sum c_h N_h) [*]`, and Lemma 3
  applies to `c - c'`.
- **`j = 1`.** (I_1) follows from (II_0). Then (II_1) follows, since the weights are 1.
- **`j >= 2`, (I_j).** Write types as `(tau, Pi)`. Equal `sigma`-images give
  `sigma(tau) = sigma(tau')` and `sigma_*(Pi) = sigma_*(Pi')`. A fixed height passes to `tau`, so
  (I_(j-2)) gives `tau = tau'`, and (II_(j-1)) gives `Pi = Pi'`.
- **`j >= 2` even, (II_j).** Group the occurring `alpha`-types by their `sigma`-image. By (I_j), the
  types in a group have pairwise distinct heights, all `>= h_*`. Equality of the images gives, for each
  group, `sum_t (c_t - c'_t) N_(h(t)) = 0`. Lemma 3 then gives `c = c'`.
- **`j >= 3` odd, (II_j).** The weights are 1 and `sigma` is injective by (I_j). ∎

**Corollary.** Under the hypothesis of Lemma B, `S^d_(r+1)(v) != 0` implies `S^b_r(iota_d(v)) != 0`.
The mirror statements, for `iota_b` from flavour `b` to flavour `d`, hold by symmetry.

## Step 3 (the shift)

**Lemma C.** Let `u` be a word, `r >= 0`, and `S^d_r(u) != 0`. Then
`S^d_r(gamma^n u gamma^-n) = 0` for at most one `n >= 0`. The mirror statement holds for `S^b_r` and
`alpha^n`.

*Proof.* Put `v = gamma^n u gamma^-n`, and define `Theta` on `d`-types of `u`:
- `Theta(h) = h + n`;
- on odd levels, `Theta((tau, Pi)) = (Theta(tau), Theta_*(Pi))`;
- on even levels `r >= 2`, `Theta((tau, Pi)) = (Theta(tau), n [triv_(r-1)] + Theta_*(Pi))`.

Here `triv_1 = (*, 0)`, `triv_(j+2) = (triv_j, 0)`, and `Theta_*` pushes coefficients forward.

- **`Theta` computes the types of `v`.** The `n` leading `gamma`-letters shift every height by `n`. They
  add `n` letters of type `triv_(r-1)` before every `alpha`-letter. They contain no `alpha`-letters.
- **`Theta` is injective.** It is built from a translation and injective maps, by induction, and it
  fixes every `triv_j`.
- **The extra letters.** The leading letters have types `triv_r`. The trailing letters `gamma^-1` all
  have the type `Theta(e_r)`, where `e_r` is the type of a `gamma`-letter appended to `u`.
- **Even `r`.** `S^d_r(v) = Theta_*(S^d_r(u))`, which is nonzero.
- **Odd `r`.** `S^d_r(v) = Theta_*( S^d_r(u) + n [triv_r] - n [e_r] )`. So it vanishes only if
  `S^d_r(u) = n ([e_r] - [triv_r])`. The right side is 0 when `e_r = triv_r`, and otherwise it holds for
  at most one `n`. ∎

`tower.py` (`conjugation_check`) finds no exception on 128 random words for `r = 0..4` and `n = 0..6`.

## Step 4 (descent)

Let `P <= Phi` be the kernel of `Phi -> <alpha>`, free on `gamma_j = alpha^j gamma alpha^-j`
(`j in Z`), and let `P_(>=0)` be the free factor on `gamma_j`, `j >= 0`. Define `P_d` and `P_(d,>=0)`
by the mirror construction.
- A word lies in `P_(>=0)` iff it has `alpha`-exponent sum 0 and all its `gamma`-letters are at
  `alpha`-height `>= 0` (Lemma 1 of the `k = 3` proof).
- **Retraction.** The retraction `P -> P_(>=0)` gives `P_(>=0) ∩ P^(j) = P_(>=0)^(j)`.
- **Inclusion.** `Phi' <= P`, so `Phi^(j+1) <= P^(j)`.
- On `P_(>=0)`, `iota_b` is the endomorphism `gamma_j -> gamma_j^(N_j)`.

Hence **`u in Phi^(j+1) ∩ P_(>=0)` implies `iota_b(u) in P_(>=0)^(j) <= Phi^(j)`**, and the same holds
for `iota_d` and `P_(d,>=0)`. Conjugation by powers of `alpha` or `gamma` preserves `Phi^(j)`.

## Step 5 (the reduction)

**Proposition.** Let `k >= 3` and `m >= 1`. Assume:
- **(i)** `T(k-1)` holds;
- **(ii)** some `w_0 in Phi^(k) ∩ P_(>=0)` has `S^d_(k-2)(iota_b(w_0)) != 0` at `P = 2^m`.

Then, for every quotient `Q`, `A^(k) = 1` implies `Q = 1`.

*Proof.* Assume `A^(k) = 1`, so `ev(w_0) = 1`. Put `u_1 = iota_b(w_0)`. For `s = 1, ..., k-1`:
- if `s` is odd, put `v_s = gamma^(n_s) u_s gamma^(-n_s)` and `u_(s+1) = iota_d(v_s)`;
- if `s` is even, put `v_s = alpha^(n_s) u_s alpha^(-n_s)` and `u_(s+1) = iota_b(v_s)`.

The flavour at step `s` is `f_s = d` for odd `s` and `b` for even `s`.

- **Descent.** By Step 4, `u_s in Phi^(k-s)`. For `s <= k-1` this lies in `Phi'`, so `u_s` has exponent
  sums `(0, 0)`.
- **Evaluation.** Choose `n_s` so large that every kind-0 letter of `v_s` has height `>= h_*` with
  `N_(h_*) > 2|v_s|`. This is possible because `|v_s| = |u_s| + 2 n_s` grows linearly while
  `N_(n_s - c)` grows doubly exponentially. Then `v_s` lies in `P_(d,>=0)` (odd `s`) or `P_(>=0)` (even
  `s`), and Lemma 1 gives `ev(u_(s+1)) = 1` by induction.
- **Nonvanishing.** We show `S^(f_s)_(k-1-s)(u_s) != 0` by induction on `s`. For `s = 1` it is (ii).
  - Given it at `s <= k-2`, avoid the one bad `n_s` of Lemma C, so `S^(f_s)_(k-1-s)(v_s) != 0`.
  - Lemma B and its corollary then give `S^(f_(s+1))_(k-2-s)(u_(s+1)) != 0`.
- **The last step.** At `s = k-1`, `S^f_0(v_(k-1)) = sum_h c_h [h] != 0`, with all heights `>= h_*`.
  - The kind-0 exponent sum of `u_k` is `Y = sum_h c_h N_h`. Lemma 3 gives `Y != 0`.
  - The other exponent sum of `u_k` equals that of `u_(k-1)`, which is 0.
- **Mirror chain.** Run the same chain on the letter swap `alpha <-> gamma` of `w_0`, with `d` first.
  The relations of Step 1 of the `k = 3` proof are symmetric, and (ii) is carried to its mirror. The
  result has the other exponent sum nonzero.
- **Conclusion.** Let `L` be the lcm of the two nonzero exponents. Then
  `alpha^L, gamma^L in A'`, since `A/A'` is abelian and generated by `alpha, gamma`. So
  `<a^(mL), c^(mL)> <= A'`, and `(A')^(k-1) = A^(k) = 1`. By (i) at exponent `mL`, `Q = 1`. ∎

**Consistency.** The zero pattern is forced. If `S^d_r(u_1) != 0` for some `r < k-2`, the chain
stopped after `r + 2` half-steps would give `u_(r+2)` a nonzero exponent sum, contradicting
`u_(r+2) in Phi'`. So `S_0, ..., S_(k-3)` of `u_1` must vanish.

## Step 6 (certification of (ii) for `k <= 11`)

`tower.py` builds `w_0 = build(k)`. Put `x = gamma_1 gamma_0^-1`, `y = gamma_0^-1 gamma_1`,
`x_2 = gamma_0 gamma_1 gamma_0^-2` and `y_2 = gamma_1^-1 gamma_0 gamma_1^-1 gamma_0`, all in `Phi'`. The
words are layered commutators of these four: layer `i` lies in `Phi^(i)`, so `w_0 in Phi^(k)`.
- The `gamma`-letters of `w_0` are at `alpha`-heights 0 and 1, so `w_0 in P_(>=0)`.
- The lengths for `k = 2..11` are 14, 56, 250, 1002, 3610, 12714, 44262, 155166, 548278 and 1946466.

**The computation.** `u_1 = iota_b(w_0)` is processed in block form: each `gamma`-letter at height `j`
is one block of weight `N_j`. The types are hashed. A formal sum is hashed linearly,
`sum c_t hash(t) mod 2^61 - 1`.
- The hash of a type is a function of the type, so the hash of a sum is a function of the sum.
- Hence **a nonzero hash certifies a nonzero sum**. A collision can only hide a nonzero value.
- Only nonzero results are used as evidence.

**Exact runs, `m = 1, 2, 3, 4`.** For `k = 2..11`, `S^d_(k-2)(u_1)` has nonzero hash. The lower levels
come out zero, matching the forced pattern.

**Symbolic runs, all large `m`.**
- In `u_1`, an `alpha`-letter has `gamma`-height `2p + qM`, where `M = N_1 = 2^P` and `(p, q)` counts the
  earlier `gamma`-letters of `w_0` at `alpha`-heights 0 and 1. A `gamma`-weight is `2 c_0 + M c_1`.
- `tower.py` runs the recursion with `M` formal.
- **Specialization.** Distinct formal heights stay distinct when `M > 2 * (p-range)`. Distinct formal
  coefficients stay distinct when `M > 4 n_0`. Here `n_0` is the number of `gamma`-letters of `w_0` at
  height 0, which bounds `|c_0|` everywhere, and `alpha`-coefficients are plain integers.
- So, by induction on the level, specialization is injective on the types and on the coefficients. A
  nonzero formal `S_(k-2)` therefore stays nonzero for every `M` above the printed bound.
- The bounds are at most `2491832 < 2^32`, so the symbolic runs cover every `m >= 5` for all
  `k <= 11`. For `k <= 8` they already cover `m >= 4`.

**Cross-checks.**
- `crosscheck` recomputes the towers without hashing, as nested exact formal sums. On 260 words it
  agrees with the hashed run, in the hash values and in the zero patterns. These are the chain words
  for `k = 2, 3, 4` at `P = 2, 4`, and random words of `P_(>=0)`, including many with vanishing levels.
- For `k = 3` and `k = 4` the results agree with `ladder.py` and `ladder4.py`, which compute `S` and
  `S_2` directly on the expanded word `iota_b(w_0)`.
- Output: `tower-output.txt` and `ladder4-output.txt`.

## Step 7 (conclusion)

**Item 1.** By induction on `k` from `T(2)`, the Proposition with Step 6 gives `T(k)` for
`3 <= k <= 11`. For `k = 3` this reproves `higman-derived-length-three-edge-images-collapse`. The pair
`<b^m, d^m>` is handled by the automorphism `a -> b -> c -> d -> a`.

**Items 2–4.** These follow as in Step 6 of the `k = 3` proof.
- **Item 2.** Take `m = 1` and `Q = H4/ncl(F^(11))`.
- **Item 3.** Pass to the normal core `A_0` of finite index `m`, so `<a^m, c^m> <= A_0`.
- **Item 4.** Use the tree gate of `nilpotent-edge-images-collapse-higman-quotients`.

## What is open

The reduction is proved for every `k`. The only `k`-specific input is (ii).
- **Proving (ii) for all `k`** would give `T(k)` for every `k`. Every virtually solvable edge image
  would then collapse, as would every tree splitting of a nontrivial quotient over virtually solvable
  edge groups.
- **A Magnus-type route.** The levels behave like a Magnus embedding: `S_r` vanishes on the descent
  images of `Phi^(r+2)`, and on the chain words it is nonzero exactly at the top level.
- **What that route needs.** Identify the kernel of `S^d_r` on the kernel of `S^d_(r-1)` as an explicit
  term `D_(r+2)` of a series of `Phi`. Then show that `iota_b` does not map `Phi^(k) ∩ P_(>=0)` into
  `D_k`.
