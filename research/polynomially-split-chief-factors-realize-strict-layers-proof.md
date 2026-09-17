---
rg: 2
id: polynomially-split-chief-factors-realize-strict-layers-proof
kind: route
title: Layer-valued words form a finite ring of derivative functions whose maximal idempotent is the identity; the resulting splitting word turns strict linear layers and strict quotient automata into strict polynomial automata
target: solvable-polynomially-split-alphabets-two-way-kaplansky
requires:
  - solvable-polynomial-automata-reduce-to-kaplansky
  - nonlinear-certificate-fibers-are-all-surjective-or-all-strict
---

**Imported inputs.**
- **(P) Peeling proof** (`solvable-polynomial-automata-chief-series-peeling-proof`, the route of
  `solvable-polynomial-automata-reduce-to-kaplansky`). Used: Lemma 1.1 (affine form of a word along `A`),
  and Steps 2, 4, 5, 6 (fibre dichotomy, collision, surjectivity transfer). Step 3 there assumes `M_d(F_p[G])`
  directly finite; Lemma B.0 below replaces it.
- **(D) Fibre dichotomy** (`nonlinear-certificate-fibers-are-all-surjective-or-all-strict`), through (P).
- Conventions as in (P): the shift is `(h.x)(g) = x(h^-1 g)`, and `Pol_1(Q)` is the set of maps `Q -> Q` given by
  one-variable words with constants. It is a group under pointwise multiplication and is closed under composition.

**Setting.** `A = F_p^d` is abelian minimal normal in the finite group `Q`, written additively when convenient,
`B = Q/A`, `bar: Q -> B`, and `rho(b) a = x a x^-1` for any `x` over `b`.
- `A` is an irreducible `F_p[B]`-module, because `Q`-invariant subgroups of `A` are its submodules.
- `D = End_Q(A)` is a finite division ring, hence a field `F_q` (Wedderburn).
- By the Jacobson density theorem, `E = span_(F_p) rho(B) = End_D(A) = M_e(F_q)`, with `e = dim_D A`.
- Since `pA = 0`, `E` is also the set of `Z`-linear combinations of the `rho(c)`, `c in Q`.

**Step 0 (derivatives of one-variable words).** Let `u in Pol_1(Q)`. By Lemma 1.1 of (P) with `k = 1`,
`u(a q(b)) = (C(b) a + D(b)) q(ubar(b))` with `C(b) in E`. Hence for every `x` over `b` and `a in A`:

    u(a x) = (C(b) a) . u(x).

Put `phi_u(b) = C(b)`. The shadow `ubar: B -> B` lies in `Pol_1(B)`. The chain rule is

    phi_(v o u)(b) = phi_v(ubar(b)) phi_u(b).

To see it, write `v(u(ax)) = v((phi_u(b) a) u(x)) = (phi_v(ubar b) phi_u(b) a) v(u(x))`.

Let `K = { f in Pol_1(Q) : f(Q) <= A }` and `Phi = { phi_f : f in K }`, a subset of `E^B`. Then:
- `f` is nonconstant on `A` iff `phi_f(1) != 0`, since `f(a) = phi_f(1) a + f(1)`.
- `Q` is polynomially split along `A` iff `1 in Phi`.

**Step 1 (closure rules for `Phi`).** Let `f, g in K`, `c in Q`, `u in Pol_1(Q)`, and `b in B`.
1. **Sum.** `fg in K`, and `phi_(fg) = phi_f + phi_g`: `(fg)(ax) = (phi_f(b)a + f(x)) + (phi_g(b)a + g(x))`.
   The constants in `A` lie in `K`, with `phi = 0`.
2. **Conjugation.** Put `h(x) = u(x) f(x) u(x)^-1`. Then `h in K`, and `phi_h(b) = rho(ubar(b)) phi_f(b)`.
   - `u(ax) = a' u(x)` with `a' in A`, and conjugation of `A` by `a' u(x)` equals conjugation by `u(x)`.
   - So `h(ax) = rho(ubar b)(phi_f(b) a + f(x)) = rho(ubar b) phi_f(b) a + h(x)`.
   - With `u = c` constant, `Phi` is closed under left multiplication by `rho(c)`, hence by `E`.
   - With `u = id`, `rho . Phi <= Phi`.
3. **Right translation.** `h(x) = f(xc)` gives `phi_h(b) = phi_f(b cbar)`.
4. **Inner substitution.** `h(x) = f(c x c^-1)` gives `phi_h(b) = phi_f(cbar b cbar^-1) rho(c)`, by the chain
   rule with `u(x) = cxc^-1`, where `phi_u = rho(c)`.
5. **Product.** Put `u(x) = x g(x)`. Then `ubar = id`, and
   `u(ax) = a x (phi_g(b) a + g(x)) = (a + rho(b) phi_g(b) a) u(x)`, so `phi_u = 1 + rho phi_g`.
   - By the chain rule, `phi_(f o u) = phi_f + phi_f rho phi_g`, and `f o u in K`. So `phi_f rho phi_g in Phi`.
   - Since `rho(b)^|B| = 1`, rule 2 gives `phi = rho (rho^(|B|-1) phi)` with `rho^(|B|-1) phi in Phi`. So every
     element of `Phi` has the form `rho phi_g`, and `Phi Phi <= Phi`.

So `Phi` is a finite subring (possibly without unit) of `E^B`.

**Theorem A, proof.**

*"Only if".* If `f(ax) = a f(x)`, then `f(a) = a f(1)` is nonconstant on `A`.

*"If".* Let `f in K` be nonconstant on `A`, so `phi_f(1) != 0`.
- `Phi(1) = { phi(1) : phi in Phi }` is a left ideal of `E` (rules 1, 2) and a right ideal (rule 4 at `b = 1`).
  `E = M_e(F_q)` is simple, so `Phi(1) = E`. By rule 3, `Phi(b) = E` for every `b`.
- Every element of a finite multiplicative semigroup has an idempotent power. Choose one exponent `N` that
  works for all of `E^B`.
- For an idempotent `eps in Phi`, put `r(eps) = sum_b rank eps(b)`. Take `eps` maximizing `r`; `0 in Phi` is an
  idempotent, so the maximum exists.
- Suppose `eps(b0) != 1` for some `b0`. Choose `phi in Phi` with `phi(b0) = 1 - eps(b0)`. Then
  `psi = phi - eps phi - phi eps + eps phi eps` lies in `Phi`, and `psi = (1-eps) phi (1-eps)` in `E^B`. So
  `eps psi = psi eps = 0`, and `psi(b0) = 1 - eps(b0)`.
- `eta = psi^N in Phi` is an idempotent orthogonal to `eps`, with `eta(b0) = 1 - eps(b0) != 0`.
- `eps + eta` is an idempotent in `Phi`. For orthogonal idempotents the images are independent: if
  `v = eps x = eta y`, then `v = eps v = eps eta y = 0`. So `r(eps + eta) > r(eps)`, a contradiction.
- Hence `eps = 1`. So there is `f in K` with `phi_f = 1`, that is, `f(ax) = a f(x)`. ∎

*Sufficient conditions.*
- **(S1)** `p` does not divide `|B|`. Take `m` with `m = 0 mod exp(B)` and `m = 1 mod p`. Then `x^m in K`, and
  `a^m = a` for `a in A`.
- **(S2)** Some `c in Q` has `p` not dividing `n/o`, where `n = exp(B)` and `o = o(cbar)`, and has
  `sum_(i<o) rho(c)^i != 0`. Take `f(x) = (xc)^n in K`. Then
  `f(a) = (sum_(i<n) rho(c)^i) a + c^n = (n/o) (sum_(i<o) rho(c)^i) a + c^n`, which is nonconstant.

*Obstruction.* Suppose `A` is central and `p | exp(B^ab)`. Let `f in K` have exponent sum `sigma` in `x`.
- Map to `B^ab`: the value of `f` is trivial there, so `xbar^sigma (prod of constants) = 1` for all `xbar`.
- At `xbar = 1` the product of constants is `1`. So `exp(B^ab) | sigma`, hence `p | sigma`.
- Since `A` is central, `f(ax) = a^sigma f(x) = f(x)`. So `f` is constant on `A`, and Theorem A gives no split. ∎

**Lemma B.0 (linear surjunctivity over `D`).** Let `alpha: E[G] -> End_D(A^G)` be
`alpha(sum_h lambda_h h)(a)(g) = sum_h lambda_h a(gh)`. Then:
- `alpha` is an injective ring homomorphism.
- Its image is exactly the set of `D`-linear cellular automata on `A^G`.
- Every injective `D`-linear cellular automaton on `A^G` is surjective iff `E[G] = M_e(F_q[G])` is directly
  finite.

*Proof.*
- **Homomorphism.** `alpha(lambda h) alpha(mu k)(a)(g) = lambda mu a(ghk) = alpha(lambda mu hk)(a)(g)`.
- **Injective.** Evaluate on `a = delta_1 v`: the output at `g = h^-1` is `lambda_h v`.
- **Image.** A `D`-linear cellular automaton with memory `W` has a `D`-linear local rule `A^W -> A`, which is a
  sum of `D`-linear maps `A -> A`, one per coordinate.
- **Directly finite implies surjunctive.** Let `T = alpha(t)` be injective.
  - `A^G` is compact, so `T` is a homeomorphism onto its closed, shift-invariant image `Y`, and `T^-1: Y -> A^G`
    is uniformly continuous and equivariant. So there is a finite `W` such that `T^-1(y)(1)` depends only on
    `y|_W`.
  - The patterns `V = { y|_W : y in Y }` form a `D`-subspace, and `y|_W -> T^-1(y)(1)` is a well-defined `D`-linear
    map `V -> A`. Extend it `D`-linearly to `mu: A^W -> A`.
  - `S(y)(g) = mu((g^-1 . y)|_W)` is a `D`-linear cellular automaton with `ST = id`. So `S = alpha(s)` with
    `alpha(st) = 1`, hence `st = 1`.
  - Direct finiteness gives `ts = 1`, so `TS = id` and `T` is surjective.
- **Surjunctive implies directly finite.** Suppose `st = 1` but `ts != 1`. Then `T = alpha(t)` is injective,
  because `ST = id`. If `T` were surjective, `S = T^-1` and `alpha(ts) = TS = id`, so `ts = 1`, a contradiction.
  So `T` is a strict `D`-linear cellular automaton. ∎

**Theorem B.1 (forward, sharpened), proof.** Run (P), Steps 2–6, unchanged, except Step 3.
- In Step 3, the constant fibre `L_(c_beta) a (g) = sum_j C_j(beta,...,beta) a(g m_j)` has `C_j in E` (Lemma 1.1).
  So it is `alpha(t)` for `t = sum_j C_j(beta,...,beta) m_j in E[G]`.
- It is injective by Step 2. If `M_e(F_q[G])` is directly finite, it is surjective by Lemma B.0.
- The rest follows from (D) and the collision argument: every `L_b` is bijective, `taubar` is injective, and `tau`
  is surjective iff `taubar` is.
- Since `E = M_e(F_q)` embeds unitally in `M_d(F_p)`, `M_e(F_q[G])` embeds unitally in `M_d(F_p[G])`, so the new
  hypothesis is weaker. ∎

**Coordinates from a splitting word.** Let `f` split `Q` along `A`, and put `u(x) = f(x)^-1 x`.
- `u(ax) = f(x)^-1 a^-1 a x = u(x)`, so `u(x) = sigma(xbar)` for a set section `sigma: B -> Q`.
- `x = f(x) sigma(xbar)`. So `x -> (f(x), xbar)` is a bijection `Q -> A x B`, with inverse `(a,b) -> a sigma(b)`.
- `f(sigma(b)) = 0`, because `f(x) = f(f(x) sigma(b)) = f(x) + f(sigma(b))`.
- Let `Psi: Q^G -> A^G x B^G` be `x -> (f o x, xbar)`. It is a shift-equivariant homeomorphism.

**Theorem B.2 (converse), proof.**

*(ii) Strict linear layer.* Suppose `M_e(F_q[G])` is not directly finite. By Lemma B.0 there is a strict
`L = alpha(sum_(h in M) lambda_h h)`.
- Write each `lambda_h = sum_(c in Q) n_(h,c) rho(c)`, with `n_(h,c) in {0, ..., p-1}`.
- Let `tau` have memory `M ∪ {1}` and rule

      tau(x)(g) = [ prod_(h in M) prod_(c in Q) (c f(x(gh)) c^-1)^(n_(h,c)) ] . f(x(g))^-1 x(g).

  This is a word with constants.
- The bracket is `sum_h lambda_h f(x(gh)) = (L a)(g)`, with `a = f o x`, and the last factor is `sigma(b(g))`.
- So `Psi tau Psi^-1 = L x id`, which is injective and not surjective.

*(i) Strict quotient automaton.* Let `taubar` be a strict `B`-polynomial automaton with rule `wbar` and memory
`m_1, ..., m_k`. Lift the constants to get `w in Q * F_k`.
- Let `tau` have memory `{1, m_1, ..., m_k}` and rule
  `tau(x)(g) = f(x(g)) . w(u(x(g m_1)), ..., u(x(g m_k)))`.
- The second factor is `w(sigma(b(g m_1)), ...)`, which lies over `taubar(b)(g)`. Let `d_b(g)` be its value
  under `f`.
- So `Psi tau Psi^-1 (a, b) = (a + d_b, taubar(b))`.
- If `taubar` is injective, so is this map. Its image contains `(y, v)` iff `v in taubar(B^G)`. So `tau` is strict. ∎

**Theorem C, proof.** Induct on `r`; for `r = 0` there is nothing to prove.
- Put `Q' = Q/Q_1`. The chain `Q_i/Q_1` has `r - 1` layers, with the same quotients `Q'/(Q_i/Q_1) = Q/Q_i`, the
  same invariants, and the same splitting.
- By induction, `Q'`-polynomial surjunctivity over `G` is equivalent to direct finiteness of
  `M_(e_i)(F_(q_i)[G])` for `i >= 2`, together with `(Q/Q_r)`-polynomial surjunctivity.
- **`<=`.** Take `tau` injective. By B.1 its shadow over `Q'` is injective, hence surjective, and so `tau` is
  surjective.
- **`=>`.** If `M_(e_1)(F_(q_1)[G])` is not directly finite, B.2(ii) gives a strict `Q`-automaton. If some
  `Q'`-automaton is strict, B.2(i) gives one. ∎

**Corollaries, proofs.**
- **Squarefree `|Q|`.**
  - All Sylow subgroups are cyclic, so `Q` is metacyclic, hence solvable.
  - A chief factor `A` has order `p` dividing `|Q|`, with `p^2` not dividing `|Q|`. So `e = 1`, `D = F_p`, and
    `p` does not divide `|B|`, so (S1) applies.
  - Every prime divisor occurs as one chief factor.
- **`A_4`.**
  - `V_4`: `B = Z/3` acts by an element with irreducible minimal polynomial `x^2 + x + 1`, so `D = F_4` and `e = 1`.
    (S1) applies.
  - The quotient `Z/3` is squarefree.
- **`S_4`.**
  - `V_4`: `B = S_3 = GL_2(F_2)` acts by the natural, absolutely irreducible module, so `D = F_2` and `e = 2`.
  - (S2) applies with `c` a transposition: `n/o = 6/2 = 3` is odd, and `1 + rho(c) != 0` because the action is
    faithful.
  - The quotient `S_3` is squarefree. `M_2(F_2[G])` directly finite implies `F_2[G]` directly finite, via
    `diag(a,1) diag(b,1) = 1`.
- **`S_3 x Z/3`.**
  - Along `A_3 x 1`, use `v(x) = x^4 r x r x` with `r = ((12), 0)`. The exponent sum is `6`, so
    `v((y,z)) = (v_(S_3)(y), 0) = (t^a, 0)`, which splits by Step 8 of (P).
  - The quotient `Z/6` is squarefree. Equivalent to direct finiteness of `F_2[G]` and `F_3[G]`.
- **`SL(2,3)`.**
  - The center `Z/2` has `B = A_4` and `B^ab = Z/3`, so the obstruction does not apply. Neither (S1) nor (S2)
    applies.
  - Explicit splitting word: `f(x) = (x^3 c)^3`, with `c` of order 3.
    - `A_4` has exponent 6, so `x^3` lies over `V_4`, that is, `x^3 in Q_8`.
    - For `y in Q_8`, `(yc)^3 = y . rho(c)y . rho(c)^2 y`.
    - If `y = +-1`, this is `y`.
    - Otherwise `c` permutes the three cosets of `Z` in `Q_8 - Z` cyclically, and a product of one element from each
      of `{+-i}`, `{+-j}`, `{+-k}` is `+-1`.
    - So `f(Q) <= Z`. Since `-1` is central and the cube is odd, `f(-x) = -f(x)`.
    - Checked by machine for all eight elements of order 3.
  - The quotient `A_4` is as above. Equivalent to direct finiteness of `F_4[G]` and `F_3[G]`.

**Theorem D, proof.** Let `Z = Z/p` be central, and `B = Q/Z`.

*D.1 (fibres).* In Lemma 1.1 of (P), `rho = 1`. So `C_j(b)` is the number of occurrences of `x_j` minus the
number of occurrences of `x_j^-1`, that is, `e_j mod p`, independent of `b`.
- Every fibre is `L_b = alpha(epsilon mod p)`, and `tau ~ (a, b) -> (alpha(epsilon) a + d_b, taubar(b))`.
- If `taubar` and `alpha(epsilon)` are injective, then equal images force `b = b'`, then `a = a'`.
- Conversely, `tau` injective makes every `L_b` injective (Step 2 of (P)), and makes `taubar` injective by Step 5
  of (P), whose collision argument needs `L_(b')` bijective. So for "only if" use (P) under direct finiteness, or
  argue directly in D.2 below, where only "if" is used.

*D.2 (lifting).* Let `taubar` be strict with `alpha(epsilon mod p)` injective. Lift the constants of its rule to
get `tau`. Lifting constants does not change exponent sums.
- `tau` is injective by the "if" part of D.1.
- `tau` is not surjective, because its shadow `taubar` is not and `Q^G -> B^G` is onto.

*D.3 (tracked realizers).* Read the exponent sums off the two rules of Theorem B.2.
- (ii): variable `x_h` occurs through `f` exactly `n_h = sum_c n_(h,c)` times, and `x_1` also occurs in
  `f(x_1)^-1 x_1`. So `epsilon = sigma_f sum_h n_h h + (1 - sigma_f) 1`.
- (i): `f(x_1)` contributes `sigma_f`, and each `u(x_(m_j))`, of exponent sum `1 - sigma_f`, occurs with multiplicity
  `e_j(w)`.

*Nilpotent two-way.*
- **Forward.** Nilpotent groups are supersolvable, so (P) Step 7 needs only `F_p[G]` for `p | |Q|`.
- **Converse, setup.** Suppose `p | |Q|` and `st = 1 != ts` in `F_p[G]`. Then `alpha(t)` is injective and not
  surjective (Lemma B.0 with `e = 1`). Write `Q = P x P'`, where `P` is the Sylow `p`-subgroup.
- **The rule.** Choose `n_h >= 0` with `n_h = t_h mod p` and `n_h = [h = 1] mod |P'|`, over `h in M ∪ {1}`. Let
  `tau(x)(g) = prod_h x(gh)^(n_h)`, in a fixed order.
- **The chief series.** Every chief factor of a nilpotent group is central of prime order. Take a chief series
  through `P'`, so `Q/P' = P` sits on top and the top factor has order `p`.
- **Injective.** Induct up the series. At a factor of prime `l != p`, `epsilon = 1 mod l`. At a factor of prime
  `p`, `epsilon = t mod p`. Both are injective. The top shadow is `alpha(t)` on `(Z/p)^G`, which is injective. By
  D.1 ("if") at each layer, `tau` is injective.
- **Not surjective.** The top shadow `alpha(t)` is not surjective.

*Split layers under a nilpotent top.* Apply Theorem C with `Q/Q_r` nilpotent, and use the nilpotent two-way result
for `Q/Q_r`.
- **`D_12 = S_3 x Z/2`, `Z/3 x| Z/4`, `F_5 x| Z/4`.** The odd-order Sylow layer `A = Z/l` is normal, and `p = l`
  does not divide `|B|`, so it splits by (S1). `Q/A` is a 2-group.
- **`S_3 wr Z/2`.**
  - `A = F_3^2`, the base's Sylow 3-subgroup, and `B = D_8`, so (S1) applies.
  - `D_8` acts on `F_3^2` as the monomial group of order 8, which is absolutely irreducible, so `e = 2` and
    `D = F_3`.
  - `M_2(F_3[G])` directly finite implies `F_3[G]` directly finite.

*`GL(2,3)`.*
- **Structure.** `Z = {+-1}` is its only minimal normal subgroup: the normal subgroups are `1`, `Z`, `Q_8`,
  `SL(2,3)` and `GL(2,3)`. `GL(2,3)/Z = S_4` and `S_4^ab = Z/2`, so the obstruction applies, and (S1), (S2) and
  Theorem C do not.
- **Forward.** (P) Step 7 with the sharpened Step 3 gives layers `F_2` (`e = 1`), `F_2^2` over `F_2` (`e = 2`),
  `F_3` and `F_2`. The hypotheses are implied by direct finiteness of `M_2(F_2[G])` and `F_3[G]`.
- **Converse.** A strict `S_4`-automaton with `epsilon = 1 mod 2` suffices, by D.2. Theorem C for `S_4` produces
  one from any failure. The splitting words are `f_(V_4) = (xc)^6` (`sigma = 6`), `f_(A_3) = x^4` in `S_3`
  (`sigma = 4`), and the top layer `Z/2`.
  - If `M_2(F_2[G])` is not directly finite (this includes `F_2[G]` failing): realizer (ii) at `V_4` has
    `epsilon = 6 sum n_h h - 5 = 1 mod 2`.
  - If `F_3[G]` is not directly finite: realizer (ii) at `A_3` gives an `S_3`-automaton with
    `epsilon = 4 sum n_h h - 3 = 1 mod 2`. Lifting by (i) through `V_4` gives
    `epsilon = 6 - 5 epsilon(w) = epsilon(w) = 1 mod 2`.
  - So `GL(2,3)`-polynomial surjunctivity over `G` is equivalent to direct finiteness of `M_2(F_2[G])` and
    `F_3[G]`. ∎

**Computation** (`experiments/solvable-polynomial-automata-2026-09-17/split_layers.py`, output
`results-split.txt`).
- Method:
  - `Pol_1(Q)` is enumerated as the subgroup of `Q^Q` generated by the constants and `id`.
  - `K = Pol_1(Q) cap A^Q` is computed by Schreier generators over a transversal of `Pol_1(Q) -> Pol_1(Q)/K`,
    with `F_p`-row reduction.
  - Split is decided by solving `f(ax) - f(x) = a` in `span K`. Every solution is verified pointwise.
- Result: 21 groups (order `<= 120`) and 68 layer entries, of which 51 are split, all verified. On every entry,
  "split" agreed with "some element of `K` is nonconstant on `A`" (Theorem A). Every non-split entry is a central
  layer with `p | exp(B^ab)` (the obstruction).
