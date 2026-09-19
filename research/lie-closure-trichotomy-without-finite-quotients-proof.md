---
rg: 2
id: lie-closure-trichotomy-without-finite-quotients-proof
kind: route
title: Audit the V Lie-closure engine line by line, keep its group-free lemmas, and replace each use of V by (H1), (H2) or delta_1
target: lie-closure-trichotomy-without-finite-quotients
requires: [thompson-v-gap-witnesses-need-unbounded-lie-closure, thompson-v-mf-witnesses-are-dense-in-simple-adjoint-groups]
artifacts:
  - research/thompson-v-gap-witnesses-need-unbounded-lie-closure-proof.md
  - research/thompson-v-mf-witnesses-are-dense-in-simple-adjoint-groups-proof.md
---

Notation is as in the target. `sigma : Gamma0 -> U(n)` is a unitary representation,
`Gamma = sigma(Gamma0)`, `K` is its closure, `K^0` the identity component, `l = Lie(K)`, `z` the
centre of `l`, `m = [l, l]`, and `w_r = sigma(r)` for `r` in `R`. We write `D = D(sigma)`.

Two routes are cited below:

- **[LCR]** is `thompson-v-gap-witnesses-need-unbounded-lie-closure-proof`;
- **[DAR]** is `thompson-v-mf-witnesses-are-dense-in-simple-adjoint-groups-proof`.

## 0. What is imported and what is re-proved

**Group-free lemmas, imported verbatim.** The following statements of [LCR] and [DAR] mention no
group presentation. They are statements about unitaries, compact subgroups of `U(n)` and real Lie
subalgebras of `u(n)`, and their proofs there use nothing about `G0` or `V`. We use them as stated.

- From [LCR]:
  - standard facts (L1)-(L4);
  - (E1), (E2);
  - Lemma O (orthogonal moves give `||w - 1|| >= sqrt 2`);
  - Lemma P, Lemma F;
  - Lemma C (commutator descent in a set that is finite modulo scalars, for `eta < 1/2`);
  - Lemma A (adjoint contraction `||Ad(u)|_m - 1|| <= 2 ||u - 1||`, and complexification keeps norms);
  - Lemma Z (`l = z (+) [l, l]` orthogonally and canonically).
- From [DAR]:
  - (1.2)-(1.6), which give the orthogonal splitting of a centre-free `m` into canonical simple ideals,
    negative definite Killing forms, inner derivations and `Ad(exp Y) = exp(ad Y)`;
  - Lemma 3.1 (an orthogonal automorphism of a compact simple `h` within `sqrt 3` of `1` is
    `exp(ad Y)`);
  - Lemma 3.2 (`Ad(K^0)|_h = Inn(h)` for a simple ideal `h` of `m`, compact and connected).

  (1.1) of [DAR] is the one step there that uses the group, and it is re-proved in Section 5 below.

**Every group-dependent use, located.** The V routes use facts about `G0` or `V` in exactly the
following places. Each is replaced below.

| place | V input used | replacement |
|---|---|---|
| [LCR] "[R]", used in Step 3 Case A and Step 5; [DAR] "[R]" item 1, used in Steps 5 and 6 | nontrivial reps of dim `<= N` have `D >= delta_N > 0` | definition of `delta_N` plus (H1) |
| [LCR] transfer tool, finite target (S1), used in Step 1, Step 2 and Step 4; [DAR] transfer tool, used in Steps 2 and 4 | `V` has no nontrivial finite quotient | (H2), Lemma T below |
| [LCR] (S2) and the character computation, used in (1a) and at the end of Step 2 | nontrivial characters of `G0` have `D = 2` | the definition of `delta_1` |
| [LCR] Step 3 Case B, "Step 2 gives `D >= 1/2`" | Step 2 | Step 2 below, with `eta_0` |
| [DAR] (1.1), "`D < 1/2` so `K^0` nonabelian" | [LC] item 2 | item 2 below, with `D < eta_0` |
| [DAR] Step 7 | "V is MF iff `delta_N -> 0`" | not used: the corollary is stated for `gap(Gamma0, R)` |

The remaining steps use only the group-free lemmas and the numerical inequalities `D < 1/2`,
`2D < 1` and `2D < sqrt 3`. These all follow from `D < eta_0 <= 1/2`.

**Lemma T (transfer).** Let `f : Gamma0 -> F` be a homomorphism to a finite group with `f(r) = 1` for
all `r` in `R`. Then `f` is trivial. *Proof.* `f` factors through `Q`, and (H2) applies.

**Lemma D (defect of sums).** If `rho = rho_1 (+) rho_2` orthogonally, then
`D(rho) = max(D(rho_1), D(rho_2))`, because `rho(r) - 1` is block diagonal. Hence, if `rho` is
nontrivial of dimension `<= N`, then `D(rho) >= delta_N`. This is the definition of `delta_N`. By
(H1), the bound is positive.

## 1. Item 1 (imprimitive models)

Let `p : Gamma0 -> Sym(k)` be the permutation action on the summands. Suppose `D < sqrt 2`. If
`p(r) E_j = E_(j')` with `j' != j`, then Lemma O, applied to `w_r` with `E = E_j` and
`E' = E_(j')`, gives `||w_r - 1|| >= sqrt 2`, which is impossible. So `p(r) = 1` for all `r` in `R`,
and Lemma T makes `p` trivial. This contradicts the hypothesis, so `D >= sqrt 2`.

An induced representation `Ind_H^(Gamma0) tau` with `1 < [Gamma0 : H] < infinity` is the orthogonal
sum of the translates `gW`. They are permuted transitively, and there are at least 2 of them.

For the last sentence, argue as in [LCR] (1c), which is group-free given the main statement. Let `E_tau`
be the `K^0`-isotypic components. Then `Gamma` permutes them, since `K` normalizes `K^0`. By the main
statement it fixes each one, and irreducibility leaves exactly one. By Schur's lemma, `Z(K^0)` acts by
scalars.

## 2. Item 2 (abelian identity component)

The reductions of [LCR] Step 2 are group-free. Finite modulo scalars forces `K^0` into the scalars.
Virtually abelian forces `K^0` inside the closure of the finite-index abelian subgroup. So assume
`K^0` is abelian, `sigma` is nontrivial irreducible, and `D < eta_0`.

- By item 1, which applies since `D < 1/2 < sqrt 2`, `K^0 = Z(K^0)` acts by scalars. So the image of
  `Gamma` in `PU(n)` is a quotient of the finite group `K/K^0`, and `U(1) Gamma` has finite image in
  `PU(n)`.
- Let `S` be the set of all `gamma w_r^(+-1) gamma^(-1)`, with `gamma` in `Gamma` and `r` in `R`.
  Each element has `||s - 1|| <= D < 1/2` by (E2). Lemma C, applied with `P = Gamma` and `eta = D`,
  shows that `S` commutes pairwise. So `N = <S>` is an abelian normal subgroup of `Gamma`.
- Let `Z_Gamma = Gamma ∩ U(1)`. The group `Gamma / (N Z_Gamma)` is a quotient of the image of `Gamma` in
  `PU(n)`, so it is finite. The composite `Gamma0 -> Gamma / (N Z_Gamma)` kills `R`, since each `w_r`
  lies in `S`. By Lemma T it is trivial, so `Gamma = N Z_Gamma`, which is abelian.
- An abelian unitary group has a common eigenvector. By irreducibility, `n = 1`, so `sigma` is a
  nontrivial character of `Gamma0`. By the definition of `delta_1`, `D >= delta_1 >= eta_0`. This is a
  contradiction.

Hence `D >= eta_0`. (If `Gamma0` has no nontrivial character, the last step is already impossible.)

## 3. Item 3 (adjoint transfer)

Assume `D < eta_0`; otherwise there is nothing to prove. Define
`rho(g) = (Ad(sigma(g))|_m)_C` on `m_C`, of complex dimension `N_sigma`. By (L3) and Lemma Z it is a
unitary representation, and by Lemma A `D(rho) <= 2D`.

- *Case A: `rho` nontrivial.* Lemma D gives `2D >= D(rho) >= delta_(N_sigma)`.
- *Case B: `rho` trivial* (including `N_sigma = 0`). The argument of [LCR] Step 3 Case B is group-free
  up to its last sentence. It uses:
  - density of `Gamma` in `K`;
  - item 1, which here gives `Z(K^0)` scalar since `D < sqrt 2`;
  - Lemma Z and (L2).

  It shows that `K^0` is central in `K`, hence abelian. Item 2 then gives `D >= eta_0`, which is a
  contradiction.

So `D >= min(eta_0, delta_(N_sigma)/2)`, with `delta_0 = +infinity` making the bound `eta_0` when
`N_sigma = 0`.

## 4. Item 4 (fixed-group amplification)

The argument of [LCR] Step 5 is group-free except for the appeal to item 3. Let `H` be the closure of
`phi(Gamma0)`, so that `dim H <= dim M`. Decompose `pi o phi` into irreducibles `sigma_j`. Some
`sigma_j` is nontrivial. By (L4) its Lie algebra is the image of `Lie(H)`, so
`N_(sigma_j) <= dim H <= dim M`. Item 3 and monotonicity of `delta` give

```text
D(pi o phi) >= D(sigma_j) >= min(eta_0, delta_(N_(sigma_j))/2) >= min(eta_0, delta_(dim M)/2).
```

## 5. Item 5 (density in one simple adjoint group)

Let `sigma` be nontrivial irreducible with `D < eta_0`.

**(5.1) `m != 0` and `m` has trivial centre.** By item 2, `K^0` is nonabelian. By (L2), `K^0` is
generated by `exp(l)`, so `l` is nonabelian and `m != 0`. The triviality of the centre is the
group-free second half of [DAR] (1.1): an element of `m` central in `m` is central in `l`, so it lies
in `z ∩ m = 0` (Lemma Z).

**(5.2) Splitting.** By [DAR] (1.2)-(1.3), `m = h_1 (+) ... (+) h_r` orthogonally, and these are the
only simple ideals. Every automorphism of `m` permutes them.

**(5.3) Invariance.** `Ad(k)` preserves `m` (Lemma Z), so `k -> (permutation of the h_a)` is a
homomorphism `K -> Sym(r)`.
- By Lemma A, `||Ad(w_r)|_m - 1|| <= 2D < 1 < sqrt 2`.
- If `Ad(w_r)` moved `h_a` onto `h_b` with `b != a`, then Lemma O, applied to `(Ad(w_r)|_m)_C`, would
  give `>= sqrt 2`. So each `w_r` fixes every `h_a`.
- By Lemma T the composite `Gamma0 -> Sym(r)` is trivial. By continuity and density, all of `K` fixes
  every `h_a`.
So `tau_a = Ad(sigma(.))|_(h_a)` is an orthogonal homomorphism into `Aut(h_a)` with
`D(tau_a) <= 2D < 1`.

**(5.4) Relators are inner.** Since `2D < sqrt 3`, [DAR] Lemma 3.1 gives
`tau_a(r) = exp(ad Y_r)`, which lies in `Inn(h_a)`.

**(5.5) Density.** Put `L = Ad(K)|_(h_a)`, which is compact. By [DAR] Lemma 3.2,
`L_0 = Ad(K^0)|_(h_a) = Inn(h_a)`, and it is normal of finite index in `L`.
- The composite `Gamma0 -> L/L_0` is a homomorphism to a finite group. It kills `R` by (5.4). By
  Lemma T it is trivial, so `tau_a(Gamma0)` is contained in `L_0`.
- `tau_a(Gamma0)` is dense in `L`, and `L_0` is closed. So `L = L_0 = Inn(h_a)`, and `tau_a` has dense
  image in `Inn(h_a)`.

**(5.6) Nontriviality and dimension.** `Inn(h_a)` is nontrivial because `h_a` is nonabelian (Step 5 of
[DAR], group-free). So `tau_a` is nontrivial, and `(tau_a)_C` is a nontrivial unitary representation of
complex dimension `dim_R h_a` with defect `<= 2D` (Lemma A). Lemma D gives
`delta_(dim h_a) <= 2D`.

## 6. Item 6 (converse)

`(tau_j)_C` is a nontrivial unitary representation of dimension `dim h_j`, with `D((tau_j)_C) = D(tau_j)`
(Lemma A, last sentence). So `delta_(dim h_j) <= D(tau_j) -> 0`, and `gap(Gamma0, R) = 0`.

## 7. The corollary

This step uses the classification of compact simple Lie algebras, as quoted verbatim in [DAR] input
[CL]. The only fact used is that there are finitely many exceptional types. Let `N_exc` be the largest
real dimension of an exceptional compact simple Lie algebra.

**(=>)** Suppose `gap = c > 0`, and suppose `tau : Gamma0 -> Inn(X(k))` has dense image. Apply
item 6 in quantitative form to the single representation `tau_C`: `D(tau) = D(tau_C) >= delta_(dim X(k)) >= c`.
So each `Gap(X)` holds with `eps = c`.

**(<=)** Suppose `gap = 0`, and let `eps_X` be the three constants.
- By Lemma D there are nontrivial irreducibles `sigma_j` with `D(sigma_j) -> 0`.
- For large `j`, `D(sigma_j) < min(eta_0, delta_(N_exc)/2, min_X eps_X / 2)`. The last two quantities
  are positive by (H1).
- Item 5 gives a simple `h` with `delta_(dim h) <= 2 D(sigma_j) < delta_(N_exc)`. Hence
  `dim h > N_exc`, so `h` is classical: `h` is isomorphic to `X(k)`, by `psi` say.
- It also gives a dense `tau : Gamma0 -> Inn(h)` with `D(tau) <= 2 D(sigma_j)`.
- Transport along `psi`: `Ad(psi) o tau` lands densely in `Inn(X(k))`, because
  `psi exp(ad Y) psi^(-1) = exp(ad psi Y)`. The inner product transported along `psi` is
  `Inn(X(k))`-invariant, and the defect is unchanged.
- This gives `D < eps_X`, which contradicts `Gap(X)`.

## 8. Sanity of the substitutions

In each of the three instances in the target's table, `eta_0 = 1/2`, which is the threshold of the V
routes.
- For `G0 = S4 *_Z2 S3`, the audit reproduces [LCR] and [DAR] line by line.
- For `Z/4 * Z/3` and `Delta(4,3,5)`, the only differences are the words in `R`. The group-free lemmas
  never read them.
