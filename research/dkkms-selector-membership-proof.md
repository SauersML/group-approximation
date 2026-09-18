---
rg: 2
id: dkkms-selector-membership-proof
kind: route
title: Unfold the honest class label on clean k-tuples, read the Grassmann edge law as a uniform direction off L'+H_U, and run the selector decoder with the dirty mass subtracted from the advantage and Lemma 5.4 as outer soundness
target: dkkms-2to1-instances-satisfy-selector-decoding-hypotheses
requires: [efficient-branch-selectors-list-decode-honest-outer-labels]
artifacts:
  - experiments/dkkms-selector-membership-2026-09-17/check_dkkms_direction_law.py
---

The notation is that of the target claim. All quotations are from Dinur, Khot,
Kindler, Minzer and Safra, ECCC TR16-198 (the copy used has Section 4.2 "The
Full Reduction", Section 5 and the references). Credit for the construction and
for Lemma 5.4 is theirs; Lemma 5.4 is credited there to Khot, Minzer and Safra
([18] of that paper).

## Quoted inputs

* **(Q1) Theorem 4.1.** "There is an absolute constant s∗ < 1 such that for
  every constant ε > 0, Gap3Lin(1−ε, s∗) is NP-hard on regular instances."
* **(Q2) Legitimacy.** "the fraction of U that are not legitimate is
  negligible, i.e. O(k²/|X|)".
* **(Q3) Lemma 4.1.** "For (U,L) there is an l-dimensional subspace
  R ⊆ {0,1}^n such that C(U,L) = {(U′,L′) ∈ A | L′ + H_{U′} = R + H_{U′}}."
  The paper also uses R ∩ H = {0}: "g exists since R∩H={0}".
* **(Q4) Definition 4.2.** "For every (U,L) ∈ C we unfold σ = Ã(C) by
  defining, A(U,L) = σ̃_U|_L, where σ̃_U is the (H_U,h_U) extension of σ". The
  extension is "f̃(z) = f(x) + h(y) and where z = x + y is the unique way to
  write z as a sum of x∈L and y∈H".
* **(Q5) Edges, constraints, folded weights.** These are as quoted in the claim.
  The folded edges come from "choose a random edge ((U,L),(V,L′)) ∈ E and then
  output (C(U,L),(V,L′))", and "The weights are summed up as well".
* **(Q6) Outer game and Lemma 5.4.**
  - "The verifier chooses U,V as in the edge distribution of G_unfolded."
  - "The verifier chooses Q ∈ Gr(X_V,q) and sends (U,Q) to the first player,
    and (V,Q) to the second player."
  - "The verifier accepts iff a|_V = b and a satisfies all of the linear
    equations on U."
  - "Lemma 5.4 (Soundness of Outer PCP, [18]). If every assignment for
    (X, Eq) satisfies at most s∗ fraction of the equations, then the players
    have no strategy that succeeds with probability better than
    ε = exp(−k/exp(qℓ))."

## Step 1: exact 2-to-1 and (B+)

Fix `(U,L) in C` with representative `R`. By (Q3), `L + H_U = R + H_U`, and
`R ∩ H_U = L ∩ H_U = {0}`. Every `z in L` has a unique decomposition
`z = r(z) + y(z)` with `r(z) in R` and `y(z) in H_U`. The map `z -> r(z)` is
linear. It is injective, since `r(z) = 0` forces `z in L ∩ H_U = {0}`. So it is
a bijection `L -> R`.

By (Q4), `A_σ(U,L)(z) = σ(r(z)) + h_U(y(z))`. If `A_(σ1)(U,L) = A_(σ2)(U,L)`,
then `σ1(r(z)) = σ2(r(z))` for all `z`, so `σ1 = σ2`. Unfolding is therefore
injective, hence bijective, between sets of size `2^l`.

Restriction `Fun(L) -> Fun(L′)` is 2-to-1. The two extensions of `σ′` differ by
a nonzero functional with kernel `L′`, so they differ at every
`x in L \ L′`. Pulling back along the bijection gives Item 1.

## Step 2: selectors on the folded game embed

Take an aggregated constraint `E` of `G_folded` between `C` and `(V,L′)`. By
(Q5), `E` accepts `(σ,σ′)` iff every multi-edge `e` of `E` accepts it, and its
weight is the sum of theirs. Let `o` be a partial bijection inside `E`, defined
on a set `D` of labels `σ′`.

For each multi-edge `e` of `E`, and each of its direction copies, define
`o′_e(σ′) := o(σ′)` if `σ′ in D`. This is a preimage of `σ′` in `e`, because
`E` accepts `(o(σ′),σ′)`. Otherwise let `o′_e(σ′)` be either preimage of `σ′`
in `e`.

Let `h` be a labelling. If `h` satisfies the oriented `E`, then
`h_(V,L′) in D` and `h_C = o(h_(V,L′)) = o′_e(h_(V,L′))`, so `h` satisfies
every oriented copy. Summing the weights gives
`val_(G_multi,o′)(h) >= val_(G_folded,o)(h)`. Computing `o′` from `o` is
polynomial.

## Step 3: the direction law (E)

The process outputs `(U,V,L′,L)` with probability
`P(U) P(V|U) |Gr(X_V,l-1)|^(-1) N^(-1)`, where `N` is the number of `l`-spaces
of `X_U` containing `L′`. Every `L′` lies in the same number of such spaces,
namely `N = (2^(3k) - 2^(l-1))/2^(l-1)`. So the two readings of "a random
L′ ... and a random L ... such that L′ ⊆ L" coincide: a uniform pair, or a
uniform `L′` followed by a uniform `L ⊇ L′`.

Restricting to `(U,L) in A` multiplies by the indicator of `L ∩ H_U = {0}` and
renormalizes. So, given `(U,V,L′)`, the space `L` is uniform on
`S := {L ⊇ L′ : dim L = l, L ∩ H_U = {0}}`, and the copy's direction `x` is
uniform on `L \ L′`. Conditioning on `(w_e, a_e) = ((V,L′),U)` is conditioning
on `(U,V,L′)`.

If `L′ ∩ H_U ≠ {0}`, then `S` is empty. Otherwise consider the map
`(L,x) -> x` on `{(L,x) : L in S, x in L \ L′}`. We show it is a bijection
onto `T := X_U \ (L′ + H_U)`.

* **Image in `T`.** If `x = y + h` with `y in L′` and `h in H_U`, then
  `h = x - y` is a nonzero element of `L ∩ H_U`, which is impossible.
* **Injective.** `L = L′ + span(x)`.
* **Onto.** Take `x in T` and put `L := L′ + span(x)`, which has dimension `l`.
  Suppose `y + εx` is a nonzero element of `H_U`, with `y in L′` and
  `ε in {0,1}`. If `ε = 0`, then `y in L′ ∩ H_U = {0}`, a contradiction. If
  `ε = 1`, then `x in L′ + H_U`, a contradiction.

Every `L in S` has exactly `2^(l-1)` elements outside `L′`, so the law of `x`
is uniform on `T`. The vectors `x_(e_i)` have disjoint supports, so
`dim H_U = k`. Since `L′ ∩ H_U = {0}`, `|L′ + H_U| = 2^(l-1+k)`.

For `T ⊆ Ω`, uniform on `T` is at total variation distance `|Ω \ T|/|Ω|` from
uniform on `Ω`. That is `2^(l-1+k)/2^(3k) = 2^(l-1-2k)`. This proves Item 3.

## Step 4: the target marginal (M)

By Step 3, the probability that the output is valid given `U` is

```text
sum_V P(V|U) * Pr_(L′)[L′ ∩ H_U = {0} | V] * |S|/N,
```

where `|S| = (2^(3k) - 2^(l-1+k))/2^(l-1)` whenever `L′ ∩ H_U = {0}`.

A vector `sum_i c_i x_(e_i)` is supported on `V` iff `c_i = 0` for every
equation replaced by a single variable. So `X_V ∩ H_U` is a `t`-dimensional
subspace of the `(2t + k)`-dimensional space `X_V`, where `t` is the number of
kept equations. `L′ ∩ H_U = L′ ∩ (X_V ∩ H_U)`. `GL(X_V)` acts transitively on
`t`-subspaces and preserves the uniform law on `Gr(X_V,l-1)`. Hence the inner
probability depends only on `(t, k, l)`.

By (Q5), the law of `t` given `U` is `Binomial(k, 1-β)`, whatever `U` is. So
the validity probability is the same for all `U`. The `U`-marginal of `G_multi`
is therefore `P(U)`, uniform on legitimate tuples, which is `ρ_A`. So `K = 1`.

## Step 5: branch identity on clean tuples

Let `U` be clean for `a`: `b_e = <a, x_e>` for all `e in U`, so
`h_U = a|_(H_U)`. With `σ = a|_R`, (Q4) gives
`σ̃_U(r + y) = <a,r> + <a,y> = <a, r+y>`. By (Q3), `L ⊆ R + H_U`, so
`A_(a|_R)(U,L) = a|_L`.

Suppose `hon(a)` satisfies an oriented copy `e`. Then
`hon(a)_C = o_e(hon(a)_(V,L′))`. So
`g_e(hon(a)_(w_e)) = A_(a|_R)(U,L)(x_e) = <a, x_e> = <λ^a_U, x_e>`, because
`x_e in X_U`.

Therefore the prediction is correct on every copy that is satisfied and has a
clean `U`. It follows that
`Pr_e[correct] >= val_(G_g)(hon(a)) - Pr_e[U dirty]`. By Step 4,
`Pr_e[U dirty] = Pr_(U uniform)[U dirty] = ε_out(a)`.

The remaining parts of Item 5:

* **Outer value.** `π_UV(a|_U) = a|_V = λ^a_V` iff `U` is clean, so
  `val_Φ(λ^a) = 1 - ε_out(a)`.
* **Inner value.** On clean `U`, `A(U,L)|_(L′) = a|_(L′) = hon(a)_(V,L′)`.
  Hence `val_(G_multi)(hon(a)) >= 1 - ε_out(a)`.
* **Dirty mass.** For a uniform ordered k-tuple of independent uniform
  equations, a union bound gives `Pr[dirty] <= kε_3`. Conditioning on
  legitimacy divides by `1 - O(k^2/|X|)`, by (Q2).

## Step 6: running the decoder

The data `(Φ_k, G_multi, annotation)` form an LEC in the sense of the parent
claim, for fixed `k` and `l`:

* the outer game has at most `|Eq|^k` vertices on each side;
* `2^m = 2^(3k)` is a constant;
* `G_multi` has polynomially many constraints, with rational weights computable
  from the process;
* `|Σ_w| = |Fun(L′)| = 2^(l-1) <= 2^l`.

Read the proof `efficient-branch-selectors-list-decode-honest-outer-labels-proof`
for where each hypothesis is used.

* **Step 0** builds the decoder from `G`, `g`, `μ` and the annotation alone. It
  never evaluates `hon`. Its soundness uses only `val(Φ) <= s < c0/2`.
* **Step 1** uses the witness `(λ, hon(λ))` and (B) only to obtain
  `Pr_e[g_e(h_(w_e)) = <λ_(a_e), x_e>] >= 1/2 + γ`. From that inequality alone
  it derives `P >= γ`.
* **Step 2** uses `|Σ_w| <= 2^l` and (E) with `τ <= γ/4`.
* **Step 3** uses (M).
* **Step 4** uses `val_Φ(λ) >= 1 - ε`.

Take the witness `λ := λ^a`, `h := hon(a)` with `ε_out(a) <= ε*`. By Step 5,
Step 1's inequality holds with `γ - ε*` in place of `γ`. Also
`val_Φ(λ^a) >= 1 - ε*`. Steps 3 and 4 above supply (E) and (M). So Steps 1-4
of that proof go through verbatim with `(γ, ε) := (γ - ε*, ε*)`, and give
acceptance probability `>= θ c0/2` on YES inputs, where

```text
c0 = ((γ - ε*)^3 2^(-l-2))^2 - 2ε*,
```

provided `τ <= (γ - ε*)/4`. This is Item 6.

## Step 7: the corollary

**The promise problem.** `Lang` is regular `Gap3Lin(1-ε_3, s*)`. It is NP-hard
by (Q1), under reductions that map YES to YES and NO to NO. The map
`x -> (Φ_k, G_multi, annotation)` is polynomial.

**YES instances.** Some `a` violates at most `ε_3` of `Eq`. By Step 5,
`ε_out(a) <= 2kε_3 =: ε*` once `|X|` is large. Finitely many small inputs are
decided by table lookup.

**NO instances.** Let `λ` be any labelling of `Φ_k`. Consider the players of
(Q6) who ignore `Q` and answer `λ_U`, resp. `λ_V`. Their questions `(U,V)` have
the law `ρ`, and they are accepted exactly when `π_UV(λ_U) = λ_V`. So
`val_Φ(λ)` is their success probability, and Lemma 5.4 gives
`val(Φ_k) <= ε_k =: s`.

**Parameters.** Put `p = (γ/2)^3 2^(-l-2)`, and suppose
`2^(l-1-2k) <= γ/8`, `ε_k < p^2/8` and `ε* <= min(γ/2, p^2/8)`. Then:

* `γ - ε* >= γ/2`, so `τ <= γ/8 <= (γ - ε*)/4`;
* `(γ - ε*)^3 2^(-l-2) >= p`, so `c0 >= p^2 - p^2/4 = 3p^2/4`;
* `s < p^2/8 < 3p^2/8 <= c0/2`.

**Conclusion.** Suppose a selector on `G_multi` had the stated property with an
inverse-polynomial confidence `θ`. By Step 6, it would give a one-sided
algorithm accepting YES inputs with probability `>= θ c0/2` and never accepting
NO inputs. Repeating it `O(1/(θ c0))` times puts `Lang`, and hence NP, in RP.

**The folded game.** A selector on `G_folded` becomes one on `G_multi` with at
least the same lift values, by Step 2. So the same conclusion holds for it.

**Near-honest labellings.** Let `h` agree with `hon(a)` at both endpoints
outside constraint mass `ζ <= γ/4`. Every oriented constraint outside that mass
that `h` satisfies is also satisfied by `hon(a)`. So
`val(hon(a)) >= val(h) - γ/4 >= 1/2 + 3γ/4`, and the argument above applies
with `3γ/4`. `square`

## Why the parent claim's direction bound was off

The parent scope paragraph took the direction uniform off an `(l-1)`-space.
Folding forces `L ∩ H_U = {0}`, which removes the whole coset structure
`L′ + H_U` of dimension `l-1+k`. That gives `2^(l-1-2k)`. Part A3 of the
artifact computes the total variation distance exactly and finds this value in
every case.
