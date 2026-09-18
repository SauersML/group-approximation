---
rg: 2
id: random-labeling-hnn-soficity-criterion-proof
kind: route
title: Label the stable letter by independent random permutations on partition pieces and count fixed points by lazy revelation
target: random-labeling-hnn-soficity-criterion
requires: []
---

Written proof, 2026-09-17. Not Lean-checked.

## 0. Setup and conventions

Let `S` be a finite generating set of `H`. Let `α_1, ..., α_p` be words in `S`
representing generators of `A`, and `β_i` words representing `φ(α_i)`. Put
`G = <H, t | t α_i t^(-1) = β_i>`, which is the HNN extension. Let `W_R` be the
set of words of length `<= R` in `S^(±1) ∪ {t^(±1)}`, and `q` the evaluation
map to `G`. Words act on the left: the rightmost letter is applied first.

A permutation model on a finite set `Z` assigns permutations to `S` and `t`.
This extends to a homomorphism from the free group, written `u ↦ u_Z`.

**Soficity criterion.** A finitely generated `G` is sofic iff for every
`R, δ` there is a model `Z` such that:
* (a) `|Fix(u_Z)| >= (1-δ)|Z|` for every `u in W_R` with `q(u) = 1`;
* (b) `|Fix(u_Z)| <= δ|Z|` for every `u in W_R` with `q(u) != 1`.

This is the standard equivalent form of Elek--Szabó's definition for finitely
generated groups.

Two facts about models are used repeatedly.

* **(F1) Change of word.** If `u, v in W_R` and `q(u) = q(v)`, then `u^(-1) v`
  lies in `W_(2R)` and is trivial in `G`. So in a `(2R, ε)`-model, `u_Z` and
  `v_Z` agree on at least `(1-ε)|Z|` points.
* **(F2) Moving bad sets.** For any word `v`, the map `y ↦ v_Z(y)` is a
  bijection of `Z`. So a bad set of size `<= ε|Z|` has a preimage of the same
  size.

## 1. The construction

Fix `R`. Let `R' = R'(R)` bound the lengths of the Britton-reduced
representatives chosen below, and of the words `u^(-1) u*` compared with them.
Take:
* an `(R_1, ε)`-model `X` as in (I);
* an `(R_1, ε)`-model `Y` with partition `P` as in (II);
* `R_1 >= 2R'`.

Write `σ_X, σ_Y` for the permutations of `s in S`, and `τ_X, τ_Y` for those of
`t`. For each piece `P` of `P`, choose an independent uniformly random
permutation `π_P` of `[M]`. On `Z = X × Y × [M]` put

    s(x, y, j) = (σ_X(s) x, σ_Y(s) y, j),
    t(x, y, j) = (τ_X x, τ_Y y, π_(P(y)) j),

so that

    t^(-1)(x, y, j) = (τ_X^(-1) x, τ_Y^(-1) y, π_(P(τ_Y^(-1) y))^(-1) j).

Projecting to `X × Y` forgets `[M]`, and there the model is the product model.

## 2. Relations (property (a))

Let `u in W_R` with `q(u) = 1`. In the free group on `S ∪ {t}`, `u` is a
product of at most `N(R)` conjugates of relator words. These are relators of
`H` of length `<= L(R)` and the words `ρ_i = t α_i t^(-1) β_i^(-1)`. `N` and
`L` are finite because `W_R` is finite.

A product of permutations each moving at most `η|Z|` points moves at most
`N η |Z|` points, and conjugation preserves the number of moved points. So it
suffices that each such relator fixes all but `O(ε)|Z|` points.

* **Relators of `H`.** They act trivially on `[M]`, and by (a) of the two models
  they fix all but `2ε|X||Y|M` points.
* **The words `ρ_i`.** On `X × Y` they fix all but `2ε` of the points, by (a).
  On the last coordinate, start at `(x, y, j)` and apply `β_i^(-1)` (no change
  to `j`). Then apply `t^(-1)`, giving the letter `π_(P(z))^(-1)` with
  `z = τ_Y^(-1) β_i^(-1) y`. Then apply `α_i`, taking `z` to `α_i z`, and
  finally `t`, giving the letter `π_(P(α_i z))`. The `j`-coordinate is therefore

      π_(P(α_i z)) π_(P(z))^(-1) j,

  which equals `j` whenever `α_i z` is in the piece of `z`. By (II) this fails
  for at most `ε|Y|` values of `z`, hence of `y`, by (F2).

So (a) holds with `δ = O_R(ε)`, deterministically in `π`.

## 3. Freeness (property (b))

Let `u in W_R` with `q(u) != 1`. Choose a Britton-reduced word

    u* = h_0 t^(e_1) h_1 ... t^(e_n) h_n,

with `h_i` words in `S`, `e_i = ±1`, `q(u*) = q(u)`, of length `<= R'`. Reduced
means that no subword `t h t^(-1)` has `q(h) in A`, and no subword `t^(-1) h t`
has `q(h) in B`. By (F1) and §2, `u_Z` and `u*_Z` agree off `O_R(ε)|Z|` points.

**Case `n = 0`.** Then `u* = h_0` is nontrivial in `H`. By (I), `h_0` fixes at
most `ε|X|` points of `X`, so at most `ε|Z|` points of `Z`.

**Case `n >= 1`.** Fix `y`. Following `u*` from the right, each letter
`t^(±1)` contributes a letter `π_P^(±1)`, where `P` is determined by `y` alone.
So the `[M]`-coordinate of `u*_Z(x, y, j)` is `w_y(π) j`, a word in the letters
`π_P`. Consider adjacent stable letters.

* **`t h t^(-1)` with `q(h)` not in `A`.** Let `v` be the point just before
  this `t^(-1)` is applied, and `z = τ_Y^(-1) v`. The contributed letters are
  `π_(P(z))^(-1)` and then `π_(P(h z))`. They cancel only if `h z` is in the
  piece of `z`.
* **`t^(-1) h t` with `q(h)` not in `B`.** Let `v` be the point just before
  this `t` is applied. The letters are `π_(P(v))` and then
  `π_(P(τ_Y^(-1) h τ_Y v))^(-1)`. They cancel only if `h (τ_Y v)` is in the
  same `τ_Y(P)`-piece as `τ_Y v`.

Adjacent stable letters with the same sign contribute letters of the same sign,
which never cancel. Each `v`, and hence each `z` or `τ_Y v`, is the image of
`y` under a fixed word. By (II) and (F2), the set of `y` at which some
cancellation occurs has size at most `2nε|Y| <= 2R'ε|Y|`. Call its complement
the good set.

For good `y`, the word `w_y` is a reduced nonempty word of length `n` over the
alphabet `{π_P}`, since no adjacent pair cancels.

**Lemma (lazy revelation).** Let `w` be a reduced word of length `n >= 1` in
letters `π_1, π_2, ...`, which are independent uniform permutations of `[M]`.
Then for every `j`,

    Pr[w(π) j = j] <= n(n+1)/(M-n).

*Proof.* Follow the trajectory `j_0 = j, j_1, ..., j_n` step by step, revealing
values of `π_ℓ^(±1)` only when needed. Suppose that before step `k` no
coincidence has occurred. Here a coincidence is a newly revealed value landing
on an already visited point. Then the revealed edges form a simple path, and
`j_(k-1)` is its newest endpoint, whose only revealed edge is the one used to
arrive.

That edge can be used at step `k` only if the letter at step `k` inverts the
letter at step `k-1`, which reducedness forbids. So the value at step `k` is
uniform over at least `M-n` unrevealed values, of which at most `n+1` are
visited points. The chance of a coincidence at step `k` is therefore at most
`(n+1)/(M-n)`.

If no coincidence ever occurs, then `j_n` is a new point, so `j_n != j_0`. A
union bound over the `n` steps finishes the proof. ∎

So for good `y`, the expected number of `j` fixed by `w_y(π)` is at most
`M R'(R'+1)/(M-R')`. Summing over `x`, over good `y`, and over the bad set,

    E |Fix(u*_Z)| <= |Z| ( 2R'ε + R'(R'+1)/(M-R') ).

**Choosing parameters.** Given `R` and `δ`, pick `ε` and then `M` so that the
right-hand side is at most `δ|Z| / (2|W_R|)`, and so that the deterministic
errors from §2 and (F1) are at most `δ/2`. By Markov's inequality and a union
bound over `W_R`, some choice of the `π_P` satisfies (b) for all `u in W_R`. It
satisfies (a) regardless. Hence `G` is sofic.

**Converse for (I).** A sofic approximation of `G` is a model satisfying (I).

## 4. Amplification

Suppose models `(Y_k, P_k)`, `k = 1..K`, are `(R, ε_k)`-models. Suppose also
that each generator of `A` keeps all but `ε_k` of the points in their piece.
The product model `Y = ∏ Y_k` has product permutations and the product
partition, whose pieces are the products of pieces. It is an
`(R, Σε_k)`-model, and `A`-generators keep all but `Σε_k` of the points in their
piece. Its stable letter is `∏ τ_k`, so `τ(P)` is the product of the `τ_k(P_k)`.

A point `(y_k)` is non-separated by `u` exactly when every coordinate is
non-separated. So the non-separated fraction is the product of the coordinate
fractions, and the same holds for the `B`-side.

Now let `S_A` and `S_B` be the finite sets of elements of `H \ A` and `H \ B`
represented by words of length `<= R`. For each `h`, suppose some model
separates `h` on a fraction `>= δ_h` of points, for all `(R, ε)`. Take `k_h`
copies with `(1-δ_h)^(k_h) < ε`, and multiply over `h in S_A ∪ S_B`. This
gives (II) with error `O(ε)` once the individual `ε`'s are small.

## 5. Amenable separation

Let `ψ : G ->> Γ` with `Γ` amenable. Given a finite set `h_1..h_r` in `H \ A`
with `ψ(h_i)` not in `ψ(A)`, and similarly for `B`, we build a model. Let
`F ⊂ Γ` be finite with `|∂_R F| <= ε|F|`, where `∂_R F` is the set of
`γ in F` whose `R`-ball, in the image generators, leaves `F`.

For each generator `s`, let `σ(s)` be any permutation of `F` extending the
partial map `γ ↦ ψ(s)γ` on `F ∩ ψ(s)^(-1) F`; do the same for `t`. For
`γ in F \ ∂_R F` and `u in W_R`, `u_F(γ) = ψ(u)γ`. Hence the model is an
`(R, ε)`-model.

The pieces are `F ∩ ψ(A)γ`, the traces of right cosets. For interior `γ`:
* each `α_i` sends `γ` to `ψ(α_i)γ`, which is in `ψ(A)γ`;
* `ψ(h)γ` is in `ψ(A)γ` iff `ψ(h)` is in `ψ(A)`, by right cancellation.

So `h` is separated at every interior point. On the `B`-side, `τ(F ∩ ψ(A)γ)`
agrees off the boundary with `ψ(t)ψ(A)γ = ψ(B)ψ(t)γ`. So `τ(P)` consists of
traces of right `ψ(B)`-cosets, and `h` not in `B`, with `ψ(h)` not in `ψ(B)`,
is separated at interior points.

Taking products over the finitely many `ψ` needed (§4) gives (II).

**Sofic injective quotients give (I).** If `ρ : G -> Λ` is injective on the
finite set of elements of `H` of length `<= R`, and `Λ` is sofic, then pulling
back a sofic approximation of `Λ` gives a model satisfying (I) at scale `R`.

## 6. Calibration

**`BS(1,2) = <a, t | t a t^(-1) = a^2>`, with `H = A = Z`, `B = 2Z`.**
* The models `Z/N`, `N` odd, with `a: x ↦ x+1` and `t: x ↦ 2x`, satisfy the
  relation exactly and are free on `H`-words of length `< N`.
* `A = H` acts transitively, so the only `A`-invariant partition is the trivial
  one. With it, (II) fails for `h = a`: `a` is not in `B`, yet `a(z)` always
  stays in the (unique) `τ(P)`-piece of `z`. The construction then gives `t`
  one constant label `π`, and the reduced word `t^(-1) a t` becomes
  `π^(-1) π = id` on `[M]`. So the `[M]`-coordinate carries no freeness, and
  the §3 argument does not apply. Freeness of `X × Y × [M]` would have to come
  from `X × Y` alone. Here it does, because `BS(1,2)` is residually finite and
  the affine models are finite quotients, but the theorem is not what proves it.
  This is the expected behaviour: (II) is exactly what lets `[M]` carry
  freeness of words with `t`, so `X` only needs to be free on `H`-words.
* The amenable quotient `ψ = id` of `BS(1,2)` separates `a` from `ψ(B)`. So §5
  supplies (II), and the theorem reproduces soficity of `BS(1,2)`.

**Automorphism case `A = B = H`.** There is nothing to separate, the trivial
partition works, and every reduced word with `n >= 1` is `t^(n)` up to base
letters. So `H rtimes Z` is sofic from (I), the known sofic-by-amenable case.

**Amenable `A`.** Ornstein--Weiss tiles of the free `A`-action in a model of
(I) give pieces. A generator of `A` crosses a tile boundary only at an
`ε`-fraction of points. If `h` not in `A` maps a point `f y_0` into its own
tile `F y_0`, then `f'^(-1) h f`, which is nontrivial, fixes `y_0`, and (I)
makes that rare, since there are only `|F|^2` pairs `(f, f')`. The `B`-side is
the same with `τ(F y_0) ≈ φ(F) τ y_0`. Remark only, not used above: over
amenable associated subgroups, (I) alone implies (II), so the theorem reduces
soficity to (I). It does not by itself reprove Elek--Szabó permanence, which
supplies (I) from soficity of `H`.
