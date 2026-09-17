---
rg: 2
id: virtually-endomorphic-self-similar-actions-finite-image-proof
kind: route
title: A fully invariant finite-index subgroup is carried into itself by every section and so acts trivially
target: virtually-endomorphic-self-similar-actions-have-finite-image
requires: []
---

Direct proof (2026-09-17, lane sw-010). Notation as in the target.

## Lemma 1: `R_n` has finite index and is fully invariant

Let `H` be a finitely generated group and `n >= 1`. Let `R_n(H)` be the intersection
of all normal subgroups of `H` of index at most `n`.

- **Finite index.** A normal subgroup of index `m <= n` is the kernel of a
  homomorphism `H -> S_m` (the regular action on `H/U`). There are finitely many
  such homomorphisms, since each is fixed by the images of a finite generating set.
  So there are finitely many such normal subgroups. A finite intersection of
  finite-index subgroups has finite index.
- **Full invariance.** Let `Φ in End(H)` and let `U <| H` have index `m <= n`.
  Then `Φ^(-1)(U)` is normal in `H`, and `H/Φ^(-1)(U)` embeds in `H/U`, so its
  index is at most `n`. Hence `R_n(H) <= Φ^(-1)(U)`, that is,
  `Φ(R_n(H)) <= U`. Intersecting over `U` gives `Φ(R_n(H)) <= R_n(H)`.
- **Normality upstairs.** Full invariance covers automorphisms, so `R_n(H)` is
  characteristic in `H`. If `H <| G`, then conjugation by `g in G` restricts to an
  automorphism of `H`, so `R_n(H) <| G`.
- **Containment.** If `U <= H` is normal in `H` of index at most `n`, then
  `R_n(H) <= U`.

## Lemma 2: invariant sets of section-closed elements act trivially

Let `N ⊆ Aut(X*)` be a set such that every `m in N` fixes every letter `x in X`
and has `m|_x in N`. Then every element of `N` acts trivially on `X*`.

*Proof.* By induction on `k`, every `m in N` fixes all words of length `k`.

- For `k = 0` this is trivial.
- For `k >= 1`, write the word as `xw` with `|w| = k - 1`. Then
  `m(xw) = m(x) m|_x(w) = x m|_x(w)`. Since `m|_x in N`, the induction hypothesis
  gives `m|_x(w) = w`. So `m(xw) = xw`.

## Proof of Theorem A

- **Choose `n`.** Let `U = core_G(Q_0) ∩ Stab_G(X) ∩ G'`, where `Stab_G(X)` is the
  kernel of the action on the first level.
  - Each of the three is normal of finite index in `G`: `Q_0` has finite index,
    `X` is finite, and `G'` is given. So `U <| G` has finite index.
  - Put `n = [G : U]`. Since `U <= G'` and `U` is normal in `G'` with
    `[G' : U] <= n`, Lemma 1 gives `N := R_n(G') <= U`.
- **`G'` is finitely generated.** It has finite index in the finitely generated
  group `G` (Reidemeister--Schreier). So `N` has finite index in `G'` by Lemma 1.
- **Sections stay in `N`.** Let `m in N` and `x in X`.
  - `m in U`, so `m` fixes every letter, and `m in Q_0 ∩ G' ∩ Stab_G(x)`.
  - By hypothesis `m|_x = Φ_x(m)`.
  - By Lemma 1, `Φ_x(N) <= N`, so `m|_x in N`.
- **Conclude.** By Lemma 2, `N` acts trivially on `X*`. Since `G <= Aut(X*)`, this
  means `N = 1`. So `G'` is finite, since `N` has finite index in it, and therefore
  `G` is finite. ∎

## Proof of Corollary B

Let `t_1, ..., t_d` be the transversal and write `ρ: G -> Aut(X*)` for the associated
action, with `X = {t_1, ..., t_d}`.

- **Section formula.** For `g in core_G(Q)`, `g t_i Q = t_i Q` for all `i`, so `g`
  fixes each letter, and its section at `t_i` is `φ(t_i^(-1) g t_i)`.
- **Choose `n`.** Let `U = core_G(Q_0) ∩ core_G(Q) ∩ G'`. Then `U <| G` has finite
  index. Put `n = [G:U]` and `N = R_n(G')`.
  - `N <= U` by Lemma 1.
  - `N` has finite index in `G'`, hence in `G`.
  - `N <| G` by Lemma 1, since `G' <| G`.
- **Sections stay in `N`.** Let `m in N`. Then `m` fixes every letter. For each `i`,
  `t_i^(-1) m t_i in N <= U <= Q_0 ∩ G'`, so
  `m|_(t_i) = φ(t_i^(-1) m t_i) = Φ(t_i^(-1) m t_i)`, which lies in `Φ(N) <= N`.
  - Here `m|_(t_i)` denotes the element of `G` whose image under `ρ` is the section
    of `ρ(m)`. The associated action satisfies `ρ(g)|_(t_i) = ρ(φ(t_i^(-1) g t_i))`
    for `g in core_G(Q)`.
- **Conclude.** Apply Lemma 2 to `ρ(N)`: every element fixes each letter and has
  its sections in `ρ(N)`. So `N <= ker ρ`, and `ρ(G)` is a quotient of the finite
  group `G/N`. ∎

## Remarks

- **Faithfulness in Theorem A.** Corollary B needs no faithfulness hypothesis;
  Theorem A uses faithfulness only in the last line.
- **Transitivity.** Theorem A allows intransitive first-level actions and a
  different endomorphism at each letter. It does not need `G` to be finitely
  presented.
- **Where division sections escape.** In the adding machine, `φ(2m) = m` maps `2^k Z`
  onto `2^(k-1) Z`. No nontrivial subgroup of `2Z` is mapped into itself, so there
  is nothing to trap.
- **The kernel is the largest trap.** By the argument above, the kernel of the
  action associated with `(Q, φ)` is the largest `N <| G` with `N <= core_G(Q)` and
  `φ(N) <= N`. Corollary B manufactures a finite-index such `N` from any
  endomorphism extension.
