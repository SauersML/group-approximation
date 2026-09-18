---
rg: 2
id: one-ended-near-regular-actions-have-a-realization-defect-proof
kind: route
title: A near-equivariant partial bijection from a free orbit of a one-ended group is right multiplication off a finite set, so it has index zero
target: one-ended-near-regular-actions-have-a-realization-defect
requires: []
artifacts:
  - research/artifacts/gq-bh-bh-shell-kazhdan-rigidity-attempt.md
---

Notation is as in the claim. A *partial bijection* `phi: A ⇀ B` between sets is a bijection between a cofinite subset `dom(phi)` of `A` and a cofinite subset `im(phi)` of `B`. Its index is

    ind(phi) = |B \ im(phi)| - |A \ dom(phi)|.

## Lemma 0 (finite changes)

If two partial bijections `phi, phi'` agree on a cofinite set `C ⊆ dom(phi) ∩ dom(phi')`, then `ind(phi) = ind(phi')`.

**Proof.** `phi` restricts to a bijection from `dom(phi) \ C` onto `im(phi) \ phi(C)`. So

    ind(phi) = |B \ phi(C)| - |A \ C|,

and the same formula holds for `phi'`, since `phi(C) = phi'(C)`. `∎`

## Lemma 1 (one-ended rigidity)

Let `A` be a genuine `P`-set and `B = P` with the left regular action. Let `chi: B ⇀ A` be a partial bijection that is *near-equivariant*: for each `g ∈ S`, `chi(gx) = g·chi(x)` for all but finitely many `x ∈ dom(chi)`. Then:
- there is `o' ∈ A` with trivial stabilizer such that `chi(x) = x·o'` for all `x` in a cofinite set `C ⊆ P`;
- `A = O ⊔ F`, where `O = P·o'` is a free orbit and `F` is finite;
- `ind(chi) = |F|`.

**Proof.** Put `psi(x) = x^-1·chi(x) ∈ A` for `x ∈ dom(chi)`. For `g ∈ S` and all but finitely many `x`,

    psi(gx) = x^-1 g^-1 · g·chi(x) = psi(x).

So there is a finite set `E ⊆ P` such that `psi` is constant along every edge `x — gx` (`g ∈ S`) of the Cayley graph with both endpoints outside `E`. Since `P` is one-ended, the graph minus `E` has exactly one infinite component `C`, and `C` is cofinite. So `psi` is constant on `C`, say equal to `o'`, and `chi(x) = x·o'` on `C`.

Suppose some `h ≠ 1` fixes `o'`. For all but finitely many `x`, both `x` and `xh` lie in `C`, and then `chi(x) = x·o' = xh·o' = chi(xh)` with `x ≠ xh`. This contradicts injectivity. So `O = P·o'` is free, and `x ↦ x·o'` is a bijection `P → O`.

Now `im(chi) ⊆ O ∪ chi(dom(chi) \ C)`, and `A \ im(chi)` is finite, so `F = A \ O` is finite. The partial bijection `chi` agrees on `C` with the total bijection `P → O ⊆ A`, `x ↦ x·o'`, whose index is `|A \ O| - 0 = |F|`. Lemma 0 gives `ind(chi) = |F|`. `∎`

## Proof of the claim

**Item 2, and item 1.** Let `Z` be a free transitive realization of `alpha` and `Y` any realization. Identify `Z` with `P`. The identity on `Y ∩ Z` is a partial bijection `chi: Z ⇀ Y`, since both sets are cofinite in `Y ∪ Z` because `Y △ N` and `Z △ N` are finite. Both actions agree with `alpha(g)` off finite sets, so `chi` is near-equivariant.

By Lemma 1, `Y = O ⊔ F` with `O` free and `F` finite, and `ind(chi) = |F|`. Counting directly,

    ind(chi) = |Y \ Z| - |Z \ Y| = y(Y) - y(Z).

So `y(Y) = delta(alpha) + |F|`, where `delta(alpha) = y(Z)`. If `Y` is also free transitive, then `F = ∅` and `y(Y) = y(Z)`, which is item 1.

**Item 3.**
- *Conjugation by `tau`.* Let `tau` be the class of a bijection `tau_hat` of `N`. Extend `tau_hat` to `N ∪ Z` by the identity on `Z \ N`, and transport the free transitive realization `Z` of `alpha` along it. This gives a free transitive realization of `tau alpha tau^-1` on `tau_hat(Z ∩ N) ∪ (Z \ N)`, whose `y` equals `|Z \ N| - |N \ tau_hat(Z ∩ N)| = y(Z)`, because `tau_hat` is a bijection of `N`.
- *Automorphisms.* Precomposing with `theta ∈ Aut(P)` does not change the underlying set or its orbits, so `Z` is still a free transitive realization.
- *Conjugation by `s`.* Transport `Z` by `z ↦ z+1`, extended to the finitely many points of `Z` outside `N`. This lowers `|Z \ N| - |N \ Z|` by exactly one; for example `N` becomes `N_{>=1}`.

**Item 4.** `c_0 = lambda(P)` acts freely and transitively on `N`, so `delta(c_0) = 0`. Then `delta(c_k) = -k` by item 3. For `k >= 0`, `c_k` acts freely and transitively on `N_{>=k}` and fixes `0, ..., k-1`, which gives a realization on `N`. For `k < 0`, item 2 gives `y(Y) = -k + |F| >= 1` for every realization `Y`, so there is none on `N`.

**Item 5.** Suppose `tau c_j tau^-1 ⊆ c_k`. The map `c_k: P -> NearSym(N)` is injective, because `lambda_g` moves every point when `g ≠ 1`. So there is an injective homomorphism `theta: P -> P` with `tau c_j(g) tau^-1 = c_k(theta(g))` for all `g`.

The near action `beta = c_k ∘ theta` is realized by the genuine action of `P` through `theta` on the free transitive realization `Z_k` of `c_k`. That action has exactly `[P : theta(P)]` orbits, each free. Since `beta = tau c_j tau^-1` is near-regular, item 2 allows only one infinite orbit, so `theta(P) = P` and `theta ∈ Aut(P)`.

Then `Z_k` is a free transitive realization of `beta`, so `delta(beta) = delta(c_k) = -k`. But item 3 gives `delta(beta) = delta(c_j) = -j`. So `j = k`.

The three consequences follow:
- `tau = 1`, `k = 0` is the one-ended node;
- conjugacy in `ker(eta)` is conjugacy by index-zero near permutations, because `ker(eta)` lies in the index-zero part;
- a `ker(eta)`-conjugate of `c_(eps j)` containing `c_(-eps)` would give `-eps = eps j`, which is impossible for `0 <= j <= N` with `eps = 1`. For `eps = -1` it would give `j = -1`, again excluded.

**Item 6.** Suppose `rho: W_N^1 -> Sym(Y)` realizes the near action of `W_N^1` on some `Y` with `y(Y) <= 0`. The gate puts `c_-1` inside `W_N^1`, and restricting `rho` to it gives a realization of `c_-1` on `Y`. By item 2, `y(Y) = delta(c_-1) + |F| = 1 + |F| >= 1`, a contradiction.

The canonical realizations `c_hat_j(g) ∈ Sym(N)` of the `c_j`, `0 <= j <= N`, generate `G_hat`, which maps onto `W_N^1` with kernel `G_hat ∩ FSym(N)`. If that kernel were trivial, the inverse isomorphism would realize `W_N^1` on `N`. So the kernel is nontrivial.

For `eps = -1`, `W_N^-1` contains `c_-N` with `delta = N`, so every realization already has `y >= N`. The gate element `c_1` has `delta = -1` and adds nothing. `∎`
