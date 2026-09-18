---
rg: 2
id: one-ended-schreier-orbits-force-index-zero-proof
kind: route
title: One end makes the labelled germ of a near-equivariant map unique on a free orbit, so the map is a bijection of orbits and its index vanishes
target: one-ended-schreier-orbits-force-index-zero
requires: []
artifacts:
  - research/artifacts/gq-bh-bh-shell-kazhdan-rigidity-attempt.md
---

Notation as in the claim. Fix a finite set `F` outside which every defining identity holds and which contains `N \ dom(sigma)` and `N \ im(sigma)`.

Let `Gamma^phi_A` be the *source graph* on an orbit `A`: vertices `A`, edges `{x, rho_(phi(g)) x}` for `g ∈ S`. Since `phi` is an automorphism, `phi(S)` is a finite generating set of `P`, so `Gamma^phi_A` is the Schreier graph of the same transitive action for another finite generating set. It is connected, locally finite and vertex-transitive, and the identity is a quasi-isometry `Gamma^phi_A -> Gamma_A`, so the two have the same number of ends.

## Lemma 0 (finite changes)

If partial bijections `sigma, sigma'` of `N` agree on a cofinite `C ⊆ dom(sigma) ∩ dom(sigma')`, then `ind(sigma) = ind(sigma')`.

**Proof.** `sigma` restricts to a bijection of `dom(sigma) \ C` onto `im(sigma) \ sigma(C)`, so `ind(sigma) = |N \ sigma(C)| - |N \ C|`, which depends only on `C` and `sigma(C) = sigma'(C)`. `∎`

## Lemma 1 (orbits go to orbits)

Let `sigma` be `phi`-twisted near-equivariant and `A` an infinite orbit with `Gamma_A` one-ended. Then:
1. `A \ F` has one infinite component `C` in `Gamma^phi_A`, and `C` is cofinite in `A`;
2. `sigma(C)` lies in a single orbit `A'`;
3. `sigma(C)` has finite coboundary in `Gamma_(A')`; if `Gamma_(A')` is one-ended, `sigma(C)` is cofinite in `A'`.

**Proof.** (1) is the definition of one end for a locally finite connected graph: the complement of a finite set has exactly one infinite component, and the finite components together with `F` form a finite set.

(2) For `x ∈ C` and `g ∈ S` with `rho_(phi(g))x ∈ C`, the identity gives `sigma(rho_(phi(g))x) = rho_g sigma(x)`, so `sigma` maps edges of `C` to edges of the target Schreier graph. As `C` is connected, `sigma(C)` is connected, hence inside one orbit `A'`.

(3) Let `y = sigma(x) ∈ sigma(C)` and `g ∈ S`. Then `rho_g y = sigma(rho_(phi(g))x) ∈ sigma(C)` whenever `rho_(phi(g))x ∈ C`, which fails for only finitely many `x`. So only finitely many edges of `Gamma_(A')` leave `sigma(C)`: it has finite coboundary. A one-ended graph has no subset with finite coboundary that is both infinite and co-infinite, and `sigma(C)` is infinite, so it is cofinite in `A'`. `∎`

## Lemma 2 (germ rigidity on a free orbit: item 2)

Let `A` be a free orbit with `Gamma_A` one-ended, and `sigma` `phi`-twisted near-equivariant. Fix `x_0 ∈ C` and put `y_0 = sigma(x_0)`. Then

    theta: A -> A',    theta(rho_(phi(w)) x_0) = rho_w y_0,

is a well-defined bijection onto the orbit `A'` of `y_0`, and `sigma = theta` on `C`.

**Proof.** *Well defined and injective on `A`.* Freeness of `A` says `rho_u x_0 = rho_v x_0` implies `u = v`, so every point of `A` is `rho_(phi(w))x_0` for exactly one `w ∈ P`, and `theta` is well defined and injective as a map on the index set. Its image is `{rho_w y_0 : w ∈ P} = A'`, so `theta` is a bijection `A -> A'`, and `A'` is free as well: `rho_w y_0 = y_0` forces `theta(rho_(phi(w))x_0) = theta(x_0)`, hence `w = 1`.

*Agreement on `C`.* Let `x ∈ C`. As `C` is connected in `Gamma^phi_A`, there is a path `x_0, rho_(phi(g_1))x_0, rho_(phi(g_2 g_1))x_0, ...` inside `C` ending at `x`, so `x = rho_(phi(w))x_0` for the word `w = g_k ... g_1`. Applying the defining identity along the path, once per edge, gives `sigma(x) = rho_w y_0 = theta(x)`. `∎`

## Item 3

Let `Z ⊆ N` be the finite set of points outside the free one-ended orbits, and let `U = N \ Z` be the union of those orbits. By Lemma 1 and Lemma 2, `sigma` maps each such orbit `A`, off a finite set, onto the free orbit `A'` by the bijection `theta_A`; by Lemma 1(3) applied with `A'` one-ended — which holds since `A'` is one of the orbits in `U`, or else `A'` meets `Z` in a cofinite subset, impossible as `Z` is finite and `A'` is infinite — the image is cofinite in `A'`.

The induced map `A ↦ A'` on these orbits is injective: two distinct orbits would have cofinite images in one `A'`, contradicting injectivity of `sigma`. It is also onto: if an orbit `B ⊆ U` were missed, then `B ∩ im(sigma)` would be finite, so `N \ im(sigma)` would be infinite, contradicting that `ind(sigma)` is an integer.

So the union `theta = ⊔_A theta_A` is a bijection of `U` onto `U`, and `sigma` agrees with `theta` on a cofinite subset `C^* ⊆ U` (take the union of the `C`'s, which omits only finitely many points of each of finitely many exceptional orbits, and note that only finitely many orbits meet `F`). Extend `theta` by the identity on `Z` to a bijection of `N`; it still agrees with `sigma` on `C^*`, which is cofinite in `N`. By Lemma 0,

    ind(sigma) = ind(theta) = 0.

Hence `ind(sigma) != 1`, and no window-zero witness exists. `∎`

## Item 1

Let `sigma` be shift-like, `phi`-twisted near-equivariant. Because `phi` is an automorphism, `Fix(rho)` is also the fixed set of the twisted action. For `x ∈ Fix(rho)` off `F` and `g ∈ S`,

    rho_g sigma(x) = sigma(rho_(phi(g)) x) = sigma(x),

so `sigma(x) ∈ Fix(rho)`. Likewise, if `x ∉ Fix(rho)`, pick `g` with `rho_(phi(g))x != x`; then `rho_g sigma(x) = sigma(rho_(phi(g))x) != sigma(x)` by injectivity, so `sigma(x) ∉ Fix(rho)`. So both `Fix(rho)` and its complement are `sigma`-invariant off a finite set.

Now suppose both are infinite. A single forward orbit `{sigma^k(x_0)}` stays, off a finite set, inside whichever of the two sets contains `x_0`, so it cannot be cofinite in `N`. This contradicts shift-likeness. Since `P` is infinite and the near action is faithful, some `g != 1` moves infinitely many points, so the complement of `Fix(rho)` is infinite. Hence `Fix(rho)` is finite. `∎`

## Item 4

Let `P` be infinite, finitely generated and simple.

*No proper finite-index subgroup.* If `[P:H] = n < ∞`, the action on `P/H` gives `P -> Sym(n)` with normal kernel `K`. Simplicity gives `K = 1`, making `P` finite, or `K = P`, making `H = P`.

*One end.* A finitely generated group has `0`, `1`, `2` or infinitely many ends. `P` is infinite, so not `0`. Two ends means virtually cyclic, which gives a proper finite-index subgroup. Infinitely many ends gives, by Stallings' theorem, a splitting of `P` over a finite subgroup, hence an action on a tree with finite edge stabilizers; the kernel of that action lies in an edge stabilizer, so it is finite, hence trivial by simplicity, and then Karrass–Pietrowski–Solitar makes `P` virtually free, which again gives a proper finite-index subgroup. So `P` is one-ended. `∎`

## Item 5

Let `rho` be free. Every orbit is free, and its Schreier graph is isomorphic to the Cayley graph of `P` for `S`, which is one-ended by item 4. So item 3 applies with `Z = ∅`, giving `ind(sigma) = 0` for every twisted near-equivariant `sigma`. `∎`

## Item 6

Let `Gamma_A` have exactly two ends. It is locally finite, connected and vertex-transitive, hence quasi-isometric to `Z`. `Aut(Gamma_A)` acts on the two-element set of ends, giving `epsilon: Aut(Gamma_A) -> Z/2`, and on `ker(epsilon)` the translation number along the quasi-line is a homomorphism to `Z` whose kernel is the automorphisms of bounded displacement. Composing with the action of `P` gives `chi: P -> Z ⋊ Z/2`, whose kernel is normal.

- If `ker(chi) = 1`, then `P` embeds in `Z ⋊ Z/2` and is virtually cyclic, so it is not infinite simple.
- If `ker(chi) = P`, every element of `P` acts with bounded displacement. But `P` is transitive on the infinite set `A`, so it moves a fixed vertex arbitrarily far along the quasi-line, and displacements are unbounded.

Both cases are impossible. `∎`

## Item 7

By item 1, `Fix(rho)` is finite, and by item 4 there is no finite orbit of size `> 1`, since a finite orbit gives a finite-index stabilizer: the orbit is then a single point by the same argument, so the finite orbits are exactly the finitely many fixed points. All other orbits are infinite, and by item 6 none has two ends. If every one of them were free, item 3 would exclude the witness, so some orbit has a nontrivial stabilizer. For such an orbit, the proof of item 3 uses freeness only through Lemma 2, so the remaining possibilities are a one-ended non-free orbit, where the per-orbit deficit is not controlled, and an orbit with infinitely many ends, where Lemma 1(1) and hence the whole argument fails. `∎`
