---
rg: 2
id: m11-torsion-linear-host-has-b1-one-proof
kind: route
title: The balanced section g has conjugates summing to zero around the 11-cycle, so the eleven b-conjugates of c form a relation whose only nontrivial section is itself; the odometer's letters still alternate on stable words, so the a-exponent survives, and abelianizing the wreath isomorphism makes the section-exponent matrix act on H_1 by an integral automorphism
target: m11-torsion-linear-host-has-b1-one
requires:
  - m11-linear-activity-self-replicating-group
  - m11-linear-activity-group-b1-two-not-finitely-presented
  - fully-self-replicating-fp-infinity-groups-are-acyclic
  - tits-hosts-for-transitive-local-actions
artifacts:
  - experiments/m11-torsion-linear-host-2026-09-18/torsion_linear_host.py
  - experiments/m11-torsion-linear-host-2026-09-18/torsion_linear_host.out
---

The notation is that of the target. Maps act on the right, and
`(gh)|_x = g|_x h|_{x^{π_g}}`. For `y ∈ X`, `p_y ∈ M_11` satisfies `1^{p_y} = y`, and
`p_y^{-1} (r@1) p_y = r@y`. Every `r` with root `π` equals `(∏_y r|_y@y) · π`, and the
factors commute.

## 1. `R'` is fully self-replicating (item 1)

Let `R_0 = ⟨M_11, a, b⟩`. The proof of `m11-linear-activity-self-replicating-group`
(section 0) writes `p@1` for `p ∈ M_11`, `a@1 = a α^{-1}` and
`b@1 = b (β@3)^{-1} (α@2)^{-1}` as words in `R_0`. The words for `p@1` are the
rigid-stabilizer certificate of `⟨M_11, b⟩`, and `α@2` and `β@3` are conjugates of `α@1`
and `β@1`. Since `r ↦ r@1` is a homomorphism, this gives `R_0@1 ⊆ R_0`, and then
`R_0@y ⊆ R_0` for every `y`.

Now `c = (c@1)(g@2)`, so `c@1 = c (g@2)^{-1}`. Here `g = a α^{-1} a^{-1} α ∈ R_0`, so
`g@2 ∈ R_0 ⊆ R'`. Hence `c@1 ∈ R'`. So `s@1 ∈ R'` for every generator `s`, and
therefore `R'@1 ⊆ R'` and `R'@y ⊆ R'`. This is condition (B).

- **(S)** The sections of the generators are `c`, `g`, `a`, `a^{-1}`, `b`, `α`, `β` and
  `1`, all in `R'`.
- **(A)** The root images are `M_11` together with trivial roots.

So `R'` is fully self-replicating with root image `M_11`, and `ψ : R' ≅ R' ≀_X M_11`.

**Growth.** Since `c` and `g` have trivial root, `c^m = (c^m, g^m, 1, …)` and
`g^m = (a^m, a^{-m}, 1, …)`. So `c^m|_1 = c^m` and `c^m|_{21} = a^m`. The element `a` has
order `11^n` on level `n`, so `c` has infinite order. Every power of `c` lies in any
nucleus, so `R'` is not contracting.

**Activity.** On level `n ≥ 2`, `c` has non-trivial sections exactly at:
- `1^n`, where the section is `c`;
- `1^{n−1} 2`, where it is `g`;
- `1^k 2 1 1^{n−k−2}` and `1^k 2 2 1^{n−k−2}`, for `0 ≤ k ≤ n − 2`, where it is `a^{±1}`.

That is `2n` sections in all, so the activity is linear. The states `a` and `b` are
bounded, and `M_11` is finitary. The automaton `{a, b, c, g}` is finite-state with at
most linear activity, so `R'` is amenable by Amir–Angel–Virág (cited).

**Tits host.** Item 4 of `tits-hosts-for-transitive-local-actions` applies with
`F = M_12` and `F_0 = M_11`.

## 2. The relation `U` (item 2)

Since `b` has trivial root, `b^k = (b^k, α^k, β^k, 1, …)`. So `b^{-k} c b^k` has trivial
root, with section `b^{-k} c b^k` at `1`, section `α^{-k} g α^k` at `2`, section
`β^{-k} β^k = 1` at `3`, and trivial sections elsewhere. Moreover
`α^{-k} (r@y) α^k = r@(y^{α^k}) = r@(y + k)`, with indices mod 11. So

`α^{-k} g α^k = a@(1+k) · (a@(2+k))^{-1}`.

The `a@y` commute (disjoint supports). So

`∏_{k=0}^{10} α^{-k} g α^k = ∏_y a@y · ∏_y (a@y)^{-1} = 1`.

Hence `U = ∏_{k=0}^{10} b^{-k} c b^k` has trivial root, section `U` at `1`, and trivial
sections elsewhere.

**`U` is trivial.** Suppose `U` moved some vertex, and take a moved vertex `v` of minimal
length `n`. Then `n ≥ 1`, since the root of `U` is trivial. We have `v = x v'`, and since
`U` acts on `x v'` as `x · (v')^{U|_x}`, the vertex `v'` is moved by `U|_x`. That forces
`x = 1`, with `v'` moved by `U|_1 = U` and of length `n − 1 < n`. This contradicts the
choice of `v`. So `U = 1`, and `e_c(U) = 11`. The script confirms `U = 1` with its exact
solver.

## 3. The `a`-exponent survives (item 3)

Treat `g` as a fourth generator. Put `S = M_11 ⊔ {a, b, c, g}`, `F = F(S)` and
`R' = F/N`. The word `g^{-1} a α^{-1} a^{-1} α` lies in `N`. The letter sections are
single letters or empty:

| letter | at `1` | at `2` | at `3` | root |
|---|---|---|---|---|
| `a` | `a` | – | – | `α` |
| `a^{-1}` | – | `a^{-1}` | – | `α^{-1}` |
| `b^{±1}` | `b^{±1}` | `α^{±1}` | `β^{±1}` | `1` |
| `c^{±1}` | `c^{±1}` | `g^{±1}` | – | `1` |
| `g^{±1}` | `a^{±1}` | `a^{∓1}` | – | `1` |

**Mass.** For every word `w`, `Σ_x e_a(w|_x) = e_a(w)`. The argument is that of
Lemma 1(iii) of the dead node: each letter contributes the `a`-exponent of its sections,
which is `±1` for `a^{±1}` and `0` for `g^{±1}`, `c^{±1}` and `b^{±1}`.

**Descent.** Lemma 2 of `m11-linear-activity-group-b1-two-not-finitely-presented-proof`
applies. It needs only that letter sections lie in `Q^{±1} ∪ P ∪ {∅}` and that the mass
identity holds, and here `Q = {a, b, c, g}`. So it suffices to show that `e_a(w) = 0` for
every relation `w` that lies on a stable cycle.

**Stable words.** Let `w` be stable at `x`, so every letter is non-finitary and has a
non-finitary section at the point where it is read. By the table:
- a letter `a` must be read at `1`, and it moves the point to `2`;
- a letter `a^{-1}` must be read at `2`, and it moves the point to `1`;
- every other non-finitary letter has trivial root and does not move the point.

So between two consecutive `a`-letters the point is constant, and the signs of the
`a`-letters alternate. Hence `|e_a(w)| ≤ 1`. The root of `w` is `α^{e_a(w)}`, and it is
trivial because `w ∈ N`. So `11 | e_a(w)`, and therefore `e_a(w) = 0`.

It follows that `e_a(N) = 0`, and `e_a` induces a surjection `R' ↠ Z` with `a ↦ 1`.
The script checks the mass identities on every word of length at most `5`, and the bound
`|e_a| ≤ 1` on all `141702` stable pairs of length at most `6`.

## 4. `H_1(R'; Z)` (item 3)

`M_11` is perfect, so `H_1(R')` is generated by `[a]`, `[b]`, `[c]`, and `[g] = 0`
because `g = [a^{-1}, α]`. The relations give:
- `b^{55} = 1` (item 2 of `m11-linear-activity-self-replicating-group`; the script rechecks it), so
  `55 [b] = 0`;
- `11 [c] = 0`, by section 2.

Put `T = ⟨[b], [c]⟩`. It is finite, of exponent dividing `55`, so only the primes `5` and
`11` can divide `|T|`. Moreover `e_a` vanishes on `T` and `e_a([a]) = 1`. So
`H_1(R') = Z[a] ⊕ T`, and `b_1(R') = 1`.

## 5. The known obstructions (item 4)

Here `d = 11`, `M_11 ≤ Alt(11)`, and `char Q = 0` does not divide `|M_11|`.

**FP_2 is unobstructed by the acyclicity theorem.**
- Item 3(d) there needs `dim H_1(R'; k) ≤ 1` for `k = Q`. That holds, since `b_1 = 1`.
- For `k = F_p` with `p > 11`, we have `H_1(R'; F_p) = F_p`, because `T` has order prime
  to `p`. So the bound holds there too.
- The only degree-2 excess that degree-1 classes can produce is item 2(i) (two distinct
  classes) or item 2(ii) (an even degree). Neither applies to a single class in degree 1.
  More directly: the basis tensors `[a]_x ⊗ [a]_y` with `x ≠ y` have odd factors, and some
  element of the 4-transitive group `M_11` swaps `x` and `y`. That element acts on the
  tensor by `−1`, so `E_2 = 0`.

**The other obstructions.**
- Bartholdi's theorem needs contraction, which fails by section 1.
- Characters, Σ and L² are blind for every `R ≅ R ≀_X P`, by
  `self-wreathing-groups-have-full-sigma-invariants`.
- Congruence quotients are blind by item 7 of `tits-hosts-for-transitive-local-actions`.

**FP_10 fails.** Take `a = 1` in item 3 of `fully-self-replicating-fp-infinity-groups-are-acyclic`.
Since `H_1(R'; Q) ≠ 0`, `H_{(d−1)·1} = H_{10}(R'; Q)` is infinite-dimensional. So `R'` is
not of type `FP_10` over `Q`.

## 6. The odometer obstruction (item 5)

The hypotheses are those of item 5 of the target. Put `x_1 = x_a` and
`x_2 = x_a^{π_a} ≠ x_1`.

**Mass.** Each letter `s ≠ a` has sections of total `a`-exponent `0`. The letter `a`
has total `a`-exponent `1`. So, as in section 3, `Σ_x e_a(w|_x) = e_a(w)` for every word
`w`. By Lemma 2 of the dead node's proof, it is enough to treat relations `w` on stable
cycles.

**Stable words.** Let `w` be stable.
- A letter `a` is read at `x_1`, since that is its only non-finitary section, and it
  moves the point to `x_2`.
- A letter `a^{-1}` has its non-finitary section `(a|_{y^{π_a^{-1}}})^{-1}` at
  `y = x_2`, and it moves the point to `x_1`.
- The other non-finitary letters have trivial root and do not move the point.

So the signs of the `a`-letters alternate, and `|e_a(w)| ≤ 1`. The root of `w` is
`π_a^{e_a(w)}`, which is trivial, and `π_a ≠ 1`. So `e_a(w) = 0`.

**Conclusion.** `e_a(N) = 0`. The generators in `P` and in `Q ∖ {a}` map to `0` and `a`
maps to `1`, so `e_a` induces a surjection `R ↠ Z`. With root image in `Alt(X)` and
`|X| ≥ 3`, item 3 of the acyclicity theorem, with `a = 1`, makes `H_{|X|−1}(R; Q)`
infinite-dimensional. So `R` is neither `FP_{|X|−1}` nor `FP_∞`.

## 7. The unimodular screen (item 6)

**The section-sum map is an automorphism.** Abelianize `ψ : R ≅ R^X ⋊ P`. For a
semidirect product, `H_1(N ⋊ P) = H_1(N)_P ⊕ H_1(P)`. Here `P` permutes the coordinates of
`H_1(R^X) = ⊕_x H_1(R)` transitively, so the coinvariants are `H_1(R)`, by the sum map.
Also `H_1(P) = 0`. So the map

`φ : H_1(R; Z) → H_1(R; Z)`, `[r] ↦ Σ_x [r|_x]`,

is an isomorphism: it is the abelianization of `ψ` followed by these identifications.

**It is a quotient of `μ`.** Let `ε : Z^Q → H_1(R; Z)` send `e_s ↦ [s]`. It is onto,
because `R = ⟨P, Q⟩` and `[p] = 0` for `p ∈ P`. Let `μ` act on `Z^Q` by
`e_s ↦ Σ_t μ_{s,t} e_t`. Then `φ(ε(e_s)) = Σ_x [s|_x] = ε(μ e_s)`, because each `s|_x`
is a word over `P ∪ Q` and letters of `P` contribute `0`. So `φ ∘ ε = ε ∘ μ`.

Let `K = ker(ε ⊗ Q)`. The identity `φ ∘ ε = ε ∘ μ` gives `μ(K) ⊆ K`. So `φ_Q` on
`H_1(R; Q) = Q^Q / K` is induced by `μ`, and its characteristic polynomial `χ_φ` divides
`χ_μ = det(t − μ)`.

**Integrality.** `φ` induces an automorphism of the lattice `Λ = H_1(R; Z)/torsion`, which
is `≅ Z^{b_1}` and spans `H_1(R; Q)`. So `χ_φ` is monic with integer coefficients and
`χ_φ(0) = ±det(φ|Λ) = ±1`. By Gauss's lemma, `χ_φ` is a product of monic irreducible
integer factors of `χ_μ`. Their constant terms are nonzero integers whose product is
`±1`, so each is `±1`.

Hence `b_1 = deg χ_φ` is at most the total degree of the factors `f` of `χ_μ` with
`f(0) = ±1`, counted with multiplicity.

**The examples** are computed by the script with sympy:

| design | `χ_μ` | bound on `b_1` |
|---|---|---|
| `R = ⟨M_11, a, b, c⟩`, `c = (c, a, …)` | `(t − 1)^3` | `3` |
| `R'` | `t (t − 1)^3` | `3` |
| `z = (z, h, …)`, `h = (z, z, 1, …) α` | `(t − 2)(t + 1)` | `1` |
| `z = (z, h, …)`, `h = (z, z, z, 1, …) α` | `t² − t − 3` | `0` |

The last two rows are conditional on full self-replication, which is not proved here.
∎
