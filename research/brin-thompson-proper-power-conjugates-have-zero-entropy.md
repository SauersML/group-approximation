---
rg: 2
id: brin-thompson-proper-power-conjugates-have-zero-entropy
kind: claim
title: Elements of Brin--Thompson groups nV have finite topological entropy, so an element of nV conjugate to a proper power of itself has zero entropy, while the baker map has entropy at least log 2
distinct_from:
  bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets: that gives zero periodic exponents, open periodic sets and logarithmic exponent growth under the same relation; this adds topological entropy, an invariant those conditions do not determine.
---

**ESTABLISHED** (elementary; no novelty claimed).

**Setting.**
- `C = {0,1}^N`, `nV` acts on `C^n` by tables, and `L(g)` is the least table
  length. All of this is as in `bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets`.
- For `x ≠ y` in `C^n`, `m(x,y)` is the least, over coordinates `j`, of the
  length of the longest common prefix of `x_j` and `y_j`. The metric
  `d(x,y) = 2^(-m(x,y))` (with `d(x,x) = 0`) induces the product topology.
- Topological entropy is taken in the Bowen--Dinaburg form. `E` is
  `(N,ε)`-separated for `T` if for all `x ≠ y` in `E` there is `0 ≤ t < N` with
  `d(T^t x, T^t y) > ε`. `s_N(T,ε)` is the largest size of such a set, and
  `h(T) = lim_(ε→0) limsup_(N→∞) (1/N) log s_N(T,ε)`.

**Statement.**
1. **Finite entropy.** `h(g) ≤ n · L(g) · log 2` for every `g ∈ nV`.
2. **Conjugacy and powers.** For homeomorphisms `T, f` of a compact metric
   space, `h(f T f^-1) = h(T)` and `h(T^m) = |m| h(T)` for every `m ≠ 0`.
3. **Proper-power relations.** Let `g ∈ nV` and let `f` be any homeomorphism of
   `C^n` with `f g^k f^-1 = g^l`, where `k, l ≠ 0` and `|k| ≠ |l|`. Then
   `h(g) = 0`.
4. **Baker map.** `b(x_0 x', y) = (x', x_0 y)` lies in `2V` and has
   `h(b) ≥ log 2`. So by item 3, `b` satisfies no relation `f b^k f^-1 = b^l`
   with `|k| ≠ |l|`, for any homeomorphism `f`.

**Scope.**
- Item 3 is a necessary condition on the element `g` of any witness for
  `bs12-embeds-in-brin-thompson-2v`, alongside the periodic-set conditions. It
  says nothing about the conjugator `f`, which may have positive entropy; the
  recorded baker-map conjugator of the odometer attempt does.
- Where the conjugators are themselves proper-power conjugates, as for the
  generators of Higman's group, item 3 applies to them too. See
  `higman-group-images-in-nv-force-zero-entropy-bs12-cycles`.

The proof is `brin-thompson-zero-entropy-proof`.
