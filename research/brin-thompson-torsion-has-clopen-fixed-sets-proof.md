---
rg: 2
id: brin-thompson-torsion-has-clopen-fixed-sets-proof
kind: route
title: Proof that torsion in nV fixes clopen sets, that minimal dihedral actions by involutions of nV are free, and of the level-coboundary finiteness criterion
target: brin-thompson-torsion-has-clopen-fixed-sets
requires: []
---

Notation as in the target. A *box* is `B = [p_1] × ... × [p_n]`; its *shape* is `(|p_1|, ..., |p_n|)`.
The canonical map from `B` onto a box `B'` of shape `ℓ'` is `(p_i w_i) -> (q_i w_i)`.

**Item 1.** Suppose `g` agrees on a nonempty open set with two prefix replacements `(p -> q)` and
`(p' -> q')`. In coordinate `i` this gives `q_i σ^(|p_i|)(x) = q'_i σ^(|p'_i|)(x)` for all `x` in a
nonempty cone. If `|p_i| - |q_i| ≠ |p'_i| - |q'_i|`, comparing the two sides forces every `x` in that
cone to be eventually periodic with a fixed period, which is false. So `c_g` does not depend on the
chosen box. Refining a box appends the same suffix to `p_i` and `q_i`, so `c_g` is constant on each box
of a representing partition, hence locally constant. Composing two prefix replacements adds the
length changes, which gives the cocycle identity.

**Item 2.** Let `g^m = 1` and `g y = y`. The cocycle identity gives
`0 = c_(g^m)(y) = Σ_(j<m) c_g(g^j y) = m · c_g(y)`, so `c_g(y) = 0`. Take a box `B ∋ y` on which `g`
is a prefix replacement `(p_i) -> (q_i)`; now `|q_i| = |p_i|`. Write `y = (p_i w_i)`. Then
`g y = (q_i w_i) = y` forces `q_i = p_i` for every `i`, so `g` is the identity on `B`. Hence `Fix(g)`
is open. It is closed, so it is clopen. For a periodic group this is exactly triviality of the germ of
every element at each of its fixed points.

**Item 3.** Write `t = ab` and `r_k = t^k a` (`k ∈ Z`); these are all the reflections of `D_∞`, each an
involution in `nV`, and `t r_k t^(-1) = r_(k+2)`. Let `F_k = Fix(r_k) ∩ Z`, which is open in `Z` by
item 2 (and closed).
- Every orbit is infinite, since `Z` is infinite and the action is minimal. So no point of `Z` is fixed
  by a nontrivial power of `t`. Hence a point lies in at most one `F_k`, because two different
  reflections fixing it would make a nontrivial power of `t` fix it.
- Let `N = ∪_k F_k`, the set of points with nontrivial stabilizer. It is open and invariant: `g F_k` is
  the fixed set in `Z` of `g r_k g^(-1)`, which is again a reflection. If `N ≠ ∅`, its complement is a
  proper closed invariant subset, which by minimality is empty. So `N = Z`.
- Then `Z` is covered by the disjoint open sets `F_k`. By compactness only finitely many are nonempty.
  But `t F_k = F_(k+2)`, and `t` maps nonempty sets to nonempty sets, so all `F_(k+2j)` are nonempty.
  This is a contradiction, so `N = ∅` and the action is free.
- Nekrashevych, arXiv:1601.01033 (TeX read on MSI, 2026-09-18), Theorem 1.1 (`th:theoremone`) assumes
  a fixed point `ξ` of `a`, and his Lemma `lem:partition` needs `Fix(a)` to have empty interior. Both
  fail for a minimal dihedral action by involutions of `nV`, by the argument above.

**Item 4, "if".** Let `β` be continuous with `c_h = β∘h - β` for `h ∈ H`, and let `S` be a finite
generating set.
- `β` is locally constant with finitely many values, so there is `L` such that `β` is constant on every
  box all of whose sides are at least `L`. Each `s ∈ S` is a canonical map on every box all of whose
  sides are at least `L_s`.
- Fix `N ≥ L + max|β| + max_s L_s`. For `y ∈ C^n` let `P(y)` be the box containing `y` of shape
  `N·(1,...,1) + β(y)`. If `y' ∈ P(y)` then `β(y') = β(y)`, so `P(y') = P(y)`. Hence the sets `P(y)`
  form a finite partition `𝒫_N` of `C^n` into boxes.
- For `s ∈ S`, `s` is canonical on `P(y)`, so `s(P(y))` is a box containing `s y`, of shape
  `N + β(y) + c_s(y) = N + β(s y)`. So `s(P(y)) = P(s y)`. Every generator therefore permutes `𝒫_N` by
  canonical maps, and so does every `h ∈ H`.
- An element acting by canonical maps on the boxes of `𝒫_N` is determined by the induced permutation.
  So `H` embeds in `Sym(𝒫_N)` and is finite.

**Item 4, "only if".** If `H` is finite, put `β(y)_i = max_(g ∈ H) (-c_g(y)_i)`. It is continuous, and
`c_(gh)(y) = c_g(h y) + c_h(y)` gives `β(h y) = β(y) + c_h(y)` coordinatewise.

**Item 5.** If `g y = g' y`, then `g^(-1) g'` fixes `y` and has finite order, so `c_(g^(-1) g')(y) = 0`
by item 2. The cocycle identity turns this into `c_g(y) = c_(g')(y)`, so `β_y` is well defined on `H y`,
and `c_h(z) = β_y(h z) - β_y(z)` holds on the orbit. The equivalence then follows from item 4.
