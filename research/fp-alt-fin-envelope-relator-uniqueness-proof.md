---
rg: 2
id: fp-alt-fin-envelope-relator-uniqueness-proof
kind: route
title: A relator-satisfying tuple gives a homomorphism fixing Alt_fin pointwise, and the trivial centralizer forces the tuple
target: fp-alt-fin-envelopes-are-unique-solutions-of-their-relators
requires: []
---

Notation as in the claim. Products are compositions.

**Step 1. A homomorphism.** Let `gamma' ∈ Sym(Omega)^k` satisfy every `r ∈ R`,
and put `G' = < S_0, gamma'_1, ..., gamma'_k >`. Let `F` be the free group on
`S_0 ⊔ {g_1, ..., g_k}`. The assignment `s -> s`, `g_i -> gamma'_i` defines a
homomorphism `F -> G'` whose kernel contains `R`, hence its normal closure.
Since `G = F / <<R>>`, it induces a homomorphism `phi : G -> G'` with
`phi(s) = s` and `phi(gamma_i) = gamma'_i`.

**Step 2. `phi` fixes `<S_0>` pointwise.** Let `h ∈ <S_0> <= G`. Write
`h = u(S_0)` with `u` a word in `S_0` alone. Then `phi(h)` is `u` evaluated in
`G'`, with the same permutations `s`, so `phi(h) = h`.

**Step 3. The centralizer.** Fix `i` and a 3-cycle `tau ∈ Alt_fin(Omega)`. The
conjugate `gamma_i tau gamma_i^-1` is again a 3-cycle, so it lies in
`Alt_fin(Omega) <= <S_0>`. By Step 2,

```text
gamma'_i tau gamma'_i^-1 = phi(gamma_i tau gamma_i^-1) = gamma_i tau gamma_i^-1 .
```

So `delta = gamma_i^-1 gamma'_i` commutes with every 3-cycle. Suppose
`delta(a) = b != a`. Choose distinct `c, d ∉ {a, b}` (possible, `Omega` is
infinite) and `tau = (a c d)`. Then `delta tau delta^-1 = (b delta(c) delta(d))`
moves `b`, while `tau` fixes `b`, a contradiction. Hence `delta = 1` and
`gamma'_i = gamma_i`. This proves clause 1.

**Step 4. Computability.** Encode a candidate as the values
`gamma'_i(n)` and `gamma'_i^-1(n)` for all `i` and `n`, each in `{1, ..., D(n)}`.
Let `T` be the tree of finite initial assignments (on `n <= N`) that refute none
of the following conditions, each checked only when every value it needs has
been assigned:
- (a) `gamma'_i(gamma'_i^-1(n)) = n` and `gamma'_i^-1(gamma'_i(n)) = n`;
- (b) for each `r ∈ R` and each `n`, the trajectory of `n` under the letters of
  `r` returns to `n`. Letters from `S_0` are evaluated by their algorithms.

`T` is computable, closed under prefixes, and finitely branching with recursive
bound `D`. Its infinite paths are exactly the tuples of mutually inverse maps
with values below `D` that satisfy `R`, i.e. the `D`-bounded solutions. The
tuple `gamma` is one, and by clause 1 it is the only one.

Fix `(i, n)`. Some level `N` of `T` has all its nodes agreeing on the value at
`(i, n)`. Otherwise every level has a node whose value there differs from
`gamma_i(n)`. There are at most `D(n)` values, so one value `v != gamma_i(n)`
occurs at infinitely many levels, hence at every level by prefix closure. By
König's lemma the subtree of nodes with value `v` has an infinite path, a second
solution, contradicting clause 1. Searching `N = 1, 2, ...` and listing level
`N` of `T` computes `gamma_i(n)`. The same holds for `gamma_i^-1`. `∎`
