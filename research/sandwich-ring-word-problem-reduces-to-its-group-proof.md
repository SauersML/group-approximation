---
rg: 2
id: sandwich-ring-word-problem-reduces-to-its-group-proof
kind: route
title: Spanning by length reduction, independence by an explicit left module on irreducible words
target: sandwich-ring-word-problem-reduces-to-its-group
requires: []
---

Here `Z[T]<p,q>` is the coproduct of unital rings `Z[T] * Z<p,q>`. It is
the ring freely obtained from `Z[T]` by adjoining two elements that commute
neither with each other nor with `T`. A **group letter** is an element of
`T \ {1}`.

**1. Spanning.** Words over `(T\{1}) ⊔ {p,q}` span `Z[T]<p,q>` over `Z`,
and so they span `U`. In `U` two rules hold:

- `t t' = (tt')` for adjacent group letters, which is the empty word when
  `tt' = 1`;
- `p g q = p q - 1`, which is the defining relation rewritten.

Each rule replaces a word by a Z-combination of strictly shorter words. By
induction on length, irreducible words span `U`.

**2. A left module.** Let `N` be the free Z-module on irreducible words.
Every irreducible word is uniquely `u w_0`, where `u in T` (with `u = 1`
meaning no leading group letter) and `w_0` is an irreducible word not
starting with a group letter. Also, `u w_0` is irreducible for every `u`,
because a leading letter is never the middle of `p g q`. So
`N = Z[T] ⊗ N_0` as abelian groups. Define Z-linear maps:

- `λ_t (u w_0) = (tu) w_0` for `t in T`: left multiplication on the first
  factor, so `t -> λ_t` is a group action, and it extends to a ring map
  `Z[T] -> End(N)`;
- `λ_q (w) = q w`, which is irreducible, since a leading `q` is in no
  `p g q`;
- `λ_p (w) = p q w' - w'` if `w = g q w'` (first letter exactly `g`, second
  letter `q`), and `λ_p (w) = p w` otherwise.

Both outputs of `λ_p` are irreducible. In the first case `w'` and `q w'` are
irreducible and `p q` has no middle letter. In the second case the only new
subwords start with `p`, and `p u q` would need `w` to start with `g q`.

By the coproduct universal property these define a ring map
`Z[T]<p,q> -> End_Z(N)`. It kills `p(1-g)q - 1`. Indeed `λ_q w = q w` does
not start with a group letter, so `λ_p λ_q w = p q w`. Also
`λ_g λ_q w = g q w`, so `λ_p λ_g λ_q w = p q w - w`. The difference is `w`.
This gives a ring map `Φ : U -> End_Z(N)`.

**3. Independence.** Let `ev(u) = Φ(u)(∅)`. For an irreducible word
`W = x_1 ... x_m`, induction from the right shows
`Φ(x_k)(x_{k+1}...x_m) = x_k x_{k+1} ... x_m`:

- a group letter `x_k` is not followed by a group letter;
- `x_k = p` is not followed by `g q`, since `W` has no `p g q`;
- `x_k = q` is always prepended.

So `ev(W) = W`. If `Σ c_W W = 0` in `U`, applying `ev` gives `Σ c_W W = 0`
in `N`, so every `c_W = 0`. With step 1, the irreducible words are a
Z-basis of `U`, and `ev : U -> N` is injective. This re-proves `Z[T] <= U`,
since group letters and `∅` are irreducible.

**4. Algorithm.** Let `T` be finitely generated with solvable word problem.
Represent group letters by words in the generators of `T`. Compute `ev(E)`
for a ring expression `E` by structural recursion:

- `ev(E_1 + E_2) = ev(E_1) + ev(E_2)`;
- `ev(E_1 E_2) = Φ(E_1)(ev(E_2))`, where `Φ` of a product is a composite and
  `Φ` of a generator is given by the formulas above.

The formulas need two tests: "is `tu = 1`?" and "is this letter `g`?". Both
are the word problem of `T`. Then decide `ev(E) = 0` by collecting like terms.
Two irreducible words are equal iff they have the same letter pattern and
their group letters agree in `T`. By injectivity of `ev`, `E = 0` in `U` iff
`ev(E) = 0`. Matrices over `U` are compared entrywise. `∎`
