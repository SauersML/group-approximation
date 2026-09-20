---
rg: 2
id: lifted-thompson-t-shift-template-dies-for-all-words
kind: claim
title: "The stabilizer function of the Sh_3 template in T-bar is interval-proper, so the explicit shift template has unbounded cross-commutator area for every system of vertex words"
distinct_from:
  commuting-conjugate-commutator-area-localizes-conjugators: that is the group-independent word-level localization lemma; this applies it inside T-bar to the stabilizer group D = C(c_I) ∩ C(c_K), identifies the class invariant d(sI), and settles the property (P) left open by wave 20.
artifacts:
  - research/lifted-thompson-t-shift-template-dies-proof.md
---

**ESTABLISHED (written proof; not Lean-verified).**  Proof route:
`lifted-thompson-t-shift-template-dies-proof`.  This settles property (P) of
`lifted-thompson-t-shift-template-area-is-a-stabilizer-function` (wave 20,
commit `e56d5901da`; that node is not yet in this checkout).

## Setting

The setting is the one of that node and of
`lifted-thompson-t-template-envelope-contains-shift-graphs` (wave 19).
`T̄` is the torsion-free finitely presented lift of Thompson's `T`, with a
fixed finite presentation, maximal relator length `M`, and Dehn area Area.

```text
c = c_I, I = [5/16, 3/8];      h = c_{sK}, K = [3/4, 7/8];
kappa = σ^(-1) h σ             (a fixed word for c_K);
D = C(c) ∩ C(c_K);   H = <c, c_K> ≅ Z^2;
f(d) = min { Area([δ c δ^(-1), kappa]) : δ a word for d }.
```

## Statement

1. **(Quantitative properness.)**  Put `R(A) = (A M + 2|c| + 2|kappa|)/4`.
   Every `d in D` with `f(d) <= A` has the form `d = h_0 g`, with
   `h_0 in H`, `g in D` and `|g| <= R(A)`, and then `d(sI) = g(sI)`.  Hence

   ```text
   #{ d(sI) : d in D, f(d) <= A }  <=  |B_(R(A))|.
   ```

2. **(P) holds.**  `f` is unbounded on every infinite subset of `D` whose
   intervals `d(sI)` are pairwise distinct.
3. **(The Sh_3 template is dead for all words.)**  Fix any vertex `a = (i,j,l)` of
   the Sh_3 template, any choice of free parts of the `t_v`, and any words `u_v`.
   Then at most `|B_(R(A))|` of the out-arcs `a -> (j,l,m)`, `m > l`, satisfy
   `Area([C_b, H_a]) <= A`.  So `sup_b Area([C_b, H_a]) = infinity` at every
   vertex, and the template violates the uniform-area clause (CCC2) of the
   chromatic commutator code criterion.

## What this changes

- The last named hole of the wave-19/20 shift-template lane is closed
  negatively.  Sh_3 was the explicit shift-graph template of wave 19, which
  passes every element-level test.  It was the surviving explicit candidate of
  the conjugate-template class after the wave-18 clique kill.  With it gone,
  the bounded-area chromatic-code lane toward `lifted-thompson-t-is-not-mf` has
  no explicit conjugate candidate left.  (That lane also needs `T` non-hyperlinear, by
  `lifted-thompson-t-chromatic-codes-force-t-nonhyperlinear`.)
- The kill extends beyond Sh_3.  By the star-finiteness corollary of
  `commuting-conjugate-commutator-area-localizes-conjugators`, *every*
  conjugate template on `T̄` (and on `T`, or on any torsion-free finitely
  presented group) is dead if one vertex has out-arcs to infinitely many
  distinct elements `C_b`, or in-arcs from infinitely many distinct `H_a`.
  - The invariant is the number of distinct partner elements in a star.
  - It dies at `(N4)`–`(N6)` of the localization proof.
  - A surviving conjugate template must be *element-locally finite*: each star
    sees finitely many partner elements, with the bound growing with the area
    budget.
- The wave-20 warning that "length alone cannot work" is respected.  The proof
  works modulo `<c, c_K>` from the start, because `H` is exactly the group
  whose ring `Z[H]` absorbs the factor `(1-c)(1-kappa)`.
- `lifted-thompson-t-is-not-mf` stays OPEN.
