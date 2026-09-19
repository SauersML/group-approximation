---
rg: 2
id: lifted-thompson-t-exact-wandering-commutator-table
kind: claim
title: "T-bar carries an exact complete-graph commutator table with a non-central mark, built from wandering copies of F under x0; its literal shift templates have relator area growing linearly in the shift, so bounded area needs non-literal words"
distinct_from:
  central-marks-escape-chromatic-codes: that says the mark of any commutator code in T-bar cannot be central; this builds an exact table with a non-central mark and measures the area of its literal words.
  v-cone-sliding-localizes-disjoint-support-relations: that derives disjoint-support commutations in V from bounded-diameter relations with no uniform area bound; this is the specific wandering family in F inside T-bar together with an area lower bound for shift templates.
  lifted-thompson-t-bounded-area-chromatic-code: that is the open bounded-area hole; this is its exact skeleton and an obstruction for one class of words.
---

**ESTABLISHED** by `lifted-thompson-t-exact-wandering-commutator-table-proof`.

**Setting.**  Embed `F` in `T̄` as the lifts that fix `Z` pointwise.  Let
`x0` be the usual generator:

```text
x0(t) = t/2     on [0, 1/2]
x0(t) = t - 1/4 on [1/2, 3/4]
x0(t) = 2t - 1  on [3/4, 1]
```

Put `J = [1/4, 1/2] = [x0(1/2), 1/2]`.  Choose `c0, h0 in F` supported in `J`
with `y = [c0, h0] != 1`, and set

```text
c_n = x0^n c0 x0^(-n),   h_n = x0^n h0 x0^(-n),   a_n = x0^n      (n in Z).
```

**Statement.**

1. **(Exact table.)**  In `T̄`:

   ```text
   [c_n, h_n] = a_n y a_n^(-1),
   [c_m, h_n] = 1   for m != n.
   ```

   So `(c_n, h_n, a_n)` satisfies CCC1 and CCC2 of
   `infinite-chromatic-commutator-code-kills-mf-mark` exactly, on the
   complete graph `K_Z`, whose chromatic number is infinite.  The mark `y` is
   non-central: it fixes `0`, while every `z^k` with `k != 0` acts freely.
2. **(Bridge lower bound.)**  Let `<S | R>` be any finite presentation of any
   group, and let `P` be the maximal relator length.  Let `s` be a letter of
   `S`, and let `c0, h0` be words neither of which represents an element of
   `<s>`.  Then for every `k != 0`,

   ```text
   Area_R([c0, s^k h0 s^(-k)]) >= (4|k| - 2(|c0| + |h0|)) / P.
   ```

   The area of `[s^m c0 s^(-m), s^n h0 s^(-n)]` is the case `k = n - m`,
   since the two words are cyclic conjugates.
3. **(Literal templates die.)**  Take any finite presentation of `T̄` having
   `x0` as a letter, and let `c0, h0` be fixed words.  In `T̄`, `c0` and `h0`
   do not lie in `<x0>`.  On every subgraph of `K_Z` with infinite chromatic
   number, the literal words `x0^n c0 x0^(-n)` and `x0^n h0 x0^(-n)` have
   unbounded CCC2 area.  Two facts give this:
   - such a subgraph has edges `mn` with `|m - n|` unbounded, because a graph
     on `Z` whose edges all have length at most `L` is properly coloured by
     `n mod (L+1)`;
   - item 2 then makes the area grow with `|m - n|`.

   The diagonal area CCC1 of the literal words is `0`.

**What stays open.**  Bounded area for some other choice of words
representing `c_n` and `h_n` (or any other table) is the open leaf
`lifted-thompson-t-bounded-area-chromatic-code`.

Item 2 does not transfer to non-letter templates.  Rewriting `s` as a letter
is a Tietze move, and it changes the area of the length-`4k` word by up to
order `k`.

Area bounded in `F`'s own presentation would make `F` non-MF (by the CCC),
hence non-amenable, since amenable groups are MF.  So the table is expected
to need genuine `T̄` relators.

DERIVATION
lifted-thompson-t-exact-wandering-commutator-table-proof
