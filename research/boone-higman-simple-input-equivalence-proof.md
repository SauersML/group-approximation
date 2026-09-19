---
rg: 2
id: boone-higman-simple-input-equivalence-proof
kind: route
title: Normalize every Boone-Higman input to an infinite computably presented simple group
target: boone-higman-iff-infinite-simple-inputs
requires: [boone-higman-thompson-simple-envelope]
---

Write `BH` for statement 1 and `SI` for statement 2.

`BH => SI`. Let

```text
S = <X | R>
```

be infinite, finitely generated, computably presented and simple, with `X`
finite and `R` recursively enumerable. Its word problem is decidable by two
parallel searches.

For a word `w`, first enumerate formal consequences of `R` until finding a
proof that `w=1`. In parallel, enumerate formal consequences of
`R union {w=1}` until finding, for every `x in X`, a proof that `x=1`.

If `w=1` in `S`, the first search terminates. The second cannot terminate,
because then every generator of the nontrivial group `S` would be trivial.
If `w!=1`, simplicity gives

```text
<<w>>_S = S,
```

so `S/<<w>>_S` is trivial and the second search terminates. Exactly one
search therefore terminates, deciding whether `w=1`. Applying `BH` to
`S` gives a finitely presented simple overgroup. Hence `SI`.

`SI => BH`. Let `G` be finitely generated with solvable word problem.
Then `G times Z` is finitely generated with solvable word problem.
Thompson's theorem, recorded as
[[boone-higman-thompson-simple-envelope]], gives an embedding

```text
G times Z <= S
```

where `S` is finitely generated, computably presented and simple. Since
`S` contains an infinite cyclic subgroup, `S` is infinite. Apply `SI` to
obtain

```text
S <= H
```

with `H` finitely presented and simple. Composing embeddings gives
`G <= H`, which is `BH`.

For the final counterexample normal form, Higman's embedding theorem places
every finitely generated computably presented `S` inside some finitely
presented group. If the `S` constructed above embedded in any finitely
presented simple group, then so would the original `G`; hence a failed input
produces a failed infinite simple input. QED
