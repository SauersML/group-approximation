---
rg: 2
id: two-generator-master-tester-consequences
kind: route
title: Transfer every fixed-host equivalence to the compressed universal group
target: two-generator-fp-torsion-free-master-tester
requires:
  - two-generator-fp-torsion-free-universal-whitehead-container
  - whitehead-universal-finitely-presented-torsion-free-group
  - degree-one-assembly-single-fp-tester-equivalence
  - whitehead-is-degree-one-assembly-cokernel
  - connective-loday-assembly-fixed-fp-torsion-free-tester
  - full-farrell-jones-fixed-fp-torsion-free-tester
  - kaplansky-three-properties-fixed-fp-torsion-free-tester
  - kaplansky-all-fields-reduce-to-finite-fields-on-one-group
  - universal-torsion-free-subgroup-colimit-class-tester
  - classical-bass-fixed-two-generator-testers
---

Use the construction in
[[two-generator-fp-torsion-free-universal-whitehead-container]], denoting by
`U` the original universal host and by `E` its two-generator
compression. We have an embedding `U->E` which injects every connective
Whitehead group, and `E` is torsion-free.

If `Wh(E)=0`, then `Wh(U)=0`, so the original universal Whitehead
theorem gives `Wh(G)=0` for every torsion-free `G`. The converse applies
the global assertion to `E`. Translating ordinary Whitehead vanishing
through the degree-one assembly cokernel gives item 2.

If the connective Loday assembly for `E` is a weak equivalence, its whole
connective Whitehead space is weakly contractible. Higher Whitehead
injectivity makes the corresponding space for `U` weakly contractible, so
the existing fixed-tester theorem gives the global assertion. Again the
converse applies it to the torsion-free group `E`.

Full Farrell--Jones, each fixed-field Kaplansky property, and every class
`C` in item 6 are subgroup-hereditary at the only step needed here:
truth for `E` implies truth for its subgroup `U`. The corresponding
fixed-`U` tester theorem then gives the global statement. Each converse
uses that `E` itself is torsion-free. Finally, finite-field transfer on the
fixed group applies verbatim with `E`, yielding the last equivalence.

The torsion-free half of
[[classical-bass-fixed-two-generator-testers]] uses exactly this compressed
universal Whitehead host `E`: its construction proves that every recursive
torsion-free input embedding into `E` is Frattini. Hence its equivalence
supplies item 7 without replacing `E`. QED

The Full Farrell--Jones statement retains its coefficient-rich,
finite-wreath meaning. The connective Loday statement does not include
negative K-groups, arbitrary coefficient categories, the virtually cyclic
family, L-theory, or finite wreath products.
