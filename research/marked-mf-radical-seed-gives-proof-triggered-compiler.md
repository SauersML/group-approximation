---
rg: 2
id: marked-mf-radical-seed-gives-proof-triggered-compiler
kind: claim
title: A marked MF-radical seed gives a halting-sensitive proof-triggered compiler
artifacts:
  - research/artifacts/seeded-self-aware-mf-switch-2026-08-23.md
distinct_from:
  authenticated-opnorm-challenge-compiler: that node asked for a CPU support-profile implementation; this gives the compiler semantics directly from one already known marked MF-radical seed.
  threshold-free-reverse-kleene-mf-higman: that consumes an arbitrary compiler and takes a fixed point; this constructs a concrete compiler from a marked seed.
  post-candidate-nemesis-has-a-finality-dilemma: that rules out changing a presentation after accepting a matrix tuple; this switch reacts only to machine halting and the fixed point searches proofs, never matrix tuples.
---

Let `H=<A|Q>` be finitely presented and let the image of a word `z` satisfy

```text
z!=1,
z in Res_MF(H).
```

There is a total computable map from every Turing-machine index `e` to a
finite alphabet, a uniformly recursively enumerable group presentation
`Gamma_e`, and one marked word `w_e`, with

```text
e halts     => w_e!=1 in Gamma_e,
e nonhalts  => w_e lies in Res_MF(Gamma_e).
```

The compiler adjoins one fresh generator `s`, emits the relators of `H`, and
emits `s=1` exactly if `e` halts. Thus the halting branch is `H`, while the
nonhalting branch is `H*Z`. Free-factor injectivity preserves nontriviality,
and MF-radical functoriality carries `z` into the nonhalting branch.
