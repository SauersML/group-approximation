---
rg: 2
id: marked-approximate-radical-survives-solution-group-embedding
kind: claim
title: A marked approximate-radical witness survives Slofstra's fixed-word embedding into a solution group
distinct_from:
  slofstra-solution-group-embedding-preserves-marked-involutions: that is the exact group-theoretic embedding theorem; this adds the elementary normalized-HS restriction argument and consumes an approximate-radical hypothesis already present in the input group.
  perfect-lcs-gap-implies-nonhyperlinear: that obtains the radical property of the solution-group sign from a strict finite-dimensional game-value gap; this transfers a radical property already proved for the embedded source word.
  slofstra-involution-not-sofic-radical: that refutes the radical hypothesis for the particular Higman-based sign in the older Tsirelson-separation construction; this is the conditional transfer theorem explaining what stronger source would have sufficed.
---

**ESTABLISHED.**  Let `G` be finitely presented, let `J' in Z(G)` be a
nontrivial involution, and suppose `J'` is trivial in every normalized-HS
asymptotic representation of `G`.  Apply
`slofstra-solution-group-embedding-preserves-marked-involutions` to obtain

```text
phi:G -> Gamma,              phi(J')=J.
```

Then `J` is nontrivial in `Gamma` and trivial in every normalized-HS
asymptotic representation of `Gamma`.  Hence the finitely presented solution
group `Gamma` is nonhyperlinear.

Proof: `fixed-word-restriction-transfers-approximate-radical-proof`.

This is a compiler, not a source of the missing witness.  Exact
finite-dimensional invisibility of `J'` is insufficient; the hypothesis
quantifies over approximate representations.
