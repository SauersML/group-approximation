---
rg: 2
id: hyperlinear-radical-is-finitely-witnessed
kind: claim
title: Hyperlinear-radical membership in an r.e. presentation is already witnessed by one finite prefix
distinct_from:
  hyperlinear-radical-presentation-compactness: that gives a possibly different finite relator window for every requested error; this proves that one prefix and one cutoff below sqrt(2) already force exact radical membership for the finite-prefix group.
  canonical-profile-word-collapse-one-window: that retains finite canonical-trace side conditions; this is unconditional and identifies a finite-prefix group's full hyperlinear radical.
  word-recursion-cannot-amplify-sublinear-summands: that is a direct-sum naturality obstruction for finite recursive tests; this is an exact compactness theorem for an arbitrary r.e. word-relator library.
---

Let

```text
Gamma=<S|r_1,r_2,...>,
Gamma_N=<S|r_1,...,r_N>
```

with `S` finite and the relator list finite or recursively enumerable. For
every word `w in F(S)`,

```text
w in Rad_hyp(Gamma)
  iff
there is N such that w in Rad_hyp(Gamma_N).             (HRF1)
```

Equivalently, fix any `alpha<sqrt(2)`. The full r.e. library kills `w` in
every tracial matrix ultraproduct if and only if some finite prefix and some
`delta>0` force

```text
||w(U)-I||_2<alpha
```

for every finite-dimensional tuple satisfying that prefix to defect below
`delta`.

Thus an unconditional countable challenge library has no additional
hyperlinear-radical power beyond a finite sublibrary. A failure which moves to
indices `j_n->infinity` is not a third possibility: diagonalization turns it
into a matrix-ultraproduct homomorphism satisfying every standard challenge
and detecting the mark.

In particular, if `w` is nontrivial in `Gamma` and lies in its hyperlinear
radical, the witnessing `Gamma_N` is already a finitely presented
non-hyperlinear group: nontriviality lifts through the quotient
`Gamma_N -> Gamma`. The prefix is generally noncomputable. Effective Higman
is still useful in a reverse-Kleene construction because it computes a named
finite presentation rather than merely proving that some prefix works.
