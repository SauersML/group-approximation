---
rg: 2
id: regular-table-local-h1-restatement-proof
kind: route
title: Unpack local nonabelian H1 in the asymptotic permutation quotient
target: regular-table-local-h1-restates-spherical-gauge
requires:
  - relation-defects-obey-permutation-gauge-law
---

For a sequence of spherical clouds, quotient the product of their symmetric
groups by permutations supported on `o(N)` points.  Let `L` consist of
classes `[c_n]` for which, for every `a>0`,

```text
|{i: ||x_i-x_(c_n(i))||>a}|/N_n -> 0.                  (RLH1)
```

The triangle inequality and permutation invariance of cardinality show that
`L` is a group.  Tight shadow permutations normalize `L`: after
conjugating by a shadow, the middle displacement is merely relabeled, while
the two shadowing errors vanish in measure.

For the relation defects

```text
delta_(g,h,k)=sigma_k^(-1) sigma_g sigma_h,
```

the local-H1 premise itself asserts that these defects define a class in the
local coefficient system.  Triviality of that local nonabelian torsor class
means precisely
that there is a zero-cochain `[c_s] in L` satisfying, for every tested
cell,

```text
[c_k]=[delta_(g,h,k)
        (sigma_h^(-1)c_g sigma_h)c_h].                 (RLH2)
```

By the exact permutation gauge law, `(RLH2)` is equivalent to

```text
(sigma_g c_g)(sigma_h c_h)=sigma_k c_k
```

modulo `o(N)` roots.  Membership in `L` says exactly that the corrections
are geometrically local off `o(N)` roots.  These are the qualitative
asymptotic clauses of the spherical local-gauge target, and the converse
constructs the same zero-cochain from any such gauges.

Finally, the sequential statement is equivalent to the uniform finite
tolerance statement by diagonalization.  If uniform thresholds fail for
some `eps_0`, choose inputs with errors below `1/n` but no admissible
`eps_0` gauge; these form a counterexample sequence.  Conversely, apply
the uniform theorem at `eps=1/n`.  Thus the local-H1 premise and the
qualitative target are the same assertion, so a route that assumes the
former to prove the latter is circular.
