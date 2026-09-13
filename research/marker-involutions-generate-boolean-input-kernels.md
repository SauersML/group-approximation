---
rg: 2
id: marker-involutions-generate-boolean-input-kernels
kind: route
title: Singleton marker cylinders give short involutions whose normal closures are exactly the desired input factors
target: monotone-mf-implications-use-commuting-involution-relators
requires:
  - binary-cylinder-words-have-a-256-quadratic-bound
  - lef-kazhdan-mf-closure-realizes-monotone-boolean-rules
  - mf-closed-normal-joins-have-unbounded-minimal-arity
  - lef-kazhdan-group-has-non-mf-quotient-by-simple-locally-finite
  - subshift-elementary-group-word-problem-degree
artifacts:
  - research/artifacts/pestov91-short-involution-mf-implications-2026-09-13.md
  - research/artifacts/compile-pestov91-mf-implication-words-2026-09-13.py
---

Sections 3--5 show a complete marker code is a singleton cylinder,
so its word is a nontrivial transvection normally generating one
simple edge factor. The product for all occurrences of a variable
normally generates precisely their product: commutators isolate
each noncentral component. Disjoint supports give independent
commuting involutions. The existing Boolean closure theorem now
applies to these single-word input relations. The network has `s+1`
edges and at most `s+1` vertices, giving the stated coding and total
word bounds. Computable Sturmian endpoints and finite marker checks
make the source and its explicit counterquotients' languages, hence
word problems, decidable.
