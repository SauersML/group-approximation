---
rg: 2
id: fp-nonhyperlinear-via-effective-twist
kind: route
title: Apply the relation-centralizing twisted-factor compiler and Higman embedding
target: non-hyperlinear-group
requires:
  - effective-nonce-twisted-factor-exists
  - recursive-twisted-factor-higman-compiler
---

The compiler produces a finitely generated recursively presented
nonhyperlinear group `F/[F,N]`, then embeds it into a finitely presented
nonhyperlinear group.  This supplies the required explicit group from any
effective witness to `effective-nonce-twisted-factor-exists`.

