---
rg: 2
id: leavitt-recursive-kernel-idempotents
kind: claim
title: The Leavitt evaluation kernel contains an infinite orthogonal family of idempotents
distinct_from:
  leavitt-evaluation-kernel-hits-augmentation-one: that says the kernel is nonzero and meets augmentation one, with one explicit three-term witness; this says the kernel contains infinitely many pairwise orthogonal idempotents, all but one of augmentation zero, and its witnesses are of a different kind.
  leavitt-corner-kernel-not-jacobson-radical: that is about one idempotent and what its existence refutes about the corner; this is about the whole family and what its size rules out about the shape of the kernel.
  leavitt-primitive-corner-recursive-extension: that is the machine — a corner extension with a compatible embedding of the whole extension into it; this is one consequence of iterating that machine.
artifacts:
  - research/artifacts/leavitt-stable-finiteness-audit-2026-08-17.md
---

Let `S = F_2[G]`, `G = L_(F_2)(1,2)^x`, `K = ker(pi)`.  Read
`lambda(a) = delta_*(a) f` of `leavitt-primitive-corner-recursive-extension`
as an injective nonunital endomorphism of `S`, and put

    q_0 = z = [1] + [g] + [g^2],      q_n = lambda^n(z)   for n >= 1.

Then every `q_n` is a nonzero idempotent lying in `K`, the family is pairwise
orthogonal, and

    eps(q_0) = 1,      eps(q_n) = 0    for every  n >= 1.

Already the primitive-corner kernel `f K f` contains `{q_n : n >= 1}`.

## Why the orthogonality is automatic

`f <= e = 1 + z`, so `z f = f z = 0`.  Every positive iterate lies in `f S f`
and is therefore annihilated by `z` on both sides.  For `i < j`,
multiplicativity of `lambda^i` turns this into

    q_i q_j = lambda^i( z . lambda^(j-i)(z) ) = 0,

and symmetrically on the other side.  Nonzeroness is injectivity of `lambda`,
idempotence is `z^2 = z`, membership in `K` is `rho . lambda = pi`, and the
augmentation values follow from `eps(f) = 0`.

## What it rules out

Any model of the correction ideal as small: not nil, not nilpotent, not
contained in the Jacobson radical, not finitely generated as a set of
orthogonal pieces.  A search or structural attack on
`leavitt-corner-one-sided-lift-exists` should exploit Peirce and corner
decompositions rather than radical perturbation theory, and should not expect
the kernel to be exhausted by finitely many idempotent blocks.

## What it emphatically does not give

**A nonunital corner self-embedding is not direct infiniteness.**  Directly
finite non-Noetherian rings can have proper corner self-embeddings and
infinitely many orthogonal idempotents; the existence of `{q_n}` is no
evidence at all for `leavitt-unit-group-algebra-not-directly-finite`.  The
tempting move — use one of these idempotents as the defect `1 - ab` — fails
because `ba = 1` constrains that defect associatively, and merely being a
nonzero idempotent of the kernel is not enough.

The telescoping correction built from the same family also fails, for the
reason recorded in `leavitt-primitive-corner-recursive-extension`: the tail
`lambda^m(error)` is nonzero at every finite depth and group-algebra elements
have finite support.
