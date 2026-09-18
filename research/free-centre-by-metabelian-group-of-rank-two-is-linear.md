---
rg: 2
id: free-centre-by-metabelian-group-of-rank-two-is-linear
kind: claim
title: The free centre-by-metabelian group of rank 2 has a faithful 4x4 representation over Z[x^(±1), y^(±1)]
distinct_from:
  free-centre-by-metabelian-groups-satisfy-boone-higman: that is membership in B_A for every rank r >= 2 and is OPEN; this is linearity of the rank-2 group C_2 only, which gives the rank-2 case of that claim through the characteristic-zero linear node.
  free-centre-by-metabelian-groups-linear-iff-residually-finite: that reduces linearity of C_r for r >= 4 to residual finiteness, using C. K. Gupta's 1973 theorem; this proves linearity of C_2 outright, with an explicit representation.
---

**ESTABLISHED** by `free-centre-by-metabelian-rank-two-linearity-proof` (lane proof,
elementary, not independently reviewed).

**Priority.** No novelty is claimed. C. K. Gupta, "A faithful matrix representation for
certain centre-by-metabelian groups", J. Austral. Math. Soc. 10 (1969) 451–464, and
"The free centre-by-metabelian groups", J. Austral. Math. Soc. 16 (1973) 294–299, give
faithful 3x3 matrix representations in this family (title and abstract read; papers not
read). The representation below was built independently from the Magnus embedding and is
probably a form of Gupta's.

## Statement

Let `F = F(x, y)`, `R = Z[x^(±1), y^(±1)]` and `C_2 = F/[F'', F]`. The assignment

```text
        [1 1 0 0]          [1 0 1 0]
x  ->   [0 x 0 1]    y ->  [0 y 0 0]
        [0 0 x 0]          [0 0 y 1]
        [0 0 0 1]          [0 0 0 1]
```

defines a homomorphism `rho: F -> GL_4(R)` whose kernel is exactly `[F'', F]`. So `C_2`
embeds in `GL_4(Q(x, y))`, a linear group over a field of characteristic zero.

As a by-product, `F''/[F'', F]` is free abelian of countably infinite rank, with basis
the classes of `[e, h e h^(-1)]`, where `e = [x, y]` and `h` runs over lifts of one
representative of each pair `{g, g^(-1)}`, `g ∈ Z^2 \ {0}`.

## Consequences

- `C_2` is residually finite and has solvable word problem.
- `C_2` lies in `B_A` and embeds in a finitely presented simple group
  (`free-centre-by-metabelian-group-of-rank-two-satisfies-pbh`).
