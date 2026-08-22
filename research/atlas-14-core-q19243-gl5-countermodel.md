---
rg: 2
id: atlas-14-core-q19243-gl5-countermodel
kind: claim
title: The fourteen-word A4 core plus collision 19243 has an exact GL5(2) countermodel
artifacts:
  - experiments/atlas_a4_gl5_core_collision_countermodel.py
  - experiments/atlas_a4_gl5_packet_screen.py
  - research/artifacts/atlas-a4-gl5-core-collision-countermodel.json
distinct_from:
  atlas-a4-gl5-packet-collision-screen: that exhausts the full thirty-word packet in GL5(2) and finds no collision-zero point; this point satisfies exactly the fourteen retained core words and fails all sixteen discarded central-C3 words.
  atlas-three-word-gap-permutation-countermodel: that is a twelve-point local S3 model for only three words; this is a common relative chart frame between two exact regular A8 margins satisfying the entire fourteen-word core.
---

Let `J=diag(GL_4(F2),1)<GL_5(F2)` and put

```text
    [0 0 0 0 1]
    [1 0 0 0 0]
h = [0 0 1 0 0].                                      (A4-GL5-1)
    [0 0 0 1 0]
    [0 1 0 1 0]
```

For the first chart use `j_1(g)=diag(g,1)` and for the second use
`j_2(g)=h j_1(g) h^-1`.  Exact arithmetic over `F2` gives

```text
(j_1(x_e)j_2(y_e))^3 = 1        for all 14 core edges e,
q_19243(j_1,j_2) = 1.                                  (A4-GL5-2)
```

The same point satisfies exactly fourteen of the full thirty packet words:
all sixteen discarded central-`C3` contexts fail.  Thus those contexts are
invisible in the classical automorphism audit but are load-bearing in finite
regular chart models.

Let `lambda` be the left regular representation of `GL_5(F2)` and set
`U=lambda(h)`.  Since

```text
|GL_5(F2)|/|A8| = 9,999,360/20,160 = 496,
```

both `lambda o j_i` restrict to exactly `496 Reg(A8)`.  Every core pair in
`(A4-GL5-2)` generates an `A4`: it has nontrivial generators of orders two
and three satisfying the `(2,3,3)` triangle presentation, so it cannot factor
through either proper nontrivial quotient of `A4`.  Restricting the ambient
regular representation to these subgroups therefore supplies all fourteen
exact regular local `A4` contexts with the same literal relative frame `U`.

This frame is uniformly outside the rank-three commutant.  For example the
certificate records

```text
c=h diag(H6[0],1) h^-1 diag(H6[0],1)^-1 != 1.          (A4-GL5-3)
```

Consequently

```text
||[U,lambda(diag(H6[0],1))]||_2 = sqrt(2).
```

For every operator `V` commuting with the rank-three subgroup
`H=<H_6,K>~=GL_3(2)`, the commutator inequality gives

```text
sqrt(2) <= 2||U-V||_2,
dist_2(U,lambda(H)') >= 1/sqrt(2).                     (A4-GL5-4)
```

External amplification preserves `(A4-GL5-2)` and `(A4-GL5-4)`.  Hence the
fourteen-core-plus-collision system does not force rank-three commutant
collapse, even at zero defect and with exact regular A8 margins.
