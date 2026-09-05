---
rg: 2
id: stw99-l-finite-graph-models-uct-kirchberg-citation
kind: route
title: Import the graph-algebra package and evaluate it on the two models
target: stw99-l-finite-graph-models-are-uct-kirchberg
requires: []
---

**Literature package plus a finite computation.**

*Imported.*  Simplicity and pure infiniteness: Bates--Pask--Raeburn--
Szymanski, section 5 (https://nyjm.albany.edu/j/2000/6-14.pdf) -- both
graphs are finite and row-finite with strictly positive adjacency
matrix, hence cofinal and strongly connected, and every vertex `i`
carries `d_i` plus `u_i` further loops, so every cycle has an exit.
Bootstrap membership: the rank-one case of Kumjian--Pask, Theorem 5.5
(https://nyjm.albany.edu/j/2000/6-1.pdf), or the standard argument that
the gauge crossed product is AF and the dual `Z`-action puts the
stabilisation in the bootstrap class.  K-theory with the vertex and unit
identifications: Drinen--Tomforde, Theorem 3.1
(https://arxiv.org/pdf/math/0103036).

*Computed here* (recorded in the artifact).  `M(u)_{ij} = delta_{ij}+u_j`
gives `(I - M^t)_{ij} = -u_i`, so `I - M^t = -u 1^t`, the cokernel is
`Z^n / Z u` and the kernel is the sum-zero sublattice.  For `u=(1,1,2)`:
`2 e_C - b - [p_2] = (1,1,2) = u` and `-e_C - [p_3] = -u`, and the
determinant of `((1,1,2),(1,1,1),(1,0,0))` is `-1`.  For `u=(1,2)`:
`Z^2/Z(1,2) = Z` via `(x,y) |-> 2x - y`, under which `[p] = 2` and
`[q] = -1`.

NOT VERIFIED AGAINST THE SOURCES IN THIS SESSION; the arithmetic was.
