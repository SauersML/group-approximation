---
rg: 2
id: simple-cstar-unitary-components-class-four
kind: claim
title: Some simple unital C*-algebra has a unitary component group with a nonzero fourfold commutator
distinct_from:
  simple-cstar-unitary-components-class-three: That asks for a nonzero triple commutator and is answered by spin trapping over T^2 x S^3; this asks for a nonzero fourfold commutator, where the natural seed eta cubed is invisible to spin bordism.
  u2-quadruple-samelson-class-four-stage: That is the nonsimple finite stage C(T^3 x S^3, M_2) of class exactly four; this asks for class at least four in a simple algebra.
artifacts:
  - research/artifacts/class-four-stage-and-blind-spin-trapping-2026-09-12.md
  - research/artifacts/component-group-class-bound-by-excess-2026-09-12.md
---

**OPEN.** Find a simple unital C*-algebra A and unitaries u_1, u_2, u_3, v in
A with [u_3, [u_2, [u_1, v]]] not in U_0(A).

A positive answer, iterated, points toward simple algebras whose component
groups are not nilpotent. Any AH example needs blocks of excess at least two
cofinally (block-component-group-class-at-most-excess-plus-two).

## Attempts

- *Spin trapping over T^3 x S^3.* The detector is blind. The seed is
  eta^3 = 12 nu (u2-quadruple-samelson-class-four-stage), and its trapped class
  lies in Omega^Spin_3 = 0 for every choice of X and Q. With rank-two protected
  blocks, spin trapping reaches eta^2 but not eta^3. Silence proves nothing
  either way about U_0.
- *String trapping.* Live but constrained. MString_3 = Z/24 sees eta^3.
  It needs string X^{4r}, complex Q of rank r with p_1(Q_R) = 0, an odd
  number <c_r(Q)^2, [X]>, and a Grassmannian-type recursion. By the Wu
  formula the parity is <v_{2r}(X) c_r(Q), [X]>. For string X this kills
  r = 2 (v_4 = 0). The Cayley plane fails at r = 4, because c_4 of a complex
  bundle on its 8-cell is divisible by 6. No example is known.
- *Framed trapping.* Needs TX ≅_s (Q* (x)_C H)_R. Then the parity is χ(X) mod 2.
  Gr_2(C^4) and HP^2 fail on p_1.
- *Larger protected blocks C^k, k >= 3.* Unexplored. The spin-bordism images
  of unstable classes in pi_*U(k) can involve cells of SU(k) above the bottom
  one, so the depth cap for rank two need not apply.
