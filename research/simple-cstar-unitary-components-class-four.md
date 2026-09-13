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
  - research/artifacts/class-four-lambda-mod-eight-trapping-2026-09-13.md
  - research/artifacts/class-four-lambda-mod-eight-trapping-part2-2026-09-13.md
---

Find a simple unital C*-algebra A and unitaries u_1, u_2, u_3, v in A with
[u_3, [u_2, [u_1, v]]] not in U_0(A).

**Answered (unreviewed), 13 Sep 2026.** The route
class-four-via-lambda-mod-eight-trapping-tower answers it with a simple
unital AH algebra (simple-ah-algebra-with-class-four-component-group). The
trapped class uses a structure only on TX − W_R, namely spin with lambda
trivialized mod 8. That bordism sees eta^3. The tower steps are the
quaternionic Grassmannians Gr_8(H^{8+2d}). The next target is class five,
where rank-two protected blocks with sphere-collapse seeds are blind.

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
  bundle on its 8-cell is divisible by 6. No example is known. *Resolved by
  relaxing*: the locus only needs a structure on the virtual bundle
  TX − W_R, and lambda mod 8 suffices to see eta^3
  (eta-cubed-survives-in-lambda-mod-eight-bordism). On Gr_k(H^{k+2d}) the
  defect is k·q_1 (quaternionic-grassmannian-trapping-defect-is-rank), so
  k = 8 works.
- *Framed trapping.* Needs TX ≅_s (Q* (x)_C H)_R. Then the parity is χ(X) mod 2.
  Gr_2(C^4) and HP^2 fail on p_1.
- *Other U(2) seeds under spin trapping.* Capped. Every element of
  pi_*U(2) is omega o h. Bracketing with alpha composes with eta_3. Bracketing
  with omega composes with nu', which stabilizes to 2 nu. So a depth-three
  bracket of seeds pulled back through sphere collapses has stable image
  eta^a (2 nu)^b · (stable images of the leaves), with a + b = 3. The unit
  S -> MSpin is a ring map, and Omega^Spin_3 = 0 kills both eta^3 and nu.
  Hence every such image is invisible to spin trapping. The same holds for
  [[u_1, v_1], [u_2, v_2]], whose image is 2 nu·eta^2.
- *Larger protected blocks C^k, k >= 3, with alpha-brackets.* Dead by
  bilinearity. <alpha, a_k> = (k−1)!·g in pi_{2k}U(k) ≅ Z/k!. Then
  <alpha, <alpha, a_k>> = (k−1)!·<alpha, g> lies in pi_{2k+1}U(k), which is
  Z/2 or 0, and (k−1)! is even. For k >= 3, brackets <a_i, a_j> have even
  coefficient (i−1)!(j−1)! unless i, j <= 2. Higher brackets such as
  <a_3, <a_2, a_2>> in pi_11 U(3) are unexplored.
- *Non-spherical seed manifolds.* Unexplored. The trapped class of a nested
  commutator on M is read by preimages in Omega^Spin_{m−3}. The
  eta^a (2 nu)^b cap is proved only for commutators that factor through a
  single sphere collapse.
