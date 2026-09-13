---
rg: 2
id: rank-two-trapping-blind-to-depth-four-brackets
kind: claim
title: The stable fivefold commutator map U(2)^{∧5} -> SU(2) is null, so no bordism trapping with a rank-two block sees a depth-four bracket
distinct_from:
  rank-two-spin-trapping-blind-to-depth-three-brackets: That kills depth three for the spin detector only; this kills depth four for every detector, through the stable commutator map itself.
  eta-cubed-commutator-has-nonzero-lambda-mod-eight-class: That shows a depth-three bracket is visible to lambda-mod-8 bordism; this shows depth four is invisible to every bordism theory.
---

Let G = U(2). The nested commutator map
c_{j+1}(g_j, ..., g_1, h) = [g_j, [..., [g_1, h]...]]: G^{j+1} -> SU(2) is 1
on the fat wedge, so it factors through a map cbar_{j+1}: G^{∧(j+1)} -> SU(2).

(a) Split Sigma^∞ G ≃ S^1 ∨ S^3 ∨ S^4, using G ≅ S^1 x SU(2) as spaces. Every
    component of Sigma^∞ cbar_{j+1} on a sphere summand of Sigma^∞ G^{∧(j+1)}
    is, up to sign, a product in pi_*^s of at least j letters from {eta, nu}
    (eta^2 counts as two letters).
(b) Hence Sigma^∞ cbar_5 ≃ 0: eta·nu = 0, eta^4 = 0 and nu^4 = 0 in
    pi_12^s = 0, so every product of four letters vanishes. The last nonzero
    component is at depth three, eta^3 on S^1 ∧ S^1 ∧ S^1 ∧ S^3. That is the
    class-four seed of simple-ah-algebra-with-class-four-component-group.
(c) Let h_* be any generalized homology theory, for instance the bordism of
    any tangential structure: Spin, the lambda-mod-8 structure, String, or
    framed. Let M be a closed h-oriented manifold and g_1, ..., g_4, h: M -> G.
    Put f = [g_4, [g_3, [g_2, [g_1, h]]]]. Then the reduced class of f_*[M] in
    h~_m(SU(2)) is zero. So every trapped invariant of the witness
    (f o pr_M) (+) 1_Q vanishes, for every X and Q, e.g. those of
    trapped-spin-bordism-class-over-any-spin-seed-factor and
    trapped-lambda-mod-eight-class-over-seed-factor.

Arbitrary seed manifolds are covered, not only seeds that factor through one
sphere collapse. A bordism-trapped simple example of class five therefore
needs a protected block of rank at least three, a witness not of the form
(f o pr) (+) 1_Q, or a detector that is not a homology theory. The unstable
map cbar_5 itself may be essential. The argument is proved in
rank-two-trapping-depth-four-stable-null-proof. Not independently reviewed.
