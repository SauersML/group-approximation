---
rg: 2
id: rank-two-trapping-depth-four-stable-null-proof
kind: route
title: Each bracket multiplies stable components by a letter of degree one to three, and four letters in eta and nu vanish
target: rank-two-trapping-blind-to-depth-four-brackets
requires: []
---

Write s_j = Sigma^∞ cbar_j: Sigma^∞ G^{∧j} -> Sigma^∞ SU(2) = S^3, and fix the
splitting Sigma^∞ G ≃ S^1 ∨ S^3 ∨ S^4 induced by the homeomorphism
S^1 x SU(2) -> G, (z, g) -> diag(z, 1)·g. Smash products of sphere summands
give the sphere summands of Sigma^∞ G^{∧j}.

**Stems used.** pi_{-1}^s = 0, pi_1^s = Z/2{eta}, pi_2^s = Z/2{eta^2},
pi_3^s = Z/24{nu}, pi_4^s = pi_5^s = 0, pi_12^s = 0. The composition product
on pi_*^s agrees with the smash product up to sign, and it is graded
commutative. Hence eta·nu in pi_4^s is 0, eta^4 in pi_4^s is 0, and
nu^4 in pi_12^s is 0.

**Base case j = 2.** The component of s_2 on S^{d_1} ∧ S^{d_0}, with
d_0, d_1 in {1, 3, 4}, lies in pi^s_{d_1+d_0-3}. For (1,1) this is
pi_{-1}^s = 0. For (1,3) and (3,1) it lies in pi_1^s, for (1,4) and (4,1) in
pi_2^s, and for (3,3) in pi_3^s. For (3,4), (4,3) and (4,4) the groups are
pi_4^s = pi_5^s = 0. Every nonzero component is therefore eta, eta^2 or a
multiple of nu: it has at least one letter.

**Inductive step.** Since cbar_{j+1} = cbar_2 o (1 ∧ cbar_j), where cbar_j
lands in SU(2) ⊂ G, we get s_{j+1} = s_2 o (1 ∧ s_j). Here 1 ∧ s_j maps the
summand S^d ∧ C of Sigma^∞(G ∧ G^{∧j}) to S^d ∧ S^3 = S^{d+3}, for each
d in {1, 3, 4} and each sphere summand C of Sigma^∞ G^{∧j}. The restriction
of s_2 to S^d ∧ S^3 is a stem x_d in pi_d^s. That is eta or 0 for d = 1, a
multiple of nu for d = 3, and 0 for d = 4. So the component of s_{j+1} on
S^d ∧ C is ± x_d·(component of s_j on C). By induction every component of
s_{j+1} is ± x_{d_j} ··· x_{d_2}·y with each x of one letter and y a
component of s_2. So it has at least j letters. This is (a).

**Vanishing.** For j + 1 = 5 each component has at least four letters. If
both eta and nu occur, it contains eta·nu = 0. Otherwise it is a power
eta^n with n >= 4, or ± (multiple of nu^4). Both vanish. So every component
of s_5 is 0, and s_5 ≃ 0, because a map out of a finite wedge of spheres is
determined by its components. This is (b).

**Detection.** Let f = c_5 o (g_4, g_3, g_2, g_1, h) = cbar_5 o q o g', where
g' = (g_4, ..., h): M -> G^5 and q: G^5 -> G^{∧5} is the quotient. On reduced
homology, (cbar_5)_*: h~_*(G^{∧5}) -> h~_*(SU(2)) depends only on s_5, so it
is zero. The reduced part of f_*[M] is (cbar_5)_* applied to the reduced
part of (q o g')_*[M], so it vanishes. Toms's trapped class, and its
seed-factor generalizations, take the value
<Euler number>·(f_*[M] − (const)_*[M]). This difference is exactly the
reduced part. So it vanishes. This is (c).

The same count reproduces the known cases: depth one (eta, Toms),
depth two (eta^2, the class-three tower) and depth three (eta^3, the
class-four tower). □
