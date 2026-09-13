---
rg: 2
id: spin-trapping-blind-to-fourfold-commutators-in-every-rank
kind: claim
title: Spin bordism kills every fourfold commutator of unitary-valued maps, in every rank N, so spin trapping never reaches class four
distinct_from:
  rank-two-spin-trapping-blind-to-depth-three-brackets: That is the rank-two case, proved through KO-characteristic numbers; this covers every rank N through the 2-local splitting of MSpin into ko-modules, with no detection by numbers needed.
  nested-commutators-pull-ko-of-unitary-groups-into-eta-powers: That shows KO- and Stiefel–Whitney numbers of fourfold commutators vanish in every rank, and leaves bordism blindness for N >= 3 open; this closes it for spin bordism.
---

Let N >= 1, G = U(N), and let c_4: G^4 -> G be the fourfold nested commutator
(g_3, g_2, g_1, h) -> [g_3, [g_2, [g_1, h]]]. It is 1 on the fat wedge, so it
factors through cbar_4: G^{∧4} -> G.

(a) For every ko-module spectrum E, the map E ∧ Sigma^∞ cbar_4 is null. More
    precisely, E ∧ Sigma^∞ cbar_j = eta^{j-1}·L_j for some map L_j, and
    eta^3 acts as zero on ko-modules.
(b) MSpin ∧ Sigma^∞ cbar_4 induces zero on homotopy. So for every closed
    spin manifold M and all maps g_1, g_2, g_3, h: M -> U(N), the fourfold
    commutator f = [g_3, [g_2, [g_1, h]]] has [M, f]_red = 0 in
    Omega~^Spin_{dim M}(U(N)).
(c) Consequently the rank-N spin detector of the transfer theorem
    (unitary-word-transfer-to-simple-ah-via-trapping with m = 1) is zero on
    every fourfold commutator witness (f o pr_M) (+) 1_Q. Spin trapping can
    certify class three (Toms's tower over T^2 x S^3), but never class four,
    whatever the protected rank and the seed manifold.

A fourfold commutator therefore needs a structure whose bordism is not a sum
of ko-modules, such as the lambda-mod-8 structure of
class-four-via-lambda-mod-eight-trapping-tower, which sees nu. The same
argument shows that any complex-oriented detector with torsion-free
coefficients, e.g. MSpin at odd primes, MU or BP, is already blind to
twofold commutators.

Inputs used as standard and recalled, with theorem numbers not re-verified
in this lane: the Anderson–Brown–Peterson 2-local splitting of MSpin into a
wedge of connective covers of Sigma^{8k} ko and suspensions of HZ/2 (Ann. of
Math. 86, 1967); Wood's equivalence ko ∧ C(eta) ≃ ku; and the odd-primary
splitting of MSO into suspensions of BP. Proof:
spin-trapping-fourfold-blind-every-rank-proof. Not independently reviewed.
