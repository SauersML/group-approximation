---
rg: 2
id: natarajan-vidick-games-pcp-amplification-error
kind: claim
title: The Pauli energy test measures against the Pauli 1-norm, which tensor-power amplification inflates, so the Natarajan--Vidick games PCP for QMA fails
invalidates:
  - games-qpcp-from-tensor-power-amplified-xx-zz
artifacts:
  - research/artifacts/qpcp-landscape-sources-2026-09-12.md
  - research/artifacts/pauli-frustration-stabilizer-rounding-2026-09-12.md
distinct_from:
  quantum-games-pcp-for-qma: that is the open games conjecture; this is the recorded error in one claimed proof, together with the corrected amplification lemma.
  bmvz-iterable-tensor-gap-amplification: that amplifies ground energy of layered projection Hamiltonians at a locality cost; this concerns the Pauli 1-norm growth of the tensor power `2((I+H)/2)^(tensor k) - I`, which is what games protocols pay.
---

**ESTABLISHED BY CITATION** (Natarajan--Nirkhe, arXiv:2403.13084v1, Section 4).

1. **(NN1) Energy test.** For `H = sum_P beta_P P`, sampling `P` with probability
   `|beta_P|/sum|beta_P|`, measuring `P` and accepting iff the outcome is
   `sign(beta_P)` accepts with probability `1/2 + <psi|H|psi>/(2||H||_(P,1))`
   (eq. (2e)). All known constructions of nonlocal games from local Hamiltonians
   (Fitzsimons--Vidick; Natarajan--Vidick) use this test, so the game promise gap
   is at least the Hamiltonian gap divided by `max ||H||_(P,1)` (eq. (3)).
2. **(NN2) Inflation.** `||(X+Z)/sqrt2|| = 1` but its Pauli 1-norm is `sqrt2`, and
   tensor powers give `sqrt2^n` (Remark 5).
3. **(NN3) Corrected amplification, Lemma 6.** For `-I <= H <= I` with promise
   `lambda_max(H) >= 1-1/p` or `<= 1-1/q`, the operator
   `H' = 2((I+H)/2)^(tensor k) - I` (eq. (9)) is `ell k`-local, `-I <= H' <= I`,
   `lambda_max(H') >= 1-k/p` or `<= 2e^(-k/(2q)) - 1` (eq. (6)), and
   `||H'||_(P,1) <= 1 + 2((1+||H||_(P,1))/2)^k` (eq. (7)).
4. **(NN4) The error.** Natarajan--Vidick (arXiv:1801.03821) amplified QMA-hard
   XX+ZZ Hamiltonians by tensor product and miscalculated the Pauli 1-norm growth.
   They concluded a constant game gap that the test does not deliver. The note
   also records that the earlier plane-vs-point low-degree soundness result they
   used had a bug. It states that it is now open whether QMA is in
   `MIP*[q=O(log n), a=O(log n)]` with efficient provers even if that result is
   recovered.

The note's first open problem asks for a QMA-complete family with bounded Pauli
1-norm to which Lemma 6 applies. The weight-one inputs with `p/q > 2+sqrt2` are in
NP by `pauli-norm-games-qpcp-needs-imperfect-completeness`.
