# Import Lemma 3.2 and Theorems 1.3 and 4.5 of Kempe--Regev--Toner, Unique Games with Entangled Provers are Easy

*Attempt artifact (2026-09-17), formerly route `unique-games-entangled-value-approximable-by-sdp-citation` into `unique-games-entangled-value-approximable-by-sdp`, requires []. Demoted from the graph together with the other two routes of this result because referee lenses 1 and 2 of three returned *refuted* on `entanglement-sound-soundness-cannot-prove-ugc` (missing outer completeness hypothesis in B3; overclaimed class kill for 2-to-1 soundness); lens 3 returned *survives*. See `## Attempts` in the claim. Restore it as a route once the statements are corrected and a full referee pass survives.*

Literature import, credited in full.

Julia Kempe, Oded Regev, Ben Toner, *Unique Games with Entangled Provers are
Easy*, arXiv:0710.0655 (v3, 3 Oct 2009); FOCS 2008; SIAM J. Comput. 39(7)
(2010). Verified on 2026-09-17 against the arXiv v3 PDF. The text below is
copied from a machine text extraction, so spacing and mathematical symbols are
normalized.

* **Definition (p. 7).** "the entangled value of G can be written as
  omega*(G) = lim_{d -> infinity} max_{|psi> in C^d (x) C^d} max_{A^s_a, B^t_b} ...",
  with "orthogonal projectors" `A^s_a`, `B^t_b` and `sum_a A^s_a = I`.
* **SDP 1 (p. 8).** "Maximize: sum_{abst} pi(s,t) V(a,b|s,t) <u^s_a, v^t_b>
  Subject to: ||z|| = 1; for all s,t, sum_a u^s_a = sum_b v^t_b = z; for all
  s,t, for all a != b, <u^s_a, u^s_b> = 0 and <v^t_a, v^t_b> = 0; for all
  s,t,a,b, <u^s_a, v^t_b> >= 0."
* **Lemma 3.2 (p. 8).** "Let G = G(pi, V) be a (not necessarily unique)
  one-round two-prover game. Then omega*(G) <= omega_sdp1(G)."
* **Theorem 4.5 (p. 13).** "Let G be a unique game. Suppose that
  omega_sdp1(G) = 1 - eps. Then omega*(G) >= 1 - 6 eps."
* **Theorem 1.3 (p. 5).** "There exists an efficient algorithm that, given a
  unique game whose entangled value is 1 - eps, outputs a value
  eps/6 <= eps' <= eps and a description of an entangled strategy for the
  provers whose success probability is at least 1 - 6 eps'."
* **Consequence stated by the authors (p. 5).** "Our result shows that the
  analogue of Conjecture 1.2 for entangled provers is false. Indeed, as long
  as, 6 eps + delta < 1, our algorithm can efficiently tell whether the
  entangled value of a game is at least 1 - eps or at most delta."
* **Form of the rounded strategy (p. 5 and p. 11).** "The main idea in our
  rounding step is to use the vectors given by the SDP solution as a quantum
  measurement performed by the provers on a maximally entangled state shared by
  them." Algorithm 1 (p. 11): "Setup: Alice and Bob share many copies of an
  n-dimensional maximally entangled state ... as well as a sequence
  Lambda = (lambda_1, lambda_2, ...) of real numbers, where the lambda_i are
  independent and each is sampled uniformly from [0, 1]."
* **Integrality gaps are entangled gaps (p. 6).** "Khot and Vishnoi constructed
  for any k >= 1 and eta > 0, a unique game with 2^k/k questions to each prover
  and answer alphabet of size k for which the value of our SDP relaxation is at
  least 1 - 9 eta and whose (non-entangled) value is at most 2/k^eta." Footnote
  2 converts the constraint graph to a two-prover game by choosing a random
  constraint and sending one endpoint to each prover.

**Commuting-operator extension (one line, not in the source).** Let `A^s_a`,
`B^t_b` be projective measurements on one Hilbert space with every `A` commuting
with every `B`, and let `psi` be a unit vector. Put `u^s_a = A^s_a psi`,
`v^t_b = B^t_b psi` and `z = psi`, taking real and imaginary parts as in the
source's proof. Orthogonality and the sum constraints hold because the `A^s_a`
are orthogonal projections summing to `I`. Nonnegativity holds because
`<A psi, B psi> = <psi, A B psi> = <psi, A B A psi> = ||B A psi||^2 >= 0`,
using that `A` and `B` commute and `A^2 = A`. The objective is the strategy's
winning probability. So `omega_qc(G) <= omega_sdp1(G)`.
