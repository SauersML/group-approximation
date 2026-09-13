# Verification of arXiv:2607.05283v1 (Burau representation of B_4), part 1

Lane z3-05-burau-search, 2026-09-13. Problem: Zaremsky 3.5, root
`zaremsky-3-05-four-strand-burau-faithful`. Part 2 has the n = 4 argument,
the gaps and the verdict.

## Source

- arXiv:2607.05283v1. Authors: Vasudha Bharathram, Joan S. Birman, Tara E.
  Brendle. Abstract-page title: "The Burau representation of the braid group
  is faithful for n = 4"; PDF title: "The Burau representation is faithful for
  n = 4". Submitted Mon 6 Jul 2026 16:28:02 UTC. Only v1. 26 pages,
  28 figures, math.GT and math.GR, MSC 57M07, 57M10, 20F65. No journal
  reference, no withdrawal (abstract page read 2026-09-13).
- Read from the arXiv e-print source `Burau4-final.tex` (1031 lines), with
  PDF pages 1–4 and 13–20 viewed for the figures.
- Claims: Main Theorem (the unreduced Burau representation rho_4 of B_4 is
  faithful) and Corollary 1.1 (the Jones representation of B_4 is faithful).

## Logical skeleton (numbering of the preprint)

- S1, Theorem 2.3 (Moody): if M_{Phi.Gamma} != M_Gamma for some Gamma in
  B_n, then Phi is not in ker rho_n. Here M_Psi = M(alpha, (beta_*^3)Psi),
  where alpha is the arc from p1 to p2 and beta_*^3 is the arc from the
  boundary basepoint to p3.
- S2, Observation 2.1: rho_5(f(Phi)) = rho_4(Phi) (+) 1 for the standard
  inclusion f: B_4 -> B_5.
- S3, Proposition 1.2 (via Long 1986, Theorem 2.2): faithful on the Brunnian
  subgroup Brun_4 implies faithful on B_4.
- S4, Lemma 3.1 (a remark of Bigelow 1999, Section 3) and Corollary 3.2. Along
  beta, consecutive exponents satisfy k_{i+1} - k_i = W_i, the signed number
  of marked points in the disk Delta_i.
- S5, Lemma 4.2: the parity condition (a disk is sign-changing iff it
  contains an odd number of marked points) implies that the Moody polynomial
  has no cancellations.
- S6, Proposition 5.1: a proper product Phi.Gamma puts (beta)Gamma in minimal
  position with alpha.
- S7, Lemma 6.1: in B_4, a disk is sign-preserving iff it contains exactly
  one endpoint of alpha, and the sets {p1}, {p2}, {p1,p2} do not occur.
- S8, Lemmas 6.2 and 6.3: for a proper product Phi = Psi.Gamma_1, with Gamma_1
  the simple loop of Fig. 6.3, every disk is of five types, and only the
  4-disk violates parity.
- S9, Proposition 6.4: there is Gamma in K_5 such that f(Phi).Gamma is a
  proper product, both f(Phi).Gamma and Gamma satisfy parity, and
  iota(alpha, (beta_*^3) f(Phi)Gamma) != iota(alpha, (beta_*^3)Gamma).
- S10, Corollary 6.5: then M_{f(Phi).Gamma} != M_Gamma.
- S11, Theorem 6.6: every nontrivial Phi in Brun_4 is conjugate to a proper
  product Phi'.Gamma_1 with iota > 0; S10, S1 and S2 then give Phi not in
  ker rho_4, and S3 finishes.

**Where the content lives.** Suppose Phi is in ker rho_4. By S2,
f(Phi) is in ker rho_5. For every Gamma in B_5 the arcs
(beta_*^3)f(Phi)Gamma and (beta_*^3)Gamma then define the same class in
H_1 of the cyclic cover relative to the lifted basepoint. So their Moody
polynomials agree up to a unit +-t^k. If both arcs satisfy parity, neither
polynomial cancels (S5), so the sum of the absolute values of the
coefficients equals the number of intersection points with alpha, for each
arc. Those counts would be equal. The existence statement S9 therefore
contradicts Phi in ker rho_4 outright, so any gap in S9 is load-bearing.

## Step checks

- **S1: PASS, with one wording fix.** Equal classes give equal pairings for
  fixed lifts. The preprint normalizes by giving the first crossing t^0, so
  the polynomials agree only up to +-t^k, and S1 should say "not equal up to
  units". Corollary 6.5 compares sums of absolute coefficients, which are
  unit-invariant, so nothing downstream breaks.
  - The class used is that of the loop bounding a regular neighbourhood of
    the arc. Its pairing with alpha is (1 - t) times M, up to a unit, and
    Z[t, t^{-1}] is a domain, so equal classes still force M to agree up to a
    unit.
- **S2: PASS.**
- **S3: PASS, modulo the cited centralizer fact.** ker rho_4 and Brun_4 are
  both normal in B_4.
  - If they intersect trivially, [ker, Brun_4] lies in ker ∩ Brun_4 = 1, so
    ker rho_4 centralizes Brun_4.
  - The preprint cites Long 1986, Theorem 2.2, for the faithfulness
    transfer. The needed input is that a nontrivial noncentral normal
    subgroup of B_4 has central centralizer. This lane did not re-read Long.
  - Brun_4 is nontrivial (Fig. 1.1). It is not central, because Delta^2 is
    not Brunnian: forgetting a strand gives Delta_3^2 != 1.
  - The reduced Burau image of Delta^2 is t^4 I, so rho_4 is injective on the
    center. Hence ker rho_4 = 1.
  - Lane z3-05-burau-theory has since proved the cited centralizer fact and
    the reduction independently: `burau-faithful-iff-faithful-on-noncentral-normal-subgroup`
    and `burau-four-faithful-iff-faithful-on-brunnian-braids`, both
    established.
- **S4: PASS** (standard). Checked on the Section 7 example below.
- **S5: PASS, with a typo.** The proof writes "|P(Delta_i)| + ... +
  |P(Delta_{j-1})| = 0" where the signed sum W_i + ... + W_{j-1} = 0 is
  meant. That sum is even, so an even number of odd disks lies between, and
  parity gives epsilon_i = epsilon_j.
- **Theorem 4.1, new proof of Magnus–Peluso (n = 3): PASS.**
  - In B_3, the n = 3 analogue of S7 leaves the sets {p3} (changing),
    {p1,p3} and {p2,p3} (preserving), and {p1,p2,p3} (changing).
  - All of these satisfy parity. So there are no cancellations, and M != 0
    whenever iota > 0.
  - Moody's one-direction criterion (Theorem 2.2, not re-read) then gives
    faithfulness.
- **S6, Proposition 5.1: SKETCH, not fully checked.**
  - The case analysis on the vertices of a new bigon (original vs new
    intersection points) runs through Figs. 5.6–5.10, and each case ends by
    naming a forbidden polygon.
  - Plausible. It is used only for minimal-position statements.
  - As stated it applies to Phi in K_n, while Proposition 6.4 applies it to
    f(Phi), which is not in K_5.
- **S7, Lemma 6.1: main claim PASS; exclusion compressed.**
  - Main claim: at an alpha–beta corner of the disk boundary, the interior
    angle is reflex exactly when the adjacent end of alpha lies inside the
    disk. So sign-preserving corresponds to exactly one endpoint inside.
  - Exclusion of {p1}, {p2}, {p1,p2}: when beta[p_*, q) enters Delta through
    alpha[q, q'], the text says this "contradicts minimal position" without
    exhibiting the bigon. An innermost-region argument likely supplies one,
    but it is not written.

## Section 7 example: bookkeeping check

- Unsimplified M_Phi has exponents 0, 2, 4, 3, 1, -3, -1, 1 and signs
  + + + - - + + +. So W = 2, 2, -1, -2, -4, 2, 2. The only parity violation
  is the -4 step, a sign change across an even count (the 4-disk). The
  cancellation is the pair -t, +t. This matches the text.
- After Gamma: exponents 0, 2, 4, 3, 1, -4, -2, 0, so W = 2, 2, -1, -2, -5,
  2, 2. Parity holds.
  - The text says the last three exponents "increase by 1". They decrease by
    1 (cosmetic).
- M_Gamma = 2t^{-3} - 3t^{-2} + 4t^{-1} - 5 + 3t - 2t^2 + t^3. The sum of
  absolute coefficients is 20, the number of listed terms, so there are no
  cancellations. Correct.
- The example arc does not come from K_4, as the preprint says. It tests
  bookkeeping only, not Lemma 6.3 or Proposition 6.4.
