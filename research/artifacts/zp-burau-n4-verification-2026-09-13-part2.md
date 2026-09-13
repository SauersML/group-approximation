# Verification of arXiv:2607.05283v1 (Burau representation of B_4), part 2

Continues part 1, which has the source, the skeleton S1–S11, and checks of
S1–S7. This part checks the n = 4 argument (Section 6 of the preprint) and
gives the verdict.

## S8: Lemmas 6.2 and 6.3 — SKETCH, load-bearing, not verified

- **Lemma 6.2.** Claim: for a proper product Phi = Psi.Gamma with Gamma
  simple, each disk of Phi is either a 1-disk {p4}, or its beta-component can
  be isotoped off Gamma.
  - The proof handles the strands pictured in Fig. 6.2: strands of
    beta' = (beta_*^3)Psi that cross Gamma near its base, each pushed once.
  - The remaining disks are slid off Gamma "along the rightmost subarc of
    alpha that appears in the local picture". There is no argument for
    beta-components crossing Gamma elsewhere, or for why the slide keeps the
    component free of interior alpha-crossings.
  - A push homeomorphism preserves iota(beta, Gamma), so (beta')Gamma crosses
    Gamma_1 as often as beta' did. The lemma needs every such crossing to be
    removable disk by disk, which the picture does not show.
- **Lemma 6.3.** The proof is one sentence plus Figs. 6.4–6.5: "up to
  equivalence, there are only finitely many possible beta-subarcs forming an
  alpha-beta disk that is disjoint from Gamma_1".
  - The enumeration into the five arcs delta_1, ..., delta_5 is not justified
    in the text.
  - In Fig. 6.4, Gamma_1 is a thin loop from p4 around p1. An arc with both
    ends on alpha and disjoint from Gamma_1 can cut off a disk whose
    alpha-side meets Gamma_1. The text does not show that such disks only
    give the listed sets.
- **Why it matters.** This is the n = 4-specific input. If it fails, disks
  of types {p1,p3,p4}, {p2,p3,p4} (sign-preserving, odd) or {p3,p4}
  (sign-changing, even) come back, and Proposition 6.4 corrects none of them.

## S9: Proposition 6.4 — GAP (load-bearing)

- **G1 (decisive).** The last paragraph replaces Gamma = gamma_1 ∪ gamma_2 by
  Gamma' = gamma_1 ∪ gamma_2', where gamma_2' = gamma' ∪ gamma'' ∪ gamma_2.
  Here gamma' runs from q to a point r on alpha, and gamma'' is any
  nontrivial loop at r in D_4 \ (beta ∪ gamma_1 ∪ gamma').
  - The preprint says it suffices that gamma_2' satisfies:
    - (1) its first beta-crossing comes after its last alpha-point;
    - (2) iota(alpha, (beta_*^3)Gamma') > iota(alpha, (beta_*^3)Gamma).
  - It then concludes "Since the subarc gamma_2' satisfies the two
    properties above, we have established the result in this case" (Case 1,
    with Case 2 reduced to it).
  - **(a) Property (2) is never proved.** The text shows only that some
    nontrivial loop gamma'' exists. Nothing shows that the fingers of
    beta_*^3 dragged along gamma' ∪ gamma'' add essential intersections with
    alpha instead of isotopically removable ones.
  - **(b) Parity of Gamma' is never re-established.**
    - The parity argument for Gamma used that gamma_2 is disjoint from alpha.
      gamma_2' meets alpha at r.
    - gamma'' is an arbitrary nontrivial loop in a disk with punctures p1,
      p2, p4, so the new alpha–beta disks along it are unconstrained. For
      example, a loop around p1 gives a disk containing p1 alone, which by
      Lemma 6.1 means non-minimal position and can bring cancellations.
    - Corollary 6.5 uses parity of the final loop to identify the sum of
      absolute coefficients of M_{Gamma'} with iota(alpha, (beta_*^3)Gamma').
  - **(c) Property (1) is fine.** It gives (beta)Gamma' = (beta)Gamma, so
    parity and the intersection count for f(Phi).Gamma' carry over.
  - **Consequence.** By the remark in part 1, if Phi is in ker rho_4 then
    "parity of Gamma' and property (2)" cannot both hold. (a) and (b)
    together are the Main Theorem for Phi, and they are asserted, not proved.
- **G2. Parity of Gamma in the first stage is not proved.**
  - "We may further assume without loss of generality that each alpha–gamma_1
    disk is equivalent to one of the five disks shown in Figure 6.5;
    otherwise we could have made a different choice of gamma_1" has no
    justification. gamma_1 is only required to be a simple path from p5 to q
    that avoids beta.
  - "Any alpha–beta disks that result from pushing beta_*^3 along gamma_1
    will also be equivalent to one of the five disks" is not proved. Disks
    straddling the unpushed part of beta_*^3 and a finger are not discussed.
  - The staged "push along gamma_1, then along gamma_2" uses pushes along
    non-closed paths, which are not mapping classes.
  - "As noted above" converts 4-disk copies into 5-disks by pointing back to
    the argument for beta, not for beta_*^3.
  - The exclusion of delta_1 ("delta_i for some i >= 2") is not explained.
- **G3. Routing of gamma_2 is asserted.** The text claims a path gamma_2
  disjoint from alpha that meets beta exactly once in each 4-disk
  beta-component and nowhere else. Fig. 6.6 is one example. There is no
  routing argument for the region between nested 4-disk components.
- **G4. First clause unchecked.** "f(Phi).Gamma is a proper product" is
  never verified for the non-simple loop gamma_2 ∘ gamma_1: neither
  Condition 1 (generalized polygons) nor Condition 2 (Gamma_I, Gamma_F).
  Proposition 5.1 is also stated for elements of K_n, and f(Phi) is not in
  K_5.

## S11: Theorem 6.6 — normalization not proved

- **G5. Proper product from free reduction.** The text says: "if the
  juxtaposition of the two words (yielding the product Phi.Gamma_1) is also a
  freely reduced word with respect to this free basis, then the second
  condition for Phi.Gamma_1 to be a proper product is immediately satisfied."
  - No argument links free reduction in the basis y1, y2, y3 (Fig. 6.9) to
    Condition 2, which concerns how Gamma_I and Gamma_F meet the innermost
    {p4}-disk of beta.
  - "beta-to-alpha trigons can be resolved by an isotopy of beta": one such
    move may create another, and termination is not argued.
- **G6. Intersection with alpha.** "The image of the arc beta_*^3 under a
  pseudo-Anosov map necessarily intersects the arc alpha nontrivially" has no
  proof: one given arc can be carried into the complement of alpha. A fix by
  a further conjugation is plausible but not given. Corollary 6.5 assumes
  iota > 0.
- **Text inconsistency.** Section 6 opens by saying Theorem 6.6 is
  faithfulness on K_4; Theorem 6.6 states Brun_4.

## Verdict: GAP

- **Correct:** the reduction to Brun_4, the Moody criterion, the
  parity-to-no-cancellation lemma, the new proof for n = 3, and the
  bookkeeping of the Section 7 example.
- **Not proved:** the n = 4 argument rests on Lemmas 6.2–6.3, supported by
  figures only, and on Proposition 6.4. Its final step (G1) asserts without
  proof exactly the facts that, for a given Phi, amount to Phi not being in
  ker rho_4.
- **Outcome:** the Main Theorem is NOT verified by this check. No citation
  route is written into `four-strand-burau-representation-is-faithful`, and
  the root stays open.
- **Scope of the check:**
  - one reader;
  - no contact with the authors;
  - no later version as of 2026-09-13;
  - figures read at PDF resolution;
  - Long 1986 (Theorem 2.2), Moody 1991 and Bigelow 1999 not re-read.
- **What would close it:**
  - a written proof of G1(a) and G1(b): a choice of gamma'' whose new
    alpha–beta disks are essential and parity-compatible, or another way to
    force unequal intersection counts while keeping parity;
  - a text proof of the Lemma 6.3 enumeration;
  - the Condition 2 normalization in Theorem 6.6.
- **In Cairn:** the argument after Proposition 6.4 is recorded as the route
  `four-strand-burau-faithful-via-parity-correction`. It requires the open
  claim `brunnian-four-braids-admit-parity-correcting-push`, which is the
  content of Proposition 6.4, Corollary 6.5 and Theorem 6.6.
