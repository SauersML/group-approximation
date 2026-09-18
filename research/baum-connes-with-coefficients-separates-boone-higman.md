---
rg: 2
id: baum-connes-with-coefficients-separates-boone-higman
kind: claim
title: Boone–Higman predicts a finitely presented simple counterexample to the Baum–Connes conjecture with coefficients, and fails if every finitely presented simple group satisfies it
requires:
  - decidable-group-with-coarsely-embedded-expanders-exists
  - hereditary-approximation-disproofs-of-boone-higman
  - coarse-embeddability-separates-boone-higman
distinct_from:
  baum-connes-counterexample-group-exists: that asks for a counterexample with trivial coefficients, which is unknown for every group; this is the version with coefficients, which is known to fail for groups coarsely containing expanders, and asks where finitely presented simple groups stand.
  coarse-embeddability-separates-boone-higman: that separator is coarse embeddability into Hilbert space; this one is the Baum–Connes conjecture with coefficients (BCC), which holds for every group coarsely embeddable in Hilbert space only on the injectivity side, so the two classes are not comparable by an inclusion proved here.
---

**ESTABLISHED** (lane proof, three lines; one input is cited and not re-read). No priority claimed.

`BCC` is the class of countable discrete groups satisfying the Baum–Connes conjecture with
coefficients.

1. **`BCC` is closed under subgroups.** This is Chabert–Echterhoff, *Permanence properties of the
   Baum–Connes conjecture* (Doc. Math. 6, 2001): BCC passes to closed subgroups. Cited, **not
   re-read**; this is the trust surface.
2. **(S2) holds.** The finitely generated, decidable group `M` of
   `decidable-group-with-coarsely-embedded-expanders-exists` fails BCC by Osajda arXiv:1406.5015v3,
   Corollary 3.3 (p. 18, read): "it does not satisfy the Baum-Connes conjecture with coefficients".
   Osajda takes this from Higson–Lafforgue–Skandalis [HLS02, Section 7].

**Theorem.** In the sense of `hereditary-approximation-disproofs-of-boone-higman`:
- `BCC` separates Boone–Higman **iff every finitely presented simple group satisfies BCC**;
- if every finitely presented simple group satisfies BCC, `boone-higman-conjecture` is false;
- if `boone-higman-conjecture` holds, some finitely presented simple group (containing `M`, and
  also `M`'s simple Kazhdan decidable host) is a counterexample to BCC.

**Class kill.** No class of BCC groups is a universal Boone–Higman host. This includes a-T-menable
groups (Higson–Kasparov; literature context, not imported), and so again `V`, `V_{n,r}` and cubulated
hosts, consistent with `coarse-embeddability-separates-boone-higman` item 4.

**Why state it separately.** BCC is an analytic property of very different flavor from coarse
embeddability, and its known failures all come from expanders. A proof that finitely presented
simple groups satisfy BCC would refute Boone–Higman. A finitely presented simple BCC counterexample
would be new in K-theory, and Boone–Higman forces one. So this is a test case for Boone–Higman in a
field where it has not been posed.
