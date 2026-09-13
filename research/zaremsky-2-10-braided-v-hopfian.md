---
rg: 2
id: zaremsky-2-10-braided-v-hopfian
kind: claim
title: "Zaremsky Problem 2.10 resolved: is braided V Hopfian, and is every quotient of braided V finitely presented?"
root: true
distinct_from:
  zaremsky-2-09-braided-v-acyclic: that root asks whether braided V has vanishing homology; this root asks about surjective endomorphisms and finite presentability of quotients
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 2, Problem 10, verbatim:
"Is braided V Hopfian? Is every quotient of braided V finitely presented? (This
would imply Hopfian.)"

The same questions are Question 4.7 ("Are F_br and/or V_br Hopfian?") and the
surrounding discussion of arXiv:1403.8132v2, where Zaremsky also proves that the
pure braided kernel `P_br` is not Hopfian (Proposition 4.8).

This claim is the question, and it has two parts:

- (H) `braided-thompson-v-is-hopfian`: every surjective endomorphism of `bV` is
  injective;
- (Q) either `every-quotient-of-braided-v-is-finitely-presented` or its negation
  `some-quotient-of-braided-v-is-not-finitely-presented`.

It is established only through these answer routes:

- `zaremsky-2-10-by-hopfian-and-fp-quotients` requires (H) and the "yes" side of (Q);
- `zaremsky-2-10-by-hopfian-and-non-fp-quotient` requires (H) and the "no" side of (Q).

Never write a `requires: []` route into this claim.
No route is recorded for a non-Hopfian answer: a non-Hopfian `bV` would also answer (Q) negatively.

**Precise reading.** `bV` is the Brin–Dehornoy braided Thompson group `V_br`.
It is finitely presented (Brin 2007, Dehornoy 2006). For a normal subgroup `N`,
`bV/N` is finitely presented iff `N` is the normal closure of finitely many
elements. So (Q) says that `bV` satisfies max-n, the ascending chain condition on
normal subgroups. Max-n implies Hopfian, because the kernels of the iterates of a
surjective endomorphism form an ascending chain.

## Attempts

- 2026-09-13 (z2-10-bv-hopfian): (H) has a complete argument, unreviewed; see
  `braided-thompson-v-is-hopfian` and
  `research/artifacts/zp-braided-v-hopfian-2026-09-13.md`.
  - Zaremsky's Corollary 2.8 forces every surjective endomorphism to preserve `P_br`.
  - `P_br` is residually nilpotent.
  - Each graded quotient `gamma_c/gamma_{c+1}` of `P_br` gives a finitely generated
    representation of `FS^op`, which is noetherian by Sam–Snowden. Hence the kernels
    of the induced graded maps stabilize.
- (Q) is open. The same method gives ACC for normal subgroups containing a fixed
  `gamma_c(P_br)`, but a chain can differ only in unbounded depth.
