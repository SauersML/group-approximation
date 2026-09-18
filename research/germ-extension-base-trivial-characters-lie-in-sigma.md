---
rg: 2
id: germ-extension-base-trivial-characters-lie-in-sigma
kind: claim
title: In a finite germ extension with finite-index germ groups and infinite base orbits, every character vanishing on the base lies in Sigma^m
distinct_from:
  rover-nekrashevych-higher-sigma-invariants-are-full: that attacks Sigma^m(V_d G) for G of type F_m through the Stein–Farley complex, whose stabilizers are products G^n; this uses the Belk–Hyde–Matucci germ complex, whose stabilizers are virtually point stabilizers in the base group, and needs no finiteness of G.
  graph-braid-ascending-matching-complexes-give-sigma: that is Morse theory for graph braid groups; this is Morse theory on the germ complex of a finite germ extension.
---

**ESTABLISHED (proof in `germ-extension-base-trivial-characters-lie-in-sigma-proof`; unreviewed).**

Let `G` be a finite germ extension of `B <= Homeo(X)` (definition and notation as in
`germ-complex-and-bux-gonzalez-morse-inputs`), and let `m >= 1`. Assume:

1. `B` has finitely many orbits on `sing(G)^{m+1}`;
2. `Fix_B(M)` has type `F_m` for every `M ⊆ sing(G)` with `|M| <= m+1`;
3. `|(G)_p : (B)_p| < ∞` for every `p in sing(G)`;
4. every `B`-orbit in `sing(G)` is infinite.

Then `G` has type `F_m`, and `[χ] in Σ^m(G)` for every nonzero `χ in Hom(G,R)` with `χ(B) = 0`.

**Corollary (Bieri–Renz).** Under 1–4, every `N ⊴ G` with `B ⊆ N` and `G/N` abelian has type `F_m`.

**How it works.** Write `χ` as a sum of *germ charges* `c((Bg)_p)` over the singular points of `g`.

- Hypothesis 3 kills the charge on isotropy groups. So the charge is a coboundary `c(β) = ν(source) − ν(target)` of a
  potential `ν` on `sing(G)` with finitely many values.
- The potential gives a `χ`-equivariant affine height on the germ complex, with `ν` placed on hidden points.
  Generic constants make `ν` nowhere zero and of both signs on some orbit.
- Every ascending link in `K_{<=m+1}` is a join of nonempty discrete sets with a skeleton of an infinite simplex, hence
  `(m-1)`-connected. Hypothesis 4 makes the simplex infinite.
- The Morse Lemma and the Bux–Gonzalez criterion finish.

**Calibration (where hypotheses 3 and 4 fail).** Thompson's `F` is a finite germ extension of `F'` acting on `[0,1]`.
Here `sing(F) = {0,1}` with finite orbits, and `(F)_0 = Z` while `(F')_0 = 1`. The character `χ_0` (log-slope at 0)
vanishes on `F'`, but one of `[±χ_0]` lies outside `Σ^1(F)` (Bieri–Neumann–Strebel; Witzel–Zaremsky Theorem A). Its germ charge at `0` is a nonzero homomorphism on the
isotropy group, so no potential exists.

## Attempts

- Proved; see the proof route. Applied in `rover-nekrashevych-bounded-automata-sigma-invariants-full`.
- Open extension: `χ` nonzero on `B`. There the charge is only defined modulo `χ(B)`. One would need `[χ|_B]` in the
  invariants of the vertex stabilizers `Fix_B(M)`. This is the case needed to pass from `V_d G_i` to `V_d G_{i+1}` in the
  polynomial-activity tower of Belk–Hyde–Matucci (their remark after `thm:RoverNek`).
