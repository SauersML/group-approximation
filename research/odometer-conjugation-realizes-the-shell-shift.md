---
rg: 2
id: odometer-conjugation-realizes-the-shell-shift
kind: claim
title: On the integers inside the 2-adic integers the shell shift is conjugation by the odometer, so window-zero witnesses of sign −1 are exactly odometer-stable groups of binary tree automorphisms commensurating N
distinct_from:
  eventually-periodic-genuine-shell-actions-give-fp-envelopes: that constructs window-zero witnesses for virtually abelian inputs by hand; this gives a framework in which the twist is conjugation by the odometer, recovers those witnesses as the automata whose sections lie in the odometer group, and shows that anything beyond virtual abelianness needs sections outside it.
  window-zero-twists-are-fixed-point-free: that is a necessary condition on twists for arbitrary actions; in this framework it holds automatically.
  genuine-action-shell-envelopes-generalize-the-regular-shell: that allows any genuine action with infinite supports; this is a concrete source of such actions, restrictions of 2-adic isometries to N.
artifacts:
  - research/artifacts/gq-bh-bh-shell-kazhdan-rigidity-attempt.md
---

**ESTABLISHED** by `odometer-conjugation-realizes-the-shell-shift-proof` (lane proof, elementary, not independently reviewed, no priority claimed).

## Setting

- `T` is the rooted binary tree, and `Aut(T)` acts on `Z_2` by reading binary digits least significant first.
- `N ⊂ Z_2` is the set of eventually-zero sequences, which is dense.
- `o: x ↦ x + 1` is the odometer, with `o(N) = N \ {0}`.
- `g ∈ Aut(T)` **commensurates `N`** if `gN △ N` is finite. It then induces a near permutation `g|_N ∈ NearSym(N)`, whose index is `|gN \ N| - |N \ gN|`.
- `s: n ↦ n+1` on `N` is the shell shift.

## Statement

1. **The shift is the odometer.** For `g` commensurating `N`, `s (g|_N) s^-1 = (o g o^-1)|_N` in `NearSym(N)`.
2. **Rigidity.** Let `g, h` commensurate `N` and satisfy `g|_N = h|_N` in `NearSym(N)`. Then `g = h`. Every `g != 1` moves infinitely many points of `N`.
3. **The construction criterion.** Suppose:
   - `G ≤ Aut(T)` is finitely generated;
   - every element of `G` commensurates `N` with index `0`;
   - `o G o^-1 ⊆ G`;
   - the near action `g ↦ g|_N` lifts to a homomorphism `rho: G -> Sym(N)`. This holds, for instance, when `G` is free on its given generators.

   Then `rho` is a genuine shell action with infinite supports that passes window zero with sign `−1` and twist `psi(g) = o g o^-1`. Moreover `R_rho = <rho(G), s> ≅ <G, o> ≅ G *_psi`.
4. **Twists are fixed-point free.** No `g != 1` in `G` commutes with `o`. This is the condition of `window-zero-twists-are-fixed-point-free`, and here it is automatic.
5. **Calibration.** Let `sigma` be the root swap. Then `G = <sigma, o sigma o^-1> ≅ D_∞` satisfies item 3, with `o(o sigma o^-1)o^-1 = sigma`. It acts on `N` as `(0 1)(2 3)…` and `(1 2)(3 4)…`, which is the eventually periodic zigzag witness.
6. **Ceiling of the odometer-bounded class.** Suppose each generator of `G` has, at some level, all its sections in `<o>`. Then `G` acts on `N` by eventually periodic near permutations, so `G` is virtually abelian.

## What this gives

A witness of window zero that is not virtually abelian, in this framework, is a finitely generated group of tree automorphisms satisfying:
- it commensurates `N` with index `0`;
- it is stable under conjugation by the odometer;
- it is not virtually abelian, which by item 6 means some generator has sections outside `<o>` at every level;
- its near action on `N` lifts.

The search space is concrete: finite-state automata, with equality decidable. Stability under the odometer can be tested by finding explicit words, or refuted on a finite level of the tree. The route `R_rho ≅ G *_psi` is finitely presented whenever `G` is.

**OPEN:** the existence of such a `G`. No example is known to this lane.

## Lesson for general BH

The window-zero gate of the shell route is a question about self-similar groups.
- Realize the ray `N` inside `Z_2`. The shell shift then becomes conjugation by the odometer, and `R_rho ≅ <G, o>` is a group of tree automorphisms containing the adding machine, with `G` its index-zero part.
- So at window zero the shell route and the self-similar route (Röver–Nekrashevych envelopes, where finite presentation comes from contraction) are the same problem seen from two sides.
- A universal window-zero shell theorem would amount to embedding every input in an odometer-stable group of automata that commensurates the integers.
- A reader looking for finite presentation of `R_rho` should look at contraction of `<G, o>`. This is a heuristic link, not proved here.
