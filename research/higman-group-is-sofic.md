---
rg: 2
id: higman-group-is-sofic
kind: claim
title: Higman's four-generator group is sofic
root: true
distinct_from:
  higman-group-nonsurjunctive: that asks for an injective non-surjective cellular automaton on Higman's group, which would make it nonsofic; this asks for soficity itself.
  higman-four-cycle-intrinsic-mf-seed: that asks for operator-norm collapse of almost-representations, a matricial-field question; this asks for approximation by permutations in normalized Hamming distance.
artifacts:
  - research/artifacts/solve-higman-sofic-2026-09-13.md
  - research/artifacts/higman-group-gottschalk-host-2026-09-12.md
---

**OPEN.** Is
`H4 = < a, b, c, d | b^a = b^2, c^b = c^2, d^c = d^2, a^d = a^2 >` sofic?

**Why this group.**
- **Candidate nonsofic group.** `H4` has no nontrivial finite quotient, so it
  is not residually finite, and being finitely presented it is not LEF. It
  contains nonabelian free groups, and it is SQ-universal (Helfgott--Juschenko,
  arXiv:1512.02135, l.271–273). Kassabov--Kuperberg--Riley (arXiv:1712.07191)
  call it "a candidate" for a non-sofic group in their abstract.
- **Open at source.** The same paper says soficity of `H_k(BS(1,m))` "remains
  unknown for $m \geq 2$" (l.314).

**Known necessary condition.** Route
`higman-soficity-forces-base-two-exponential-permutations` sends this claim to
`order-four-exponential-permutations-exist-for-base-two`. That target is
equivalent to `H4` having some nontrivial sofic quotient
(`base-two-exponential-permutations-iff-sofic-higman-quotient`).

## Attempts

1. **Permutation reformulation (Helfgott--Juschenko; Kassabov--Kuperberg--Riley).**
   *Open at the base-two case.* The permutations exist for every base `m > 2`
   and are unknown for `m = 2` (l.1281 of the second source). Details and the
   dead sub-routes are in the Attempts of
   `order-four-exponential-permutations-exist-for-base-two`.
2. **Shape of any nontrivial sofic quotient `Q` (solve-higman-sofic,
   2026-09-13).** *Constraints only, no witness.* Such a `Q`:
   - keeps all four `BS(1,2)` subgroups, with every generator of infinite order
     (`nontrivial-higman-quotients-keep-all-four-bs-subgroups`);
   - has `[a,c]` and `[b,d]` macroscopically nontrivial in every approximation
     (`almost-commuting-opposite-higman-generators-force-collapse`);
   - is not LEF, not locally elementary amenable, and not residually elementary
     amenable (`nontrivial-higman-quotients-are-not-locally-elementary-amenable`);
   - has generators of tower-type distortion
     (`nontrivial-higman-quotients-have-tower-distorted-generators`).
3. **Commutator-contractive lengths (Thom, arXiv:1005.0823, Theorem `main`
   l.368–372 and Corollary `corhig` l.395–397 of the TeX).** *Does not reach
   soficity.* `H4` and its quotients do not embed in metric ultraproducts of
   finite groups with commutator-contractive invariant length functions. The
   normalized Hamming length on `Sym(n)` is not commutator-contractive.
4. **Edge-group filter (w5-free-neg-c, 2026-09-12).** *A filter, not a route.*
   `nonsofic-subgroups-of-higman-group-have-free-edge-groups`: a nonsofic
   finitely generated subgroup splits over nonabelian free edge groups in both
   amalgam splittings.
5. **Amalgam over an amenable edge quotient (solve-higman-sofic).** *Open
   sub-question, abelian case dead.*
   - `H4 = G_1 *_(F_ac) G_2` with `G_1 = <a,b,c>`
     (`higman-group-splits-as-amalgams-over-free-subgroups`).
   - Suppose `G_1` has a sofic quotient `G_1'` with `b` of infinite order, in
     which `F_ac` has amenable image `A` and a kernel invariant under `a <-> c`.
     The map `a -> c, b -> d, c -> a` carries `G_1` onto `G_2`. So
     `G_1' *_A (G_1' relabelled)` is a nontrivial quotient of `H4`. It would be
     sofic by permanence of soficity for amalgams over amenable subgroups
     (Elek--Szabo; literature, not re-read).
   - An abelian `A` is impossible: `[a,c] = 1` together with `b^a = b^2` and
     `c^b = c^2` forces `c = 1` (Steps 1–6 of
     `almost-commuting-higman-collapse-proof` with `delta = eta = 0`).
   - **Virtually nilpotent `A`, or virtually solvable `A` of finite Hirsch length, is impossible, and
     so is any tree splitting of a nontrivial quotient over such edge groups (sw-053, 2026-09-17).** See
     `nilpotent-edge-images-collapse-higman-quotients`. One conjugation by `b^(2^K)` scales the
     a-conjugates `c^(a^k)`, `0 <= k <= K`, by pairwise distinct exponents. Their Mal'cev logarithms
     (or derived-series images) are then eigenvectors with distinct eigenvalues, so `K + 1` is at most
     the Hirsch length. A Helly-type tree gate puts an opposite pair into an edge stabilizer of any
     tree action without a global fixed point.
   - **Virtually metabelian `A` of any rank (including `Z wr Z` and the free metabelian group) is
     also impossible, and so is any tree splitting over such edge groups (sw-053, 2026-09-17).** See
     `virtually-metabelian-edge-images-collapse-higman-quotients`. With `alpha = a^m`,
     `gamma = c^m`, `P = 2^m` and `z = [gamma, alpha]`, conjugation by `b^P` sends `z` to
     `gamma^(2-2^P)` times a `gamma`-conjugate combination of `z`. So `z` is torsion under `gamma` on
     `<alpha,gamma>' ⊗ Q`. The `d`-side relations make it torsion under `alpha` too. The commutator
     module is then finite-dimensional, and the finite-Hirsch-length collapse applies.
   - Open: amenable `A` that is not virtually metabelian and has infinite Hirsch length (e.g.
     derived length at least 3), and non-elementary-amenable `A`. GAP could not decide the
     metabelian-type relators at `2*10^6` cosets.
6. **Amenable quotients.** *Open.* Helfgott--Juschenko: "It is not known whether
   it has amenable quotients" (l.261–262). Item 2 excludes elementary amenable
   ones.
