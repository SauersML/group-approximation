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
   - **Virtually (finite-Hirsch-length solvable)-by-metabelian `A` is impossible, and so is any tree
     splitting over such edge groups (sw-053b, 2026-09-17).** See
     `solvable-by-metabelian-edge-images-collapse-higman-quotients`. If `<a^m,c^m>''` is solvable of
     finite Hirsch length, the metabelian argument still runs. Every commutator error lies in
     `A''` or in a conjugate of `phi(W')`, both of Hirsch length at most `h(A'')`. On a free cyclic
     `Q[T^±1]`-module, `T^e - 1` is injective, so these errors cannot create infinite rank. This
     kills derived-length-3 edge images of infinite Hirsch length whose second derived subgroup has
     finite rank, e.g. the Heisenberg-type central extension of `Z wr Z` with `G''` infinite cyclic.
   - **The one-sided span method is dead above the bottom derived layer (w3-053, 2026-09-18).**
     See `higman-one-sided-span-bound-fails-at-derived-length-three` and
     `higman-b-side-derived-closure-stays-in-bottom-layer`.
     - **Explicit example.** There is a group satisfying the `b`-side relations with `A''' = 1` and a
       free cyclic `Q[X^±,Y^±]`-module `A'/A'' ⊗ Q`. So Step 2 (bound the `gamma`-span of `z` from the
       `b` side) is false at derived length 3.
     - **Universal statement.** In `G_1 = <a,b,c>`, `ncl(F_ac^(k)) ∩ F_ac <= P^(k-1)`, where
       `P = ncl_F(c)`. So the universal `b`-side group with `A^(k) = 1` has free solvable
       `A/A^(k-1)`.
     - **Consequence.** A collapse proof for derived length `>= 3` must bound the bottom layer
       `A^(k-1)/A^(k)` one-sidedly, or couple both sides before bounding `A'/A''`.
     - **The candidate.** `[z, z^alpha]` is not usable as stated, since `b^P` does not normalize
       `<alpha,gamma>`. The `phi`-stable pieces are `u_k = gamma^(alpha^k)`, with
       `u_k^(b^(P^k)) = u_k^2`.
   - **Virtually derived-length-3 `A` of any rank is impossible, and so is any tree splitting over
     such edge groups (w5-053, 2026-09-18).** See `higman-derived-length-three-edge-images-collapse`.
     The two-sided closure does not stay in `P'' ∩ P_d''`. In fact `ncl_H4(F''') = H4`.
     - **The chain.** Take an explicit `w_0 in <alpha,gamma>'''`. Conjugate it by `b`, then
       `gamma^n`, then `d`, then `alpha^n'`, then `b`. Each `b`- or `d`-step replaces letters by powers
       `N_j = 2^(P^j)`.
     - **The result.** A word with exponent sums `(0, Y)`, `Y != 0`. A Fox-type count shows it: the
       `d`-step sends a formal sum `S(u_1)` to `P/P'`, and `N_(j+1) >= N_j^2` prevents cancellation.
     - **Collapse.** The mirror chain gives `(Y, 0)`. Then `<alpha^Y, gamma^Y> <= A'`, which is
       metabelian, and the metabelian theorem applies.
     - **Certification.** `S(u_1) != 0` is certified exactly for `m <= 4` and symbolically for all
       `m >= 2` (`experiments/higman-two-sided-ladder-2026-09-18`).
     - **Consequence.** `H4/<<F'''>>` is trivial, so it offers no amenable edge image.
   - **Virtually solvable `A` of derived length `<= 11` is impossible, and so is any tree splitting
     over such edge groups (w5-053, 2026-09-18).** See
     `higman-bounded-derived-length-edge-images-collapse`, with proof
     `higman-bounded-derived-length-tower-chain-proof`. `ncl_H4(F^(11)) = H4`.
     - **Reduction.** The `k`-step chain `b, gamma^n, d, alpha^n', b, ...` reduces derived length `k`
       to `k - 1`. It needs an order-`(k-2)` tower invariant `S_(k-2)(iota_b(w_0))` to be nonzero for
       some `w_0 in F^(k)`. The invariants are signed counts of letters by nested types, and they
       survive the `h -> N_h` substitution because `N_(h+1) >= N_h^2`.
     - **Certification.** This is done for `k <= 11`: exactly for `m <= 4`, and symbolically in
       `M = 2^P` for `m >= 5` (`experiments/higman-two-sided-ladder-2026-09-18/tower.py`).
     - **Narrowing of the Open item below.** Its solvable survivors now need every finite-index
       subgroup to have derived length `>= 12`, as well as `A_0''` of infinite Hirsch length. Proving
       nonvanishing for all `k` would remove the solvable case entirely.
   - **Every virtually solvable `A` is impossible, and so is any tree splitting of a nontrivial
     quotient over virtually solvable edge groups (w6-053, 2026-09-18).** See
     `higman-virtually-solvable-edge-images-collapse`, with proof
     `higman-virtually-solvable-edge-images-collapse-proof`. `ncl_H4(F^(k)) = H4` for every `k`.
     - **The missing input, proved for all `k`.** Lemmas B and C of the tower chain reduce the
       nonvanishing input to a free-group statement: `S_(k-1)` is not identically zero on
       `<alpha,gamma>^(k)`.
     - **Proof.** On the `r`-th derived term, `S_r` is a Fox derivation over the homomorphism
       `S_(r-1)`. If it vanished on the next derived term it would be inner over the fraction field.
       Conjugation by `x^n` then forces `z = theta(z) + n` for a variable-renaming `theta`, and no
       rational function satisfies that. The explicit witnesses are
       `w_(r+1) = [w_r, x_r w_r x_r^-1]`.
     - **Consequence for the Open item below.** Its solvable survivors are gone. Only amenable `A` that
       are not virtually solvable remain: locally solvable groups of unbounded derived length, other
       elementary amenable groups that are not virtually solvable, and non-elementary-amenable groups.
   - Open (solvable part now closed by w6-053, see above): amenable `A` that is not virtually metabelian and has infinite Hirsch length (e.g.
     derived length at least 3), and non-elementary-amenable `A`. GAP could not decide the
     metabelian-type relators at `2*10^6` cosets. After sw-053b, the solvable survivors are those
     in which every finite-index subgroup `A_0` has `A_0''` of infinite Hirsch length. The two suggested
     routes do not close this case. Route (i) is a Mal'cev/unipotent argument, and it fails because
     `W` and `b^P`-conjugate `W` sit in different nilpotent subgroups. Route (ii) tracks
     `h(W ∩ W^(b^P))`, and it closes exactly when `h(A'') < ∞`. The missing ingredient is an
     element of `A''` with a genuine eigen-shift under `b^P`, analogous to `phi(z) = gamma^(2-2^P)(...)`
     for `z`. A candidate is `[z, z^alpha]`, analysed over `A''/A''' ⊗ Q`.
6. **Amenable quotients.** *Open.* Helfgott--Juschenko: "It is not known whether
   it has amenable quotients" (l.261–262). Item 2 excludes elementary amenable
   ones.
