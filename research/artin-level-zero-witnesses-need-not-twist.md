---
rg: 2
id: artin-level-zero-witnesses-need-not-twist
kind: claim
title: "A representation proving that the level-0 dead-cut Laplacian is not onto can have twisted Alexander rank zero: an explicit 2-dimensional witness for the (2,3,2,4) dead join"
distinct_from:
  artin-2x2-dead-joins-sigma1-iff-k-q-odd-family: that decides Sigma^1 on the 2x2 dead joins by building twisted witnesses; this shows that for halves (2,q,2,p) the natural level-0 witnesses are not twisted witnesses, so the passage from level 0 to the Novikov level cannot be made witness by witness
  artin-sigma1-dead-edge-ring-obstruction: that certifies non-membership by rings in which all dead-edge sums vanish; the witnesses here kill only two of the four sums, and they certify only that the level-0 ideal is proper
artifacts:
  - experiments/artin-level-descent-census-2026-09-17/verify_example.py
  - experiments/artin-level-descent-census-2026-09-17/verify_example.log
  - experiments/artin-level-descent-census-2026-09-17/enum2.py
  - experiments/artin-level-descent-census-2026-09-17/calib2.py
  - experiments/artin-level-descent-census-2026-09-17/calib2.log
  - experiments/artin-level-descent-census-2026-09-17/char0_witness.py
  - experiments/artin-level-descent-census-2026-09-17/verify_perm.py
  - experiments/artin-level-descent-census-2026-09-17/verify_perm.log
  - experiments/artin-level-descent-census-2026-09-17/verify_candidate2.py
  - experiments/artin-level-descent-census-2026-09-17/verify_candidate2.log
  - experiments/artin-level-descent-census-2026-09-17/census2.py
  - experiments/artin-level-descent-census-2026-09-17/perm_search.py
---

**ESTABLISHED** by `artin-level-zero-witnesses-need-not-twist-proof` (unreviewed).

**Setting.** Let `G` be the 2x2 dead join with halves `(h_ac, h_bc, h_be, h_ae)`:
- the complete graph on `a, b, c, e`;
- `l(ab) = l(ce) = 2`, and `l(xy) = 2 h_xy` on the four cross edges;
- `χ = (1, 1, -1, -1)` and `H = ker χ`.

The two blocks are `{a, b}` and `{c, e}`. Every cross edge `ρ = pq` (`p ∈ {a, b}`) is dead. Put
`σ_ρ = S_k(pq) = 1 + pq + ... + (pq)^(k-1)` with `k = h_pq`, and `g_ρ = σ_ρ (p - 1)`.

The dead-cut criterion of the Artin Σ^1 lane (artin-sigma1-equals-dead-cut-laplacian-surjectivity)
reduces here to two left ideals:
- level 0: `J_0 = Σ_ρ Z[H] σ_ρ` in `Z[H]`;
- Novikov: `J = Σ_ρ N_χ g_ρ` in `N_χ`.

The known facts are `J = N_χ ⟺ [χ] ∈ Σ^1`, and `J_0 = Z[H] ⟹ J = N_χ`. The corrected conjecture
(artin-sigma1-is-level-zero-laplacian-surjectivity) asks for the converse.

For a representation `π : G -> GL_n(F)`, put:
- `c0(π)`, the dimension of the common kernel `∩_ρ ker π(σ_ρ)` in `F^n`;
- `ct(π)`, the dimension of `∩_ρ ker π(σ_ρ)(s π(p_ρ) - 1)` in `F(s)^n`.

Then:
- `c0(π) > 0` proves `J_0 ≠ Z[H]`, by applying `π` to `Σ λ_ρ σ_ρ = 1`;
- `ct(π) > 0` proves `[χ] ∉ Σ^1`, because `g ↦ s^(χ(g)) π(g)` extends to a ring map
  `N_χ -> M_n(F((s)))`.

Call `π` a *descending witness* if `c0(π) > 0` and `ct(π) > 0`.

**Claim.**
1. **(General inequality.)** For every representation `π`, `ct(π) <= c0(π)`.
   - `c0` is the corank at `s = 0` of the polynomial matrix `M_π(s)`, the stack of the
     `π(σ_ρ)(s π(p_ρ) - 1)`. `ct` is its generic corank.
   - A witness descends iff `ct(π) > 0`.
   - `ct(π) = c0(π)` exactly when the corank of `M_π` does not jump at `s = 0`.
   - A non-descending witness is therefore one whose whole corank at `0` is a jump.
2. **(Explicit non-descending witness.)** For halves `(2, 3, 2, 4)`, the representation over `F_5`
   ```
   a = [[0,1],[2,0]],  b = [[2,4],[3,2]],  c = [[0,2],[1,2]],  e = [[4,2],[1,1]]
   ```
   satisfies all Artin relations. It has `c0 = 1` and `ct = 0`. The gcd of the 2x2 minors of `M_π(s)`
   is `s(s - 1)`.

   The same holds for halves `(2, 3, 2, 5)` with
   ```
   a = [[0,1],[1,1]],  b = [[3,1],[1,4]],  c = [[1,4],[4,2]],  e = [[1,1],[1,0]]
   ```
   Here the gcd is `s^2`. This example uses `5 = 0` in `F_5`.
3. **(Structural reason, any field.)** Let the halves be `(2, q, 2, p)` with `gcd(q, p) = 1`. Let
   `π : G -> GL_2(F)` satisfy:
   - `π(σ_bc) = π(σ_ae) = 0`;
   - `1 + π(ac)` and `1 + π(be)` have rank one and the same kernel.

   Then `c0(π) = 1` and `ct(π) = 0`. Both examples in 2 are of this shape.
4. **(No cheap rescue.)** Twisting by characters of `G/H` does not change `ct`: take
   `π_ω(g) = ω^(χ(g)) π(g)`. Nor does inducing from the finite-index subgroups
   `χ^(-1)(N Z)`: both preserve `ct = 0`. Both also leave the restriction to `H`, and so the
   level-0 witness, unchanged.
5. **(Outside the 2x2 joins, and the only census candidate resolved.)** Let `G_5` be the Artin
   group on `a, b, c, d, e` with labels `ab 6, ac 4, ad 4, ae 10, bc 3, bd 4, be 2, ce 2`, where
   `cd` and `de` are free. Put `χ = (1, -1, -1, 1, -1)`.
   - The cross edges are `ab, ac, ae, db`, with halves `3, 2, 5, 2`. The living graph has the two
     components `{a, d}` and `{b, c, e}`.
   - Over `F_5` there are 52 two-dimensional level-0 witnesses. None of them descends: all have
     `c0 = 1` and `ct = 0`. There are none over `F_3` or `F_7`.
   - One is `a = c = [[0,1],[1,1]]`, `b = [[0,4],[4,1]]`, `d = [[3,4],[1,0]]`, `e = 2`. Its gcd of
     minors is `s(s - 2)`.
   - Nevertheless `[χ] ∉ Σ^1(G_5)`. The permutation representation into `S_6`
     ```
     a = (0,2,1,4,5,3), b = (1,3,5,0,4,2), c = (0,4,5,1,3,2), d = (4,2,1,5,3,0), e = (0,1,5,3,4,2)
     ```
     (images of `0..5`) satisfies the relations, with `c0 = ct = 1` over `Q`. The
     `s`-independent vector `e_5 - e_1` spans the twisted kernel.
   - So the level-0 ideal is proper here too, and the corrected conjecture is consistent. But
     here also the smallest witnesses do not descend.

**What it shows.**
- The characters here are *not* counterexamples. By artin-2x2-dead-joins-sigma1-iff-k-q-odd-family,
  `[±χ] ∉ Σ^1` for every `(2, q, 2, p)` with `q, p >= 3`, witnessed by different representations. For
  `(2, 3, 2, 4)` that is an `S_6` permutation representation, and for `(2, 3, 2, 5)` a signed `S_5`
  representation.
- What dies is a class of proofs of the corrected conjecture: **witness-wise descent**. Such a
  proof would take a finite-dimensional module witness of `J_0 ≠ Z[H]` that extends to `G`. Examples
  are a quotient given by residual finiteness of `coker L_0`, or the output of the
  representation semi-procedure. It would then show that this same witness, perhaps twisted or
  cyclically induced, has positive twisted rank.
  - Part 2 shows that this fails in a class where the conjecture is known to hold.
  - So the level-0 to Novikov passage is not functorial in the witness. A proof must either
    manufacture new representations, as the `p`-dimensional constructions do, or work in
    `Z[H]` itself.
- **Census dichotomy.** Over `F_3` and `F_5`, exhaustive 2-dimensional searches were run on the
  2x2 joins `(2,2,2,2)`, `(2,2,2,3)`, `(2,2,2,5)`, `(3,3,3,3)`, `(2,3,2,5)`, `(2,5,2,3)`,
  `(2,3,2,4)`, `(2,4,2,5)`, `(2,2,3,3)`, `(2,3,3,3)`, `(3,2,2,5)` and `(2,2,4,4)`. Non-descending
  witnesses occur *only* in the opposite-twos family `(2, q, 2, p)` with `q, p >= 3` coprime.
  - This is exactly the family where every dead-edge ring witness is zero (Remark R1 of the
    2x2 proof).
  - In every other case tested, each 2-dimensional level-0 witness descends: `c0pos = ctpos` in
    `calib2.log`.
  - `(2, 4, 2, 5)` gave no 2-dimensional level-0 witness at all over `F_3` or `F_5`.
- **Five-vertex census.** A 5-vertex search covered two-block, non-star dead cuts of circuit
  rank `>= 3` (`census2.py`, three seeds, 34 instances). The verdicts were 25 NONMEMBER, 8 SILENT and 1
  CANDIDATE. NONMEMBER means some 2-dimensional witness descends, and SILENT means there is no
  level-0 witness in dimension 2. The single CANDIDATE is an
  instance with level-0 witnesses but no descending 2-dimensional one. That instance is `G_5` of
  Part 5, and it has the same shape as Part 3:
  - the two odd-half cross sums vanish;
  - the two half-2 sums have rank one with a common kernel.

  An `S_6` search settles it as a non-member. So every census CANDIDATE met so far is a failure
  of witness-wise descent, not a counterexample to the corrected conjecture.
