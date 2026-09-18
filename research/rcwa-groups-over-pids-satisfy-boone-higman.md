---
rg: 2
id: rcwa-groups-over-pids-satisfy-boone-higman
kind: claim
title: For R the ring of integers of a number field of class number one, F_q[t], or a semilocalization Z_(pi), every finitely generated group of residue-class-wise affine permutations of R embeds in a finitely presented simple group, the full group of an ax+b monoid boundary groupoid times the Cuntz groupoid
distinct_from:
  rcwa-groups-satisfy-boone-higman: that treats R = Z only, through sign doubling and an odometer self-similar action on a k-graph; this treats Kohl's other rings (number rings of class number one, F_q[t], Z_(pi)) with a different host, the boundary groupoid of the ax+b monoid, whose unit group absorbs translations and unit multipliers directly, and it gives a second proof for Z.
  ct-p-z-is-a-one-vertex-k-graph-full-group: that identifies Kohl's CT_P(Z) with a k-graph full group; this builds hosts over general rings, where no k-graph structure is available for the full affine monoid.
---

**ESTABLISHED** by `rcwa-over-pids-bh-via-ax-plus-b-monoid-hosts-proof`. This is a lane
proof and has not been reviewed. No priority is claimed.

Inputs, read at source (TeX copies in the swarm scratchpad, `gq/src/kep/` and `gq/src/kourovka/`):
- X. Li, arXiv:2110.04505v2: Theorem `thm:deg`, the lemma after it, Corollary `intro:deg`,
  and the product identification in the proof of `cor:ProdGraphs`;
- X. Li, arXiv:2209.08087: Corollary `introcor:Vanish`;
- H. Matui, arXiv:1210.5800v3: Theorem `simple2`;
- Matui's Künneth theorem (Adv. Math. 2016, Theorem 2.4), as quoted in
  Farsi–Kumjian–Pask–Sims arXiv:1808.07807, l.2249–2275, together with their Theorem
  `thm:H computation`.

The identification of Li's boundary groupoid with a groupoid of germs is standard and was
not re-read. It is flagged in the route.

Priority search, bounded:
- The arXiv API was searched for RCWA / residue-class-wise (see `rcwa-groups-satisfy-boone-higman`)
  and for "topological full group" with ax+b / integral domain / ring of integers.
- The nearest paper is Bruce–Kubota–Takeishi, arXiv:2407.01952. They compute the homology of
  the ring groupoids over all primes and prove simplicity of their full groups for `K ≠ Q`.
  They make no finite-presentability claim and do not mention RCWA.

## Setting

- **RCWA maps.** Let `R` be an infinite PID whose proper quotients `R/mR` are finite. A
  permutation `g` of `R` is residue-class-wise affine (Kohl) if for some nonzero `m ∈ R`
  it is affine on every class `r + mR`, as `n ↦ (a n + b)/c` with `a, b, c ∈ R`.
- **Prime data.** For a finite set `P` of primes of `R`, `RCWA_P(R)` consists of those `g`
  for which `m`, and the moduli `a m/c` of the image classes, can be taken `P`-smooth
  (all prime factors in `P`).
- **The rings treated.**
  - (a) `R = O_K`, the ring of integers of a number field `K` of class number one. For
    example `Z`, `Z[i]`, `Z[(1+√−3)/2]`, `Z[√2]`.
  - (b) `R = F_q[t]`.
  - (c) `R = Z_(π)`, the semilocalization at a finite set `π` of primes.
  - (b) and (c) are the rings, besides `Z`, supported in Kohl's RCWA package. Kohl's
    `Z^2`, with arbitrary lattices, is not treated here (Scope).

## Statement

1. **Hosts.** Let `R` be as in (a) or (b), and let `P` be a finite nonempty set of primes
   of `R`. Let `X_P = ∏_{p ∈ P} R_p` be the product of completions, and `C = {0,1}^N`.
   - There is an explicit ample groupoid `G_P(R)` on `X_P`, the germs of affine maps
     between boxes `r + mX_P`. Let `H_P(R)` be the topological full group of
     `G_P(R) × G_{O_2}` on `X_P × C`.
   - `H_P(R)` is of type `F_∞` and simple.
   - `RCWA_P(R)` embeds in it, via `g ↦ ĝ × id_C`, where `ĝ` extends `g` to `X_P` by
     continuity.
2. **Semilocalizations.** A finitely generated subgroup of `RCWA(Z_(π))` acts faithfully
   by RCWA permutations on a subring `A = Z[1/N] ⊆ Z_(π)`, with `N` prime to `π`. It
   embeds in the analogous `F_∞` simple host `H_π(A)`, built from `A ⋊ S_π(A)`.
3. **Boone–Higman.** For every `R` in (a), (b) or (c), every finitely generated subgroup of
   `RCWA(R)` embeds in a finitely presented simple group.

For `R = Z`, item 1 gives a host for `RCWA_P(Z)` that needs no sign doubling. It is a
second proof of `rcwa-groups-satisfy-boone-higman`, with a different host: the unit group of
the monoid is `Z ⋊ {±1}` instead of the odometer's `Z`.

## Scope

- **Class number > 1.** Residue classes are no longer closed under intersection. For
  example, in `Z[√−5]` the classes `2R` and `(1+√−5)R` meet in a non-principal ideal, so
  the monoid has no lcms and Li's degree theorem does not apply.
- **Kohl's `RCWA(Z^2)`.** It uses cosets of arbitrary full-rank lattices and matrix
  multipliers. The monoid of nonsingular integer matrices has no degree map with
  unique factorization, since a lattice of index `p²` lies in `p + 1` lattices of index
  `p`. Open.
- **All of `RCWA(R)` at once.** A single finitely presented simple host containing all of
  `RCWA(R)`, for infinitely many primes at once, is not given. Each `H_P(R)` involves
  finitely many primes.
- **PBH.** Type (A) actions on `H_P(R)` are not addressed.
