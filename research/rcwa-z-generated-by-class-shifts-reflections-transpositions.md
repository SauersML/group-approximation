---
rg: 2
id: rcwa-z-generated-by-class-shifts-reflections-transpositions
kind: claim
title: Kohl's factorization conjecture holds - every residue-class-wise affine permutation of Z is a product of class shifts, class reflections and class transpositions, in the normal form (commuting class shifts)(element of CT(Z))(commuting class reflections)
requires:
  - ct-z-is-the-rcwa-group-fixing-the-nonnegative-integers
  - ct-p-z-is-a-one-vertex-k-graph-full-group
distinct_from:
  ct-z-is-the-rcwa-group-fixing-the-nonnegative-integers: that identifies the subgroup CT(Z) with the RCWA permutations fixing N_0 setwise (Kourovka 17.59); this factors every RCWA permutation of Z, including orientation-reversing pieces and pieces with nonzero shift, through that subgroup, and so settles the factorization conjecture stated in Kohl's RCWA manual.
  rcwa-groups-satisfy-boone-higman: that embeds finitely generated RCWA groups in finitely presented simple hosts; this is a generation theorem for RCWA(Z) itself and needs no host.
---

**ESTABLISHED** (lane proof, not reviewed). It uses only
`ct-z-is-the-rcwa-group-fixing-the-nonnegative-integers` (Kourovka 17.59) and item 3 of
`ct-p-z-is-a-one-vertex-k-graph-full-group`, plus two lines of arithmetic. Both nodes are
lane proofs, not reviewed. No priority is claimed.

## The conjecture

S. Kohl, *RCWA — Residue-Class-Wise Affine Groups* (GAP package manual, chapter 2, read on
2026-09-18 at docs.gap-system.org/pkg/rcwa/doc/chap2.html), verbatim:

> "There is computational evidence for the conjecture that any residue-class-wise affine
> permutation of ℤ can be factored into members of the following three series of
> permutations of particularly simple structure."

The three series are defined there as follows.
- **Class shift.** "The class shift ν_{r(m)} is the rcwa mapping of ℤ which maps n ∈ r(m)
  to n + m and which fixes ℤ ∖ r(m) pointwise."
- **Class reflection.** "The class reflection ς_{r(m)} is the rcwa mapping of ℤ which maps
  n ∈ r(m) to −n + 2r and which fixes ℤ ∖ r(m) pointwise."
- **Class transposition.** τ_{r₁(m₁),r₂(m₂)} is the involution interchanging r₁ + km₁ and
  r₂ + km₂ for all k and fixing everything else.

The manual's `FactorizationIntoCSCRCT` "may return `fail`, stop with an error message or
run into an infinite loop". Residue classes are written `r(m)` with `0 ≤ r < m`.

## Statement

Every `g ∈ RCWA(Z)` factors as

    g = ν_{s_1(n_1)}^{c_1} ⋯ ν_{s_N(n_N)}^{c_N} · h' · ς_{r_{i_1}(m)} ⋯ ς_{r_{i_D}(m)},

with the following properties:
- the classes `s_i(n_i)` partition `Z`, so the class shifts commute;
- the classes `r_{i_j}(m)` are distinct classes mod `m`, so the reflections commute;
- the `c_i ∈ Z` are integers;
- `h' ∈ CT(Z)` is a product of class transpositions.

Negative powers are allowed, since `ν_{r(m)}^{-1} = ς_{r(m)} ν_{r(m)} ς_{r(m)}`. So
`RCWA(Z) = ⟨class shifts, class reflections, class transpositions⟩`, which proves Kohl's
conjecture.

**Refinement.** Let `P` be a set of odd primes and `P' = P ∪ {2}`. If the modulus and the
multipliers of `g` are `P'`-smooth, then every factor can be taken with `P'`-smooth moduli,
and `h' ∈ CT_P(Z)`.

## Proof

Let `g` be affine on every class `r_i(m)`, `0 ≤ r_i < m`, with slope `σ_i ≠ 0`. Put
`D = {i : σ_i < 0}`.

1. **Remove the reversals.**
   - `ς_{r_i(m)}` maps `r_i + tm` to `r_i − tm`, so it maps `r_i(m)` onto itself.
   - Put `ρ = ∏_{i ∈ D} ς_{r_i(m)}`. The factors have disjoint supports, so they commute,
     and `ρ² = 1`.
   - On `r_i(m)` with `i ∈ D`, `gρ(n) = g(−n + 2r_i)` is affine with slope `−σ_i > 0`. On
     the other classes `gρ = g`.
   - So `h := gρ` is affine and increasing on every class mod `m`.
2. **Read off the shifts.** Steps 1–2 of `ct-z-is-the-rcwa-group-fixing-the-nonnegative-integers`
   use only positive slopes. They give classes `s_i(n_i)` partitioning `Z`, with
   `0 ≤ s_i < n_i` and `n_i = σ_i m` up to sign, and integers `c_i`, such that
   `h(r_i + tm) = s_i + (t + c_i) n_i` for all `t`.
3. **Remove the shifts.** `ν_{s(n)}^j` maps `s + tn` to `s + (t + j)n` on `s(n)`. Put
   `κ = ∏_i ν_{s_i(n_i)}^{−c_i}`, whose factors have disjoint supports. Then
   `h' := κh` satisfies `h'(r_i + tm) = s_i + t n_i`.
4. **`h' ∈ CT(Z)`.**
   - `h'` is RCWA.
   - For `n = r_i + tm`, we have `n ≥ 0` iff `t ≥ 0` iff `h'(n) ≥ 0`, because
     `0 ≤ r_i < m` and `0 ≤ s_i < n_i`.
   - So `h'(N_0) = N_0`, and `h' ∈ RCWA^+(Z) = CT(Z)` by
     `ct-z-is-the-rcwa-group-fixing-the-nonnegative-integers`.
5. **Assemble.** `g = hρ = κ^{−1} h' ρ`, which is the displayed normal form.

**Inverse class shifts.** `ς_{r(m)} ν_{r(m)} ς_{r(m)}` sends `r + tm` to `r − tm`, then to
`r − (t − 1)m`, then to `r + (t − 1)m`. So it is `ν_{r(m)}^{−1}`.

**The refinement.** If `m` and the slopes are `P'`-smooth, then so are the `n_i`, so the
shifts and reflections have `P'`-smooth moduli. The element `h'` is piecewise canonical with
`P'`-smooth moduli, so `h' ∈ CT_P(Z)` by item 3 of `ct-p-z-is-a-one-vertex-k-graph-full-group`. ∎

## Remarks

- **The effective part.** Steps 1–3 are explicit. The factorization of `h'` into class
  transpositions comes from the proof of Kourovka 17.59, which goes through Matui's
  simplicity theorem. So this proof does not supply the missing termination of
  `FactorizationIntoCSCRCT`.
  - An effective factorization of `h' ∈ CT_P(Z)`, by refining box partitions as for
    Thompson's `V`, is the natural next step.
- **Consequences.**
  - `RCWA(Z)` is generated by `CT(Z)` together with the class shifts and class
    reflections of proper classes. Any two such class shifts are conjugate by an element
    of `CT(Z)` mapping one class canonically onto the other, and likewise for class
    reflections.
  - The class-wise order-preserving subgroup is `⟨CT(Z), class shifts⟩`.
- **In the hosts.** In `rcwa-groups-satisfy-boone-higman`, the class shift `ν_{r(m)}` is the
  odometer twist `σ` on the box `B(r, m)` of the host `H_P`.
