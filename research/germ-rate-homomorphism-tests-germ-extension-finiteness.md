---
rg: 2
id: germ-rate-homomorphism-tests-germ-extension-finiteness
kind: claim
title: At an eventually periodic point the base germ group is infinite cyclic and carries a germ-rate homomorphism to the positive rationals, which must have finitely generated image for condition (E4)
distinct_from:
  rational-germ-singular-sets-are-finite-graph-path-spaces: that locates the singular points and shows they are eventually periodic when there are finitely many; this computes the germ groups at such a point and gives a necessary arithmetic condition for the Belk--Hyde--Matucci germ hypothesis.
  finite-state-mobius-pieces-see-finitely-many-primes: that bounds the primes appearing in locally Mobius finite-state pieces on a p-adic tree; this is the germ-level statement for any normal-form boundary, and it is the finite generation of a rate group rather than a bound on affine pieces.
  p-adic-dilation-normalizers-act-by-power-maps: that constrains conjugators of p-adic dilations by a six-exponentials argument; this constrains the germ group of a germ extension by a finite generation argument.
artifacts:
  - research/artifacts/gq-bh-bh-free-21-automatic-germ-extensions.md
---

**ESTABLISHED** by `germ-rate-homomorphism-test-proof` (lane proof, elementary, not
independently reviewed; no priority claimed).

## Setting

`L`, `∂L`, `B` and rationality as in `rational-germ-singular-sets-are-finite-graph-path-spaces`,
with `∂L` having no isolated points. Let `Γ` be a finite germ extension of `B` whose elements
are rational, and let `p ∈ sing(Γ)` be eventually periodic; by item 3 of that claim this is
automatic once the generators are thin. Write `(H)_p = Stab_H(p)/RStab_H(p)` for germ groups.

## Statement

1. **The base germ group is infinite cyclic.** `(B)_p ≅ Z`. A generator is the *period shift*
   `τ_p`, the prefix replacement `u v^k η ↦ u v^{k+m} η` for the least admissible `m ≥ 1`,
   where `p = u v^∞`.
2. **The germ rate.** For `γ ∈ (Γ)_p` represented by a rational `h` fixing `p`, the limit
   `ρ_p(γ) = lim_{n→∞} |out_h(p_1 … p_n)| / n` exists and is a positive rational, depends only
   on `γ`, and `ρ_p : (Γ)_p → Q_{>0}` is a group homomorphism into the multiplicative group.
   Moreover `(B)_p ≤ ker ρ_p`.
3. **The germ rate test (a necessary condition for (E4)).** Suppose condition (E4) holds at `p`
   through its normal branch, that is `(B)_p ⊴ (Γ)_p` with `(Γ)_p/(B)_p` finitely presented, or
   through the finite-index branch. Then `ρ_p((Γ)_p)` is a finitely generated subgroup of
   `Q_{>0}`. In particular only finitely many primes divide numerators and denominators of
   germ rates at `p`.
4. **A sufficient condition for (E4).** Condition (E4) holds at `p` whenever `(Γ)_p` is
   finitely generated abelian, and whenever `(B)_p` has finite index in `(Γ)_p`.
5. **Rates detect the finite-index branch.** If `ρ_p` is nontrivial then `(B)_p` has infinite
   index in `(Γ)_p`, so only the normal branch of (E4) can hold at `p`.

## Why it matters

Together with `thin-rational-actions-give-finite-germ-extensions`, this reduces the germ half
of `automatic-groups-embed-in-corner-germ-extensions` to a computation at finitely many
eventually periodic points, and supplies a test that can refute it: a structure whose germs at
one singular point expand the ray by unboundedly many different prime ratios fails (E4).

## Calibration

- **Flats.** For `Z^2 * Z` at a corner, `z2-free-z-normal-form-boundary-has-corner-singular-orbits`
  computes `(Γ)_p ≅ Z^2` with `(B)_p` the diagonal. All germs are prefix replacements, so every
  rate is `1`, `ρ_p` is trivial, `(Γ)_p` is finitely generated abelian, and item 4 gives (E4).
  This is consistent with item 5, since there `(B)_p` has infinite index and the normal branch
  is the one that holds.
- **Dilations.** A germ that replaces each period by `k` periods has rate `k`. A host whose
  germs at one point realize dilations by infinitely many primes has non-finitely-generated
  rate group, so by item 3 it fails (E4). That is the germ-level analogue of
  `finite-state-mobius-pieces-see-finitely-many-primes`.

## Scope

- Item 3 is a necessary condition only. Nothing here decides (E4) for any group that is not
  already covered by item 4.
- Items 1 and 2 need `p` eventually periodic, `∂L` perfect, and the germs represented by
  rational maps. Nothing is claimed at non-eventually-periodic singular points, which by item 3
  of `rational-germ-singular-sets-are-finite-graph-path-spaces` exist only when (E1) already
  fails.
