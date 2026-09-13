---
rg: 2
id: weighted-similarity-proper-power-conjugates-are-equicontinuous
kind: claim
title: If every element of a group of homeomorphisms of a path space is a similarity for a positive edge-weighted metric on all sufficiently heavy cones, every element conjugate to a proper power generates an equicontinuous cyclic group
distinct_from:
  graph-path-almost-automorphism-proper-power-is-equicontinuous: that is the case of unit edge weights with pieces given by path isometries, which map cones onto cones; this allows arbitrary positive edge weights and pieces that need not be onto a cone.
  finite-nucleus-rsg-proper-power-conjugates-are-equicontinuous: that is the open statement for every finite-nucleus RSG, whose nuclear maps need only be injective and open; this needs every nuclear map to be an exact similarity for one weighting.
---

**ESTABLISHED** (elementary; no novelty claimed).

**Setting.**
- `Γ` is a finite directed graph and `Σ_Γ` its space of one-sided infinite
  paths.
- `E ⊆ Σ_Γ` is clopen with no isolated points, and `C(u)` is the cone of paths
  starting with `u`.
- `w` assigns a positive weight to each edge, and `w(u)` is the total weight of
  a finite path.
- `x ∧ y` is the longest common prefix, and `d_w(x, y) = exp(-w(x ∧ y))`.
- A homeomorphism `h` of `E` is a **`w`-similarity on `U` with ratio `λ`** if
  `w(hx ∧ hy) = w(x ∧ y) + λ` for all distinct `x, y ∈ U`.
- `h` is **`w`-tame** if some `L_h` makes `h` a `w`-similarity on every cone
  `C(u) ⊆ E` with `w(u) ≥ L_h`.

**Statement.** Let `G` be a group of `w`-tame homeomorphisms of `E`. Let
`f, g ∈ G` and nonzero integers `k, l` with `|k| ≠ |l|` satisfy
`f g^k f^-1 = g^l`. Then:
1. there are `K` and `A` with `d_w(g^m x, g^m y) ≤ e^K d_w(x, y)` for all
   `m ∈ Z` and all `x, y` with `w(x ∧ y) ≥ A`;
2. so `{g^m : m ∈ Z}` is equicontinuous.

**Rational similarity groups.** Let `G ≤ R_(Γ,E)`, in the sense of
Belk--Bleak--Matucci--Zaremsky (arXiv:2309.06224v3). Suppose every element of
`Nuc_G` is a `w`-similarity on its whole domain. Then every element of `G` is
`w`-tame, so the conclusion holds. As in
`finite-nucleus-rsg-proper-power-conjugates-are-equicontinuous`, this gives:
- every homomorphism from the Baumslag--Gersten group into such a `G` kills `a`;
- every homomorphism from Higman's group `H4` into such a `G` is trivial.

**Reach.**
- **Covered.** Unit weights with path isometries recover the equicontinuity part
  of `graph-path-almost-automorphism-proper-power-is-equicontinuous`.
  Non-uniform weights and non-surjective pieces are allowed. No finite-nucleus
  RSG with a non-isometric similarity nucleus has been checked to exist.
- **Not covered.** Nuclear maps that are bi-Lipschitz but not similarities. The
  involution `q` of `research/artifacts/bh-bg-rsg-nonisometric-hosts-2026-09-13.md`
  §1 has ratios `-1, 0, 1` for `w(0) = 2`, `w(1) = 1`. For those,
  `bilipschitz-finite-nucleus-rsg-proper-power-germs-are-torsion` gives only
  torsion germs at rational periodic points.

The proof is `weighted-similarity-exponent-pumping-proof`.
