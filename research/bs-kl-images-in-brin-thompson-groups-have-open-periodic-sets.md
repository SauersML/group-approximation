---
rg: 2
id: bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets
kind: claim
title: An element of a Brin--Thompson group nV that is conjugate to a proper power of itself has zero periodic exponents and an open periodic set, so an infinite-order image of s under BS(k,l) → nV carries a nonempty closed aperiodic invariant set
distinct_from:
  almost-automorphism-conjugate-to-proper-power-is-equicontinuous: that treats almost automorphisms with tree-automorphism sections, including V_{d,r} and Rover--Nekrashevych groups, and excludes nV; this treats Brin--Thompson nV, whose sections are trivial but whose exponent cocycle is vector valued, and it does not give equicontinuity.
  bs12-embeds-in-brin-thompson-2v: that is the open embedding question; this is a necessary-condition theorem about any witness.
---

**ESTABLISHED** (elementary; no novelty claimed).

**Setting.**
- `C = {0,1}^N` is the Cantor space, and `C(u)` is the cone of sequences
  beginning with the finite word `u`.
- A *brick* is a product `C(u_1) × … × C(u_n)` in `C^n`.
- Brin's group `nV` (Brin, *Higher dimensional Thompson groups*, Geom. Dedicata
  108 (2004)) is the group of homeomorphisms `g` of `C^n` with a *table*: two
  partitions of `C^n` into finitely many bricks `B_i = Π_j C(u_{i,j})` and
  `B'_i = Π_j C(v_{i,j})` such that
  `g(u_{i,1} w_1, …, u_{i,n} w_n) = (v_{i,1} w_1, …, v_{i,n} w_n)`.
- `L(g)` is the largest word length `|u_{i,j}|`, `|v_{i,j}|` in some table of
  `g`, minimized over tables.

**Statement.** Let `g, f ∈ nV` with `f g^k f^-1 = g^l`, where `k, l ≠ 0` and
`|k| ≠ |l|`. Then:
1. **Zero periodic exponents.** Every periodic point `x` of `g`, of least period
   `p`, has exponent vector `δ_{g^p}(x) = 0 ∈ Z^n`. Here `δ` is the exponent
   cocycle of the route: on a table brick, `δ_g = (|v_j| - |u_j|)_j`.
2. **Local periodicity.** `g^p` is the identity on a whole brick containing `x`.
   So the set `Per(g)` of periodic points is open.
3. **Aperiodic core.** `g` has finite order iff `Per(g) = C^n`. If `g` has
   infinite order, `K(g) = C^n \ Per(g)` is a nonempty closed `g`-invariant set
   with no periodic points.
4. **Logarithmic exponents.** If `k = ±1`, there is `c` with
   `|δ_{g^N}(x)|_∞ ≤ c (1 + log|N|)^2` for all `N ≠ 0` and all `x`.

**Consequence.** In every homomorphism `BS(k,l) → nV` with `|k| ≠ |l|`, the image
of `s` either has finite order or has a nonempty closed invariant set without
periodic points, while all its periodic points lie in an open set on which some
power is the identity. For `BS(1,l)` its exponent sums grow at most like
`(log N)^2` everywhere.

**Scope.**
- *What is not decided.* Whether `BS(1,2)` embeds in some `nV` with `n ≥ 2`.
  That is `bs12-embeds-in-brin-thompson-2v`, still OPEN. Undistortedness does not
  exclude it, since `mV` has distortion elements (Callard--Salo,
  arXiv:2208.00685v3, Theorem E, checked against the extracted text).
- *Relation to `V`.* For `n = 1`, non-embedding of `BS(k,l)` in `V` is already
  covered by `almost-automorphism-conjugate-to-proper-power-is-equicontinuous`.
- *What this node adds.* The vector cocycle, local periodicity, which is special
  to trivial sections, and the aperiodic-core reduction for `nV`.

The proof is `brin-thompson-exponent-cocycle-proof`.
