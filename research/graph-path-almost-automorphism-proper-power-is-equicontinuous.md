---
rg: 2
id: graph-path-almost-automorphism-proper-power-is-equicontinuous
kind: claim
title: An almost automorphism of the path space of a finite graph that is conjugate to a proper power of itself generates an equicontinuous group, and has finite order when its sections are trivial
distinct_from:
  almost-automorphism-conjugate-to-proper-power-is-equicontinuous: that is the statement for one regular rooted forest, a full shift with a single cone type; this is the statement for the path space of an arbitrary finite graph, so for one-sided shifts of finite type with several cone types and their topological full groups.
artifacts:
  - research/artifacts/bh-bg-similarity-hosts-2026-09-12.md
---

**ESTABLISHED** (elementary; no novelty claimed beyond the scope below).

**Setting.**
- `E` is a finite directed graph with no sinks. `X_E` is the set of one-sided
  infinite paths `x = e_1 e_2 ...` (with `r(e_i) = s(e_(i+1))`), with
  `dist(x,y) = 2^-|x ∧ y|`, where `|x ∧ y|` is the length of the longest common
  prefix. `X_E` is compact, zero-dimensional and metrizable.
- For a finite path `u` (a vertex counts as a path of length 0), `Z_(r(u))` is
  the set of infinite paths starting at `r(u)`, and the *cone* is
  `C(u) = u Z_(r(u))`.
- A *path isometry* is a bijection `h : Z_v → Z_(v')` with
  `|h(w) ∧ h(w')| = |w ∧ w'|`.
- `A(E)` is the set of homeomorphisms `g` of `X_E` with a *table*: finite
  partitions `X_E = ⊔ C(u_i) = ⊔ C(v_i)` and path isometries
  `h_i : Z_(r(u_i)) → Z_(r(v_i))` with `g(u_i w) = v_i h_i(w)`. It is a group.
  When every `h_i` is the identity (so `r(u_i) = r(v_i)`), `g` lies in the
  topological full group of the one-sided shift of finite type `X_E`.

**Statement.** Let `g, f ∈ A(E)` with `f g^k f^-1 = g^l`, where `k, l ≠ 0` and
`|k| ≠ |l|`. Then:
1. there are `N` and `K` such that, for every `m ∈ Z` and every finite path `q`
   of length `N`, `g^m` acts on `C(q)` as `q w ↦ p h(w)` with `h` a path
   isometry and `||p| - N| ≤ K`. In particular every `g^m` is `2^K`-Lipschitz on
   each level-`N` cone, and `{g^m : m ∈ Z}` is equicontinuous;
2. some `g^j` with `j ≥ 1` maps every level-`N` cone onto itself;
3. if all sections of `g` are identities, then `g` has finite order.

**Consequence.** Let `BS(k,l) = < s, u | u s^k u^-1 = s^l >` with `|k| ≠ |l|`.
Every homomorphism from `BS(k,l)` to the topological full group of a one-sided
shift of finite type (given by a finite graph) sends `s` to an element of finite
order, so `BS(k,l)` embeds in none of these groups.

**Scope.**
- *What is not new.* The argument is the one-cone-type proof of
  `almost-automorphism-conjugate-to-proper-power-is-equicontinuous`, run on a
  finite graph. The only changes are the pigeonhole count (finite paths of a
  fixed length instead of forest words) and the fixed-point step on `Z_(r(q))`.
  No literature search was run for the consequence.
- *Not covered.*
  - Brin--Thompson groups `nV`: exponents are vectors, and the pigeonhole step
    fails.
  - Rational similarity groups whose sections are not path isometries.
  - Full groups of non-expansive groupoids, or of two-sided shifts.

The proof is `graph-almost-automorphism-exponent-pumping-proof`.
