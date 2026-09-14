---
rg: 2
id: rank-close-commutant-roots-restrict-to-level-one-roots
kind: claim
title: A root of a tuple rank-close to an amplification that commutes with the tuple's commutant restricts to a root at amplification one, so etale roots of rank-close tuples never go beyond exact roots of the original tuple
distinct_from:
  etale-roots-lie-in-the-bicommutant-of-the-constants: that says an etale root commutes with the commutant of its own constants and that amplification is inert for etale roots; this perturbs the amplified constants in normalized rank and shows the perturbation cannot create etale roots either, unless the unperturbed tuple already has an exact root.
  amplified-algebraic-roots-in-characteristic-zero: that is the approximate root premise for every tuple; this rules out one mechanism for it, the rank-density version through etale or commutant-compatible roots, and decides nothing about exact non-etale or approximate roots.
  etale-roots-of-the-semisimplification-lift-to-exact-roots: that lifts etale roots of a semisimplification to exact roots; this constrains which rank-close tuples can carry etale roots at all.
artifacts:
  - research/artifacts/hl-kl-rank-density-2026-09-14.md
---

**ESTABLISHED** through `rank-close-commutant-roots-level-one-proof` (linear
algebra plus `etale-roots-lie-in-the-bicommutant-of-the-constants`; unreviewed,
no novelty claimed).

**Setup.** `L` is any field, `a = (a_1, ..., a_k)` is in `GL_n(L)^k`, and `w` is
any word in `F_k * <x>`. For `r >= 1`, a tuple `a' = (a'_1, ..., a'_k)` in
`GL_{nr}(L)^k` is compared with the amplification `a (x) 1_r` through
`rho_j = rank(a'_j - a_j (x) 1_r)`. Write `C(a')` for the set of matrices commuting
with every `a'_j`. A root `T` of `w(T ; a') = 1` is *commutant-compatible* if
`TX = XT` for every `X` in `C(a')`.

**Theorem K.** Suppose `n (rho_1 + ... + rho_k) < r`, and let `T` in `GL_{nr}(L)` be a
commutant-compatible root of `w(T ; a') = 1`. Then there are a subspace `S` of
`L^r` with `dim S >= r - n (rho_1 + ... + rho_k)` and a matrix `t` in `GL_n(L)`
such that:
- `L^n (x) S` is invariant under `T`, `T^{-1}` and every `a'_j^{+-1}`;
- on `L^n (x) S` one has `T = t (x) 1_S` and `a'_j = a_j (x) 1_S`;
- `w(t ; a) = 1`.

**Corollary L (etale roots).** Let `delta < 1/(k n^2)`. If some tuple `a'` with
`rank(a'_j - a_j (x) 1_r) <= delta n r` for every `j` has an etale root, then
`w(x ; a) = 1` has a root in `GL_n(L)`. Indeed an etale root is
commutant-compatible by Theorem G of
`etale-roots-lie-in-the-bicommutant-of-the-constants`, and
`n sum_j rho_j <= k n^2 delta r < r`.

**Corollary M (what this says about rank density).** The rank-density form of
gap G2-new in `research/artifacts/hl-kl-etale-g1-2026-09-14.md` asks for tuples
`a'` within normalized rank `delta` of `a (x) 1_r` having an exact root. If
`w(x ; a) = 1` has no root in `GL_n(L)`, then for `delta < 1/(k n^2)`:
- no such `a'` has an etale root, so rank density cannot come from etale roots,
  from the Hensel lifting of Theorem E of
  `etale-roots-of-the-semisimplification-lift-to-exact-roots` applied to `a'`, or
  from genericity of the etale locus;
- every exact root of every such `a'` fails to commute with some matrix
  commuting with all the `a'_j`.

If `w(x ; a) = 1` does have a root `t`, rank density is trivial with `delta = 0`
and `T = t (x) 1_r`. So on the tuples where rank density matters, it needs exact
roots that are neither etale nor commutant-compatible.

**Scope.**
- The threshold `delta < 1/(k n^2)` is what the proof needs, not a proved limit.
- Nothing here produces or excludes approximate roots.
