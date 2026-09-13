# SB_3 and short-detour enumerations, part 2: distance-vector keys fail, and the height-refined keys

Lane z1-03-qi-fn, 2026-09-13. Continues `zp-sb3-short-detour-2026-09-13-part1.md` (same model and notation):

- v = (x_1, x_2, x_3) with Σ h(x_i) = 0;
- d_i = |x_i|;
- σ_i is the direction of the baseward edge of tree i.

Status: the obstruction in §1 is proved here; the rest is census data. UNREVIEWED.

## 1. Proposition: radial keys in the distance vector are never short-detour

**Proposition.** Let g be any strict total order on N^3, and order the vertices of the level set by
K(v) = (Σ d_i, g(d(v))), breaking ties among equal keys arbitrarily. Then some v ≠ o has no neighbour
of strictly smaller key. So no such enumeration satisfies the first condition of a short-detour
enumeration.

*Proof.* Fix an even s ≥ 6 and let m be the g-least vector in P_s = { d ∈ N^3 : Σ d_i = s }. Put
t = #{k : m_k ≥ 1}. Every move from a vertex changes Σ d_i by −2, 0 or +2.

1. **Case t ≥ 2.** Choose x_k of length m_k ending in a down letter, e.g. a^p B^q with p + q = m_k and
   q ≥ 1. Then σ_k = ↑, since the baseward edge is the inverse of the last letter, and h(x_k) can be any
   value in {−m_k, −m_k + 2, …, m_k − 2}.
   - The possible sums Σ h(x_k) fill {−s, …, s − 2t} in steps of 2. Since s is even and s ≥ 6 ≥ 2t,
     the value 0 occurs, so there is a level-0 vertex v with d(v) = m and every baseward edge up.
   - A move of v needs an up-step in one tree and a down-step in another. No tree has a baseward
     down-edge, so either the up-step is baseward and the down-step is away, giving d(v) − e_i + e_j ∈ P_s,
     which is g-larger than m, or both steps are away, giving Σ d_i = s + 2.
   - Either way the key increases.
2. **Case t = 1**, i.e. m = s·e_k. Take x_k of length s with h(x_k) = 0 and the other coordinates
   trivial. A move either goes baseward in tree k and away in another tree, giving m − e_k + e_j ∈ P_s,
   which is g-larger, or away in both trees, giving Σ d_i = s + 2. Again the key increases. ∎

So the vertex (aB, aB, aB) of the part 1 census is one instance of a general obstruction. Keys that see
more than the distance vector are needed.

## 2. Height-refined keys: the first condition holds

Put hs(v) = Σ |h(x_i)|. Consider K1 = (Σ d_i, −hs, d(v)), so that at equal ℓ^1 radius, more height
spread comes earlier.

**Lemma.** Under K1 every v ≠ o has an earlier neighbour.

1. If some σ_i = ↑ and some σ_j = ↓, then i ≠ j, and the move that is baseward in both trees lowers
   Σ d_i by 2.
2. Otherwise every baseward edge points the same way, say up; the down case is symmetric.
   - Since Σ h = 0, there is an i with d_i ≥ 1 and h(x_i) ≥ 0. If every nonzero coordinate had negative
     height, the sum would be negative.
   - There is also a j ≠ i with h(x_j) ≤ 0: the remaining two heights sum to −h(x_i) ≤ 0.
   - Move baseward-up in tree i and away-down in tree j. Then Σ d_i is unchanged, and hs grows by 2,
     since |h + 1| = |h| + 1 for h ≥ 0 and |h − 1| = |h| + 1 for h ≤ 0.
   - So the neighbour has the smaller key. ∎

The second condition (earlier neighbours joined by bounded detours) is being censused on MSI for K1–K4
(`sb3_keys.py`). Part 3 records the tables.
