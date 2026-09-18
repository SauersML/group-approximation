# Referee review of the SB_3 short-detour census (part 4), 2026-09-17

Reviewer: swarm-0917-w6-w6-z-last1 (lane: last mile toward `zaremsky-open-problems-2026-07-12`).
Object under review: `research/artifacts/zp-sb3-short-detour-2026-09-13-part4.md` (lane z1-03-qi-fn,
2026-09-13), the computer-assisted proof of `sb3-radial-height-order-is-a-short-detour-enumeration`, held
back pending review. Verdict: **PASS**. Scripts and logs: `experiments/sb3-short-detour-review-2026-09-17/`.

## 1. Statement checked

SB_3 = ker(F_2^3 → Z), every standard generator ↦ 1, identified with the level-0 vertices
v = (x_1, x_2, x_3) of T^3 (reduced words, h = exponent sum). Generating set
S = { x_i y_j^{-1} : i ≠ j, x, y ∈ {a, b} } (24 elements, symmetric), acting by right multiplication.
Key K1(v) = (Σ|x_i|, −Σ|h(x_i)|, (|x_1|, |x_2|, |x_3|)), lexicographic, ties broken arbitrarily.

Claim: for every v ≠ o, (1) E(v) := {neighbours with smaller key} ≠ ∅, and (2) some e_0 ∈ E(v) reaches
every element of E(v) in ≤ 6 steps through vertices of key < K1(v). Hence K1 is a short-detour enumeration
(in the sense of `short-detour-enumeration-gives-contractible-qi-2-complex`) with L = 12. The claim states
L = 10; §5 shows the sharper bound "≤ 3 steps", so L = 6.

## 2. From the claim to the definition (checked)

- Each key class is finite (Σ|x_i| is bounded), o is the unique minimum, so K1 with any tie-breaking is an
  enumeration g_0 = o, g_1, … of SB_3 of order type ω.
- A move changes the lengths of exactly two coordinates by ±1, so the length vector changes and a
  neighbour never has the key of v. Hence the Γ-neighbours of v in the initial segment A_k before v are
  exactly E(v), and every vertex of smaller key lies in A_k. Paths through smaller keys lie in Γ[A_k].
- Two elements of E(v) are joined through e_0 by a walk of length ≤ 12 in Γ[A_k]. Both bullets of the
  definition hold with L = 12. Condition (1) also shows S generates SB_3.

## 3. Soundness of the finite reduction (part 4 §2), re-derived

Per tree: 'S' stores the whole word when |x_i| ≤ 2; 'L' stores the last two letters w and
c = clip(h(x_i), ±3) when |x_i| ≥ 3, so x_i = p·w reduced with p ≠ ∅.

1. **Coverage.** Every real v ≠ o has a configuration; the feasibility filter only discards classes in which
   Σh = 0 is impossible, or v = o. Superset coverage is all that is needed.
2. **Abstract paths are real.** A letter appended to a nonempty known word, or cancelled against its last
   letter, is the same operation on p·w (no interaction with p). The only operation that could touch p,
   acting on an 'L' coordinate whose known word has become empty, is forbidden. So the abstract graph is a
   subgraph of the induced graph on the real vertices p·(known words), and abstract tuples determine real
   vertices injectively.
3. **Earlier-marking is sound.** Length changes are exact. For exact heights (all 'S' and |c| < 3),
   |h + dh| − |h| is exact. For c = +3 (h ≥ 3) and dh ≥ −3, h + dh ≥ 0, so |h + dh| − |h| = dh; symmetric
   for c = −3. Otherwise the vertex is marked undetermined and treated as not earlier in the BFS. Thus a
   vertex marked earlier is really earlier; no false positives.
4. **E(v) is exact.** A neighbour changes each touched coordinate by one letter; the known word has length
   2 so no move is forbidden, and |dh| = 1 is never undetermined. So abstract E(v) = real E(v), and the
   script returns failure if any neighbour were undetermined.
5. Therefore "abstract E(v) ≠ ∅ and BFS from E[0] through abstract earlier vertices reaches all of E(v)
   within 6 steps" for every configuration implies (1) and (2) for every real v. The lexicographic third
   component is decided by the first coordinate whose length changes, which the script uses.

No gap found. (The choice of e_0 = E[0] depends on Python set order; this is harmless, since the
statement only needs one e_0.)

## 4. Computations (this review)

| run | script | result |
|---|---|---|
| published script re-run verbatim (extracted from part 4 §5) | `sb3_abstract_as_published.py 2 3 6 4` | 101 tree configs, 197416 feasible configs, **bad 0** (`run_published_2_3_6.log`, 3m54s) |
| independent re-implementation from the statement (string words, interval arithmetic for saturated heights, least eccentricity over all e_0) | `sb3_independent_abstract.py 2 3 6 4` | 101 tree states, 197416 feasible configs, least-eccentricity histogram {0: 400, 1: 6517, 2: 130003, 3: 60496}, **bad 0** (`run_independent_2_3_6.log`, 17m56s) |
| real-vertex census, exhaustive \|x_i\| ≤ 3, no abstraction | `sb3_real_vertex_census.py exhaustive 3 2` | 14908 vertices (same count as part 3), min eccentricity histogram {0: 288, 1: 1297, 2: 11827, 3: 1496}, **bad 0** |
| real-vertex census, 4000 random vertices, \|x_i\| ≤ 10, biased to large heights | `sb3_real_vertex_census.py random 10 4000 917 2` | min eccentricity ≤ 3, **bad 0** |

The independent implementation reproduces the feasible configuration count 197416 exactly.

## 5. The constant: L = 6, which covers the claimed L = 10

The published script shows that one e_0 reaches E(v) within 6 steps, which gives L = 12. That is larger
than the constant L = 10 in the claim's statement. The independent run closes this gap. In every
configuration it computes the least eccentricity of E(v) over all e_0 ∈ E(v), inside the abstract graph of
vertices that are really earlier. Its soundness argument is the same as §3; the only change is that
saturated heights are handled as intervals instead of clipped values, which is at least as conservative.

- The maximum over all 197416 configurations is 3.
- So for every real v ≠ o some e_0 ∈ E(v) reaches every element of E(v) within 3 steps through vertices
  of smaller key.
- Any two elements of E(v) are then joined through e_0 by a path of length ≤ 6 in Γ[A_k].
- So K1 is a short-detour enumeration with L = 6. This implies the claim with L = 10, and the 2-cells of
  the resulting complex have perimeter ≤ 8.

The real-vertex censuses (no abstraction) agree: the least eccentricity is always ≤ 3.

Verdict: **PASS**. `sb3-radial-height-order-is-a-short-detour-enumeration` is proved as stated.
