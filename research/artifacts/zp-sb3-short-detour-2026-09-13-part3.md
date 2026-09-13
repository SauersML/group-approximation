# SB_3 and short-detour enumerations, part 3: census of the height-refined order K1

Lane z1-03-qi-fn, 2026-09-13. Model and notation as in parts 1–2. Order key
K1(v) = (Σ d_i, −Σ |h(x_i)|, (d_1, d_2, d_3)), compared lexicographically, with ties among equal keys broken
arbitrarily. Status: COMPUTATIONAL EVIDENCE, not a proof. UNREVIEWED.

## 1. What was checked (MSI, `sb3_keys.py`, `sb3_depth.py`, python 3.11)

For a level-0 vertex v ≠ o:

- E(v) is the set of neighbours with strictly smaller key. A neighbour never has an equal key, because a
  move changes two coordinates of the distance vector.
- **depth(v)** is the least D such that breadth-first search from one element of E(v), through vertices of
  strictly smaller key, reaches all of E(v) within D steps.

Using only strictly smaller keys is valid for every tie-breaking. So any two elements of E(v) are joined
inside the initial segment by a path of length ≤ 2·depth(v).

| census | vertices | no earlier neighbour | depth 0 | 1 | 2 | 3 | 4 | 5 | ≥ 6 |
|---|---|---|---|---|---|---|---|---|---|
| exhaustive, all \|x_i\| ≤ 3 | 14908 | 0 | 288 | 1317 | 7217 | 5121 | 867 | 98 | 0 |
| random, \|x_i\| ≤ 6 | 20000 | 0 | 893 | 1744 | 8884 | 6470 | 1829 | 180 | 0 |
| random, \|x_i\| ≤ 9 | 4000 | 0 | 160 | 314 | 1788 | 1333 | 360 | 45 | 0 |

The maximal depth is 5 in all three censuses. Other keys (same checks, exhaustive |x_i| ≤ 3):

- K3 = (Σ d_i, −Σ|h|, Σ d_i^2, d): 0 failures at detour depth 6.
- K1 and K3 at depth 3: 965 and 723 failures. These are depth-limit artefacts; for example
  v = (e, aB, Ba) has seven earlier neighbours, pairwise at distance ≤ 4.
- K2 = (Σ d_i, +Σ|h|, d): 52 vertices with no earlier neighbour, among them (e, e, aB).
- K4 = (Σ d_i, −Σ|h|, −Σ d_i^2, d): 2740 failures at depth 3, not rechecked at depth 6.

A deepest instance at depth 5 is v = (a, bA, ABa): d = (1, 2, 3), h = (1, 0, −1).

## 2. Conjecture and consequence

**Conjecture** (`sb3-radial-height-order-is-a-short-detour-enumeration`). K1 orders the level set of T^3,
i.e. SB_3 with generating set { x_i y_j^{-1} : i ≠ j }, as a short-detour enumeration with L = 10.

The first condition is proved (part 2 §2). If the conjecture holds:

- by `short-detour-enumeration-gives-contractible-qi-2-complex`, SB_3 is quasi-isometric to a
  contractible, locally finite, proper geodesic 2-complex;
- SB_3 is not of type F_3 (Stallings 1963; the octahedron case of Bestvina–Brady);
- so Zaremsky Problem 1.3 has answer **no** under the geodesic reading, for n = 3 and hence every n ≥ 3.

## 3. Route to a proof

The detour condition at v depends only on bounded local data within distance about 6 of v:

- in each tree, the last ~6 letters of x_i, or the whole word when it is shorter;
- each height h(x_i) clipped to [−6, 6];
- the pattern of coordinate changes, which decides the lexicographic comparison without the actual values
  of the d_i.

So a finite configuration census would give a rigorous computer-assisted proof. As stated it is too
large (~10^11 configurations before symmetries), so it needs to be cut down.

Two ways forward:

- a hub vertex c(v), within detour depth ≤ 3 of every earlier neighbour, so that the top 4 letters
  suffice; the symmetries a↔b in each tree and the global swap up↔down cut the census by 16;
- a human case analysis using the part 1 star lemma together with the fact that every vertex with
  Σ d_i < Σ d_i(v), or with larger height spread, is earlier.
