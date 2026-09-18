---
rg: 2
id: irrational-slope-v-tau-is-of-type-f-infinity
kind: claim
title: Cleary's golden-ratio rearrangement group V_τ is of type F_infinity; its golden subdivision category is Ore with a Garside family of elementary splits {L, R, M}, and its descending links are matching complexes with M-edges, (floor((n-2)/3)-1)-connected
requires:
  - irrational-slope-t-tau-and-v-tau-are-finitely-presented
distinct_from:
  irrational-slope-t-tau-and-v-tau-are-finitely-presented: that proves T_τ is F_∞ and V_τ finitely presented (as a full contracting RSG); this upgrades V_τ to F_∞, the statement Burillo–Nucinkis–Reeves assert and defer to "the methods of Stein".
  pisot-unit-slope-stein-groups-are-finitely-presented: that gives finite presentation of all (F)-unit Stein groups through BBMZ; F_∞ is not reachable that way, since BBMZ prove only finite presentation, and V_τ is not the full group of a shift of finite type (its groupoid has H_1 = Z/2).
  contracting-rover-nekrashevych-groups-are-f-infinity: that is the open F_∞ question for Röver–Nekrashevych groups of contracting self-similar groups; V_τ is a full contracting RSG, but this proof goes through subdivisions, not through the nucleus.
  circle-pl-groups-inherit-finiteness-from-interval-groups: that handles T-versions by the full simplex over one orbit; V-versions have point stabilizers that contain V again, so that trick is circular for them and a Stein–Farley argument is needed.
---

**ESTABLISHED** through `irrational-slope-v-tau-is-of-type-f-infinity-proof` (lane proof, not reviewed; no
priority claimed). Burillo–Nucinkis–Reeves (arXiv:2006.02401, l.101) assert this "by the methods of Stein" and
do not present it. A web search (09-18) found no written proof. The proof follows Brown's and Stein's
Stein–Farley method in Witzel's Garside-category form.

## Statement

Let `τ = (√5 − 1)/2` and let `V_τ` be the group of Burillo–Nucinkis–Reeves: piecewise-linear bijections of the
unit interval with finitely many breakpoints in `Z[τ]` and slopes in `τ^Z`.
1. `V_τ` is of type `F_∞`. So is its index-two simple subgroup `V_{xz}`.
2. **Structure used.** Call a partition of an interval *admissible* if it arises by iterating the two golden
   splits `L = (long, short)` and `R = (short, long)` (lengths `τ, τ²` of the whole).
   - Admissible partitions are closed under restriction.
   - Any two have a common admissible refinement.
   - A partition of `[0,1)` is divisible by `L` iff it contains `τ`, and by `R` iff it contains `τ²`.
     The lcm of `L` and `R` is the three-piece split `M = (τ², τ³, τ²)`.
3. **Descending links.** For a vertex with `n` pieces, the descending link is the complex `K(n)`.
   - Its vertices are the 4 labelled golden merges of each pair of pieces.
   - Its simplices are disjoint families of merges, plus the *M-couples* `{L(a,b), R(b,c)}` that
     assemble into one `M`-merge of `(a,b,c)`.
   - `K(n)` is `(⌊(n−2)/3⌋ − 1)`-connected.

With `circle-pl-groups-inherit-finiteness-from-interval-groups` and Cleary's theorem, all three golden groups
`F_τ ≤ T_τ ≤ V_τ` are now `F_∞` on main.

## Lesson for general BH

When two splitting rules do not commute, finiteness survives if their lcm is again a finite splitting rule.
For the golden ratio, `L ∨ R = M` is one more elementary split. Every descending-link simplex that uses the
extra rule is then a join of *couples* over a smaller matching complex, and a bad-simplex argument absorbs the
couples. This is the Garside condition in its simplest form. The lcm closure of the elementary moves must be
finite and local, as it is for Stein's integral slopes and here; whether it is for other quadratic Pisot slopes is open.
Constructive hosts should be designed so that their elementary moves close under lcm, not merely so that
they commute.
