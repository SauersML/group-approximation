---
rg: 2
id: power-two-folded-fatgraphs-of-genus-k-plus-two-family-proof
kind: route
title: Periodic boundary segments, fifteen affine pairing rules and nineteen vertex templates, checked by exact affine arithmetic for all k
target: power-two-folded-fatgraphs-of-genus-k-plus-two-family
requires:
  - legal-f-folded-fatgraphs-give-surface-subgroups
  - power-two-legal-folded-certificates-reach-beyond-power-one
  - hyperbolic-f3-by-z-with-genus-two-surface-certificates
  - legal-folded-certificates-at-power-one-census
artifacts:
  - experiments/legal-f-folded-fatgraphs-2026-09-17/power_two_family_symbolic.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/power_two_family_symbolic.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/power_two_family_certificates.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/power_two_family_certificates.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/power_two_family_m1_lp.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/power_two_family_m1_lp.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/verify_surface.py
---

Conventions are those of `legal-f-folded-fatgraphs-give-surface-subgroups` and of
`verify_surface.py`:

- upper case is inverse;
- `p` is the edge involution and `next` the boundary order;
- vertices are the cycles of `sigma = next o p`;
- the label of a dart is its letter, and (L) is tested on the labels of the darts in a cycle;
- a junction (`f^2`-vertex) corner sits at the dart that starts a block `f^2(x)^-1`;
- a minus corner sits at a dart of a minus circle.

Standard facts used, not re-read at source: Bestvina--Handel, Brinkmann, one-endedness of
free-by-cyclic groups, and invariance of the Alexander polynomial of a group with `b_1 = 1`
(up to units and `t <-> t^-1`).

**Step 1: automorphism.** Write `phi = phi_k`. We have `phi(cA) = babb BBA = b` and
`phi(aC) = abb BBAB = B`, so `phi(aaCaC) = abb B B = a`. Then `phi(cAcAA) = phi(aaCaC)^-1 = A` and
`phi(b (cAcAA)^k) = c a^k A^k = c`. So `phi` is onto, hence an automorphism, with inverse
`psi_k = (a -> aaCaC, b -> cA, c -> b (cAcAA)^k)`. `verify_surface.py` re-checks
`phi o psi = psi o phi = id` for `k <= 200`.

**Step 2: hyperbolic, and the invariants.**

- The transition matrix `M_k` has columns `(1,2,0)`, `(k,0,1)` and `(1,3,0)`. Expanding the
  determinant along its first row gives `det(tI - M_k) = (t-1)(t^2-3) - 2kt - 2 = t^3 - t^2 - (2k+3)t + 1`.
- The zero pattern of `M_k` does not depend on `k >= 1`, so neither does that of `M_k^3`. It is
  positive for `k = 1` (checker), so `M_k^3 > 0` for all `k`.
- The only possible rational roots are `±1`, and `chi_k(1) = -2k - 2` and `chi_k(-1) = 2k + 2` are
  nonzero. So `chi_k` is irreducible.
- Step 2 of `hyperbolic-f3-by-z-with-genus-two-surface-certificates-proof` uses only these facts
  and a Perron--Frobenius root `> 1`. So `phi_k` is fully irreducible and atoroidal, and `G_k` is
  one-ended and hyperbolic.
- `H_1(G_k) = Z ⊕ coker(M_k - I)`, with `|det(M_k - I)| = |chi_k(1)| = 2k + 2`. The kernel of the
  unique map `G_k -> Z` up to sign is `F`, so the Alexander polynomial is `chi_k`.
- For `k >= 2`, neither `chi_k` nor its reciprocal `t^3 - (2k+3)t^2 - t + 1` equals any of the
  following, so `G_k` is not isomorphic to those groups:
  - `t^3 - (i+j+1)t^2 - (i+3j+5)t + 1` of `hyperbolic-f3-by-z-family-with-genus-two-surfaces`
    (equality forces `i = j = 0` and `k = 1`, and the reciprocal would need `i + 3j + 5 = 1`);
  - `t^3 - 2t^2 - 6t + 1`;
  - the degree-`>= 4` polynomials of `hyperbolic-fn-by-z-genus-two-surfaces-every-fibre-rank`.

**Step 3: (TT) and gates.** `phi_k` and `phi_k^2` are positive, so (TT) holds. On directions,
`Df` sends `a -> a`, `b -> c`, `c -> b`, `A -> B`, `B -> A` and `C -> B`. So `A` and `C` share a
gate, and the gates are `{a}, {b}, {c}, {A, C}, {B}` for every `k`. They are the same for `f^2`.

**Step 4: the boundary.** `partial^- = {bc, CB}`. Since `f(bc) = c a^k babb` is positive, the
following words are reduced:

```text
f^2(b) = babb (abb)^k,    f^2(c) = c a^k abb c a^k c a^k,
N1 = bc,   P1 = f^2(bc)^-1 = f^2(c)^-1 f^2(b)^-1 = A^k C A^k C BBA A^k C (BBA)^k BBAB,
N2 = CB,   P2 = f^2(CB)^-1 = f^2(b) f^2(c)      = babb (abb)^k c a^k abb c a^k c a^k.
```

- `|P1| = |P2| = 6k + 10`.
- Positions are 0-based within a circle.
- The junction darts (block starts) are `P1[0]`, `P1[3k+6]`, `P2[0]` and `P2[3k+4]`.
- The segment table of `power_two_family_symbolic.py` (`SEGS`) lists these words as runs of the
  periodic patterns `A`, `C`, `BBA`, `B`, `b`, `abb`, `c` and `a`, with affine endpoints.

**Step 5: the pairing.** The pairs are given by the following rules, with the parameter in the
range shown:

| rule | pairs | range |
|---|---|---|
| r1 | `P1[k+1+i] <-> P2[4k+4-i]` | `0 <= i <= k-1` |
| r2 | `P1[2k+1] <-> P2[3k+4]` | |
| r3 | `P1[2k+2+i] <-> P2[3k+3-i]` | `0 <= i <= 2` |
| r4 | `P1[2k+5+i] <-> P2[5k+8-i]` | `0 <= i <= k-1` |
| r5 | `P1[3k+5] <-> P2[4k+8]` | |
| r6 | `P1[3k+6+i] <-> P2[4k+7-i]` | `0 <= i <= 2` |
| r7--r10 | `N1[0] <-> P1[3k+9]`, `N1[1] <-> P1[k]`, `N2[0] <-> P2[5k+9]`, `N2[1] <-> P2[3k]` | |
| r11 | `P1[i] <-> P2[1+3i]` | `0 <= i <= k-1` |
| r12 | `P1[3k+11+3j] <-> P2[5k+10+j]` | `0 <= j <= k-1` |
| r14 | `P1[3k+9+3j] <-> P2[3k+2-3j]` | `1 <= j <= k-1` |
| r15 | `P1[3k+10+3j] <-> P2[3k-3-3j]` | `0 <= j <= k-1` |
| r16 | `P1[6k+9] <-> P2[2]` | |

(`power_two_family_certificates.py` lists the `j = 0` case of r15 separately, as r13.) The rules
define `6k + 12` pairs. Step 7 shows that every dart lies in some rule domain. Since there are
`12k + 24` darts, the domains are then pairwise disjoint, and `p` is a well-defined involution.
Every rule joins two different circles, so `p` has no fixed point, and no rule joins two minus
darts.

**Step 6: vertex templates.** Each template lists darts in `sigma` order:

| template | darts | parameter | labels |
|---|---|---|---|
| T1 | `P1[k+2+i], P2[4k+4-i]` | `0 <= i <= k-2` | `Aa` |
| T2--T5 | `P1[2k+1+s], P2[3k+5-s]` | `s = 0, 1, 2, 3` | `Ca, Bc, Bb, Ab` |
| T6 | `P1[2k+6+i], P2[5k+8-i]` | `0 <= i <= k-2` | `Aa` |
| T7--T10 | `P1[3k+5+s], P2[4k+9-s]` | `s = 0, 1, 2, 3` | `Ca, Bc, Bb, Ab` |
| T11 | `P1[0], P2[2]` | | `Ab` |
| T12 | `P1[6k+8], P2[0]` | | `Ab` |
| Q1 | `N1[0], P1[3k+10], P2[3k-2], P1[k]` | | `bBaC` |
| Q2 | `N1[1], P1[k+1], P2[4k+5], P1[3k+9]` | | `cAaB` |
| Q3 | `P1[i], P2[3i+2], P1[6k+10-3i], P2[3i-2]` | `1 <= i <= k-1` | `AbBa` |
| Q4 | `P1[2k+5], P2[5k+9], N2[1], P2[3k+1]` | | `AcBa` |
| Q5 | `P1[3k+11+3j], P2[5k+11+j], P1[3k+15+3j], P2[3k-3-3j]` | `0 <= j <= k-3` | `AaBb` |
| Q5' | `P1[6k+5], P2[6k+9], P1[6k+9], P2[3]` | | `AaBb` |
| Q6 | `P1[3k+12], P2[3k], N2[0], P2[5k+10]` | | `BbCa` |

- Counting parameter values: T1 and T6 give `k - 1` vertices each, T2--T5, T7--T10, T11 and T12
  give 10, so `2k + 8` vertices of valence 2. Q1, Q2, Q4, Q5' and Q6 give 5, Q3 gives `k - 1` and
  Q5 gives `k - 2`, so `2k + 2` vertices of valence 4.
- Total: `V = 4k + 10` and `2(2k + 8) + 4(2k + 2) = 12k + 24` darts.
- The junction darts `P1[0], P2[0], P1[3k+6], P2[3k+4]` lie in T11, T12, T8 and T3, all of valence
  2 and one junction dart each. So (2) and (3) hold.
- The minus darts lie in Q1, Q2, Q4 and Q6, one per vertex. With Step 5, (4) holds.
- In every label word the gates `{a},{b},{c},{A,C},{B}` are pairwise distinct, so (L) holds.

`power_two_family_symbolic.py` checks this table for all `k >= 3` at once. A position is an
affine function `c_0 + c_k k + c_i i` over a region `R = {k >= 3, lo(k) <= i <= hi(k)}`, with
`lo` and `hi` affine and `hi - lo` non-decreasing. `R` is a polyhedron whose vertices are the
corners at `k = 3`, and whose recession cone is spanned by `(1, lo_k)` and `(1, hi_k)`. So an
affine function is `>= 0` on `R` iff it is `>= 0` at those corners and non-decreasing along both
rays. This is checked in exact rationals (`nonneg`), and equalities are checked as two
inequalities. For each template dart the program:

1. finds a rule whose domain contains the dart on all of `R`. The rule's parameter must be an
   integer affine function of `(k, i)`, inside the rule's range on `R`;
2. applies `next` (wrapping when the image is the last position) and checks the next template dart
   on `R`, closing up after the last one;
3. reads the label from a segment that contains the dart on `R`, with matching residue modulo the
   pattern length. It checks that the image dart carries the inverse letter. For image darts the
   region may be split into its first parameter value and the rest;
4. decides junction status: each junction position is either equal to the dart on `R`, or
   separated from it by at least 1 on `R`;
5. asserts (L), (2), (3) and (4) for the template.

It also checks that the template sizes add up to `12k + 24` as an affine function, that the
vertex count is `4k + 10`, and that the rules define `6k + 12` pairs. Output:
`power_two_family_symbolic.log`, ending `SYMBOLIC CERTIFICATE OK`. The same run also checks,
numerically for `3 <= k <= 60`, that the templates are exactly the orbits and cover all darts.

**Step 7: coverage, by hand.** Every dart lies in exactly one template instance. Here `k >= 3`.

- `N1[0], N1[1]`: Q1, Q2. `N2[0], N2[1]`: Q6, Q4.
- `P1[0..3k+10]`:
  - `[0]` T11;
  - `[1..k-1]` Q3;
  - `[k]` Q1, `[k+1]` Q2;
  - `[k+2..2k]` T1;
  - `[2k+1..2k+4]` T2--T5;
  - `[2k+5]` Q4;
  - `[2k+6..3k+4]` T6;
  - `[3k+5..3k+8]` T7--T10;
  - `[3k+9]` Q2, `[3k+10]` Q1.
- `P1[3k+11..6k+9]`, by residue:
  - `3k+11+3j`, `0 <= j <= k-1`: Q5 (`j <= k-3`), Q5' (`6k+5`), T12 (`6k+8`);
  - `3k+12+3j`, `0 <= j <= k-1`: Q6 (`3k+12`), Q5 third dart (`3k+15..6k+6`), Q5' (`6k+9`);
  - `3k+13+3j`, `0 <= j <= k-2`: Q3 third dart `6k+10-3i` (`i = k-1-j`).
- `P2[0..3k]`, by residue:
  - `0 mod 3`: `0` T12, `3` Q5', `6..3k-3` Q5 fourth dart, `3k` Q6;
  - `1 mod 3`: `1..3k-5` Q3 fourth dart, `3k-2` Q1;
  - `2 mod 3`: `2` T11, `5..3k-1` Q3 second dart.
- `P2[3k+1..6k+9]`:
  - `[3k+1]` Q4;
  - `[3k+2..3k+5]` T5--T2;
  - `[3k+6..4k+4]` T1;
  - `[4k+5]` Q2;
  - `[4k+6..4k+9]` T10--T7;
  - `[4k+10..5k+8]` T6;
  - `[5k+9]` Q4, `[5k+10]` Q6;
  - `[5k+11..6k+8]` Q5 second dart, `[6k+9]` Q5'.

So the union of the template instances is all `12k + 24` darts. Each instance is a `sigma`-cycle
(Step 6), and the instance sizes add up to `12k + 24`. So the instances are pairwise disjoint and
are exactly the vertices of `X_k`. In particular every dart lies in a rule domain, which completes
Step 5.

**Step 8: small k, and an independent check.** For `k = 1, 2` the template ranges degenerate, so
`power_two_family_certificates.py` builds the certificate from the rules and runs `verify_surface.py`.
It runs for every `1 <= k <= 200`, and checks:

- the explicit inverse and the closed form of `chi_k`;
- `M^3 > 0`, (L), (2), (3) and (4);
- connectivity;
- `chi = -2(k+1)`, genus `k + 2`, and `2k + 2` vertices of valence 4.

Result: `200 of 200 certificates OK`.

**Step 9: conclusion.**

- `X_k` is connected, because r1 joins P1 to P2, r7 joins N1 to P1 and r9 joins N2 to P2.
- `V = 4k + 10` and `E = 6k + 12`, so `chi(X_k) = -2k - 2`.
- By the criterion applied to `f^2`, `S*_{f^2}(X_k)` is `pi_1`-injective in the mapping torus of
  `f^2`. Its fundamental group is `<F, t^2>`, of index 2 in `G_k`.
- The boundary circles are glued in pairs with opposite orientations, so the surface is closed and
  orientable, with `chi = -2k - 2`, that is genus `k + 2`.

**Step 10: power one.** `power_two_family_m1_lp.py` runs the word-free LP of
`legal-folded-certificates-at-power-one-census` (`lp_allwords.py`) on `f_k` at `m = 1`. For
`2 <= k <= 30` it is infeasible, with an exact integer Farkas vector. By part 1 of that node, no
legal `f_k`-folded fatgraph exists. `QED`
