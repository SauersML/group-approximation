# Zaremsky Problem 1.13: is Σ^∞(G) open? Part 1: necessary shape, known computations, mechanisms

Lane z1-13-sigma-inf, 2026-09-13. Root: `zaremsky-1-13-sigma-infinity-is-open`.

Problem 1.13 verbatim (Zaremsky, *Some open problems*, July 12, 2026): "Every Σ^n(G) is an
open subset of the character sphere Σ(G), but what about Σ^∞(G)? Must that be open?"

## 1. What a counterexample must look like (established on main)

- `non-open-sigma-infinity-needs-unbounded-sigma-depth`: with depth
  `δ(ψ) = min{n : ψ ∉ Σ^n(G)}`, `Σ^∞(G)` fails to be open at `χ` iff characters of finite depth
  accumulate at `χ`, and then their depths tend to infinity. Stabilizing invariants give an open
  `Σ^∞(G)`.
- `bnsr-invariants-stabilize-at-cohomological-dimension`: a group of type `F_∞` with `cd G = d < ∞`
  has `Σ^m(G;Z) = Σ^d(G;Z)` for `m ≥ d` and `Σ^m(G) = Σ^{max(d,2)}(G)` for `m ≥ max(d,2)`. Proof:
  Novikov–Sikorav homology characterizes `Σ^q(G;Z)` in degrees `≤ q` (Suciu arXiv:2010.07499,
  abstract), it is `Tor^{ZG}_i(\widehat{ZG}_{-χ}, Z)`, which vanishes above `d`; then
  `Σ^n(G) = Σ^2(G) ∩ Σ^n(G;Z)` (eq. (2.1) of arXiv:2309.12213). For type F this is recorded by
  Ershov–Zaremsky (arXiv:2505.18826 §2.1): "Note that if G is of type F with a finite classifying
  space of dimension n, then Σ^n(G) = Σ^∞(G) (for example this follows from [Zar17, Citation
  1.5])." So a counterexample has infinite cohomological dimension.

## 2. Every computed Σ-sequence of an infinite-dimensional F_∞ group stabilizes

Sources read on 2026-09-13 (arXiv abstract pages, or the first pages of the PDF where marked).
The search was bounded: Zaremsky's arXiv author listing, the arXiv full-text search "BNSR
invariants" (17 results, 2015–2026), and the papers below. No paper found states that `Σ^∞` of
some group is not open, or exhibits infinitely many distinct invariants for one group of type
`F_∞`.

| Group | Type | Result | Source |
|---|---|---|---|
| Thompson's F | F_∞, infinite cd | "[χ] is in Σ^2(F) = Σ^∞(F) unless a ≥ 0 and b ≥ 0" | Bieri–Geoghegan–Kochloukova 2010, as Theorem A of Witzel–Zaremsky arXiv:1501.06682 (PDF p. 1) |
| F_{n,∞} (n ≥ 2) | F_∞ | "For any n, m ≥ 2, we have Σ^m(F_n) = Σ^2(F_n)." | Zaremsky arXiv:1502.02620, Theorem A (PDF p. 2) |
| golden-mean F_τ | F_∞ | Σ^∞(F_τ) = Σ^∞(F_τ,Z) = Σ^2(F_τ) (Theorem 1.1) | Molyneux–Nucinkis–Santos Rego arXiv:2309.12213 (HTML, via extraction; recheck wording) |
| Lodha–Moore groups | F_∞ | complete computation; abstract: every finitely presented normal subgroup is of type F_∞ | Lodha–Zaremsky arXiv:2007.12518 (abstract) |
| Stein F_{2,3} | F_∞ | abstract: "every discrete character lies in Σ^∞(F_{2,3}), but there exist (non-discrete) characters that do not even lie in Σ^1(F_{2,3})" | Spahn–Zaremsky arXiv:2012.05000 (abstract) |
| pure braid P_n | F, finite-dim | inclusions proper for 3 ≤ m ≤ n but "Σ^∞(P_n)=Σ^{n-2}(P_n)" | Zaremsky arXiv:1507.08597 (abstract) |
| McCool groups | F, finite-dim | every Σ^m dense or empty | Ershov–Zaremsky arXiv:2505.18826 (abstract) |
| Houghton H_n | F_{n−1}, not F_n | full computation; Σ^∞ undefined | Zaremsky arXiv:1808.00634 |
| RAAGs, products of free groups | F, finite-dim | stabilize at the dimension | Bux–Gonzalez; Meier–Meinert–VanWyk |

For Lodha–Moore and F_{2,3} the abstracts do not say in words that `Σ^m = Σ^2` for all `m ≥ 2`;
read the theorems before citing stabilization for them. The Stein group is the one known case
where membership depends on arithmetic (discrete versus non-discrete characters); see §3 (M3).

## 3. Mechanisms, and where each stands

- **(M1) Products do not help.** Over a field `K` the product formula of Bieri–Geoghegan gives
  `Σ^m(A×B;K)^c = ∪_{p+q=m} Σ^p(A;K)^c * Σ^q(B;K)^c` (join in `S(A×B) = S(A)*S(B)`). Reading it on a
  join point `ψ = cosθ·α + sinθ·β` (0 < θ < π/2) gives additivity of depth,
  `δ_{A×B}(ψ) = δ_A(α) + δ_B(β)`, and `δ_{A×B}(α) = δ_A(α)` on `S(A)`. A finite-depth sequence
  accumulating at a point of infinite depth therefore already exists in a factor. Products of groups
  whose invariants stabilize have stabilizing invariants (over fields; the homotopical product
  formula is only an inclusion in general).
- **(M2) Two-ended Thompson-like groups saturate at m = 2.** In F, F_{n,∞} and F_τ the characters
  outside `Σ^1` are the two end germs (log-slope at 0 and at 1), and `Σ^2^c` is their spherical
  convex hull; nothing new appears at higher m. Any group whose bad characters come from boundedly
  many independent "ends" with convex-hull growth stabilizes by Carathéodory in `S(G)`.
- **(M3) Arithmetic depth: a consistent shape for "no".** Nothing in the openness theorems forbids
  a group with a circle of characters where rational directions of height h have finite depth
  `f(h) → ∞` and irrational directions lie in `Σ^∞`: each `{δ ≤ m}` would be a finite set (closed),
  each `Σ^m` open, and `Σ^∞` not open at any irrational point. F_{2,3} shows membership can depend
  on discreteness, with the opposite polarity (discrete characters all in Σ^∞).
- **(M4) Tropical upper bounds.** `Σ^m(G;Z)` avoids the tropicalizations of the homology jump loci
  in degrees ≤ m (Papadima–Suciu; Suciu arXiv:2010.07499; Liu–Suciu arXiv:2605.28595, twisted
  version). These are rational polyhedral sets. A group of type `F_∞` whose degree-k jump loci were
  subtori of slopes accumulating at an irrational slope has upper bounds whose union is not closed;
  a matching lower bound on `Σ^m` would answer Problem 1.13 negatively. Unexplored.
- **(M5) Pure braided Thompson groups (Problem 2.13).** They are of type F_∞ and contain every pure
  braid group P_n, whose invariants separate up to index n−2 (arXiv:1507.08597). If characters of
  the pure braided group restrict to vertex stabilizers P_n with depth growing in n but bounded on
  the relevant descending links, the invariants need not stabilize. Unexplored; shared with lane
  z2-13-pure-braided-bht.

## 4. Next steps for this lane

1. (M4)/(M3): look for an F_∞ group with character sphere S^1 and infinitely many distinct
   rational bad directions (Stein-type groups with slope groups of rank 2 and Houghton-type ends).
2. (M5): compute characters of pure braided F and their restrictions to P_n stabilizers.
3. A positive theorem for groups acting on CAT(0) cube complexes with finitely many end germs.
