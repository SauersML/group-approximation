# Thompson's group F: which certificate shapes survive

Lane `thompson-f-amenability`, 2026-09-12. This is the second pass after
`thompson-f-amenability-map-2026-09-12.md`.

**Sources, read from PDFs extracted on MSI:**
- V. Guba, *Amenability problem for Thompson's group F: state of the art*,
  arXiv:2305.07113v4 (J. Groups Complexity Cryptology 15 (2023)), all 24 pages;
- V. Guba, *Systems of equations over the group ring of Thompson's group F*,
  arXiv:2201.02308v1 (Comm. Algebra 2022): abstract, §2 (`Q_k`), §3 (Theorems 2, 3,
  Question 1, Corollary 2);
- V. Guba, *Cayley graphs of R. Thompson's group F: new estimates for the density*,
  arXiv:2210.12304v1: abstract and §1;
- D. Kielak, appendix to Bartholdi, arXiv:1605.09133v2: Theorem A.1 with proof;
- U. Haagerup and K. K. Olesen, arXiv:1609.05086, §4.

## 1. Certificate shapes and where each stands

| Shape | Would prove | Status |
|---|---|---|
| Følner sets | amenable | Explicit families die at every fixed tower (`thompson-f-folner-function-exceeds-every-tower`). Best density in `{x_0, x_1}` is `> 3.5`, against the maximum `4` (arXiv:2210.12304). |
| Closed-walk counts | non-amenable | dead (`thompson-f-moment-data-cannot-certify-nonamenability`) |
| Pure evacuation scheme (capacity 1) | non-amenable | Dead for `{x_0, x_1, x_1 x_0^-1}` and `{x_0, x_1, x_2}`: Cheeger constant `< 1` (survey Thms 2.5, 2.6, 2.8). |
| Evacuation with capacity `C >= 2`, or a bounded flow with inflow `>= epsilon` | non-amenable | open, and equivalent (survey Props 1.3, 2.3, 2.4) |
| Non-Ore pair `a u = b v` | non-amenable | open, and equivalent (Kielak Thm A.1). Excluded: pairs where either side is a unit times a product of twisted binomials `1 + lambda g` with `g` any one-bump element (§2, items 4–5). That covers `1 - x_0`, `1 - x_1`, `x_0 - x_1`, `1 - x_2 x_1^-1`, all their conjugates, and the pairs `(1 - a, 1 - c)`. Also excluded: degree-one homogeneous pairs `P_(1,m)` and `P_(2,1)` (survey Thms 3.10, 3.11, 3.14). |
| Non-Ore system `Q_k` | non-amenable | `Q_3` excluded (survey Cor 3.13). New: every `Q_k` with at most one form `alpha x_0 + beta x_1 + gamma x_2` having all coefficients nonzero, and every `Q_k` over `F_2`. Open: over other fields with at least two full trinomials. Guba names `Q_4` there as a candidate. |
| `(1 - x_1) u = b v` with only zero solutions (survey Q 3.20; arXiv:2201.02308 Question 1) | non-amenable | **dead**, answered positively here (`thompson-f-one-minus-x1-is-ore-with-every-element`) |
| Bounded-coefficient series identity `sum_g g = (1 - x_0) S_1 + (1 - x_1) S_2` | non-amenable | open, and equivalent (survey Thm 3.22) |
| Regular-subword bound on relations (Wajnryb--Witowicz) | non-amenable | open; the withdrawn arXiv attempt was incorrect (survey §4.3(3)) |
| Simplicity of `C*_r(T)` | non-amenable | Haagerup--Olesen Thm 4.5 prove one direction, and they cite Le Boudec--Matte Bon for the converse. Only the Haagerup--Olesen direction was read here. |
| Finitely supported Liouville measure | amenable | dead (`thompson-f-random-walks-are-not-liouville`) |
| Proximal or strong-amenability argument | amenable | dead (`thompson-f-is-not-strongly-amenable`) |

## 2. New unconditional results on this graph

1. **`thompson-f-binomial-pairs-have-common-multiples`.** `(1 - a) R ∩ (1 - c) R ≠ 0` for
   all `a, c ≠ 1`: the Fox gradient of a relator of `<a,c>` is nonzero by Brin--Squier.
   The basic identity used everywhere is `t (1 - t^-1 h t) = (1 - h) t`.
2. **`thompson-f-twisted-x0-binomial-is-ore-with-every-element`.**
   `(1 + lambda x_0) R ∩ b R ≠ 0` for all `lambda ≠ 0` and all `b`. It combines Guba's
   reduction, a coset test weighted at `-1/lambda`, and a dimension count in place of
   Guba's Theorem 3.
3. **`thompson-f-one-minus-x1-is-ore-with-every-element`** answers Question 3.20. Conjugates
   of `x_1` have nested supports `(p, 1)`. Apply Theorem 3.18 inside `F_[p,1]`, innermost
   first.
4. **`thompson-f-rescaled-x0-binomials-have-common-multiples`.** The general statement.
   - *The class.* `O_1` is the set of one-bump elements `g` such that `1 + lambda g` meets
     every principal right ideal of `K[F_[supp g]]`.
   - *Families.* Any finite family of twisted binomials of `O_1` elements, plus one
     arbitrary element, has a nonzero common right multiple. Sort by right endpoint: the
     conjugates of the next bump by the current multiple all share that endpoint, so they
     nest.
   - *Transfer.* Restriction between `K[F]` and `K[F_[p,q]]` uses freeness of `K[F]` over
     `K[F_[p,q]]`.
   - *Members.* `O_1` contains `x_0^{+-1}`, all `x_n^{+-1}`, `x_1 x_0^-1` (bump `(0,3/4)`),
     `x_2 x_1^-1` (bump `(1/2,7/8)`), and all their conjugates. The supports were computed
     exactly in `experiments/thompson-f/pl_check.py`.
   - *Consequences.* Items 1–3 above are special cases, and Guba's `Q_k` holds over `F_2`
     for every `k`.
5. **`thompson-f-one-bump-binomials-have-common-multiples`.** `O_1` is every one-bump
   element, whatever its endpoint slopes, so item 4's families and product statements hold
   for all of them.
   - *Slope `1/2` at `0`.* The weighted coset test absorbs the germ at `0`. Near `1`,
     conjugation by `g` acts as a power `phi^n` of the shift, so Guba's letter-window count
     runs with `phi^n`.
   - *Slope `2^-m` at `0`.* A self-similar conjugacy identifies the index-`m` subgroup
     `{f : m | e(f)}` with `F` and turns that slope into `1/2`. Intersecting over the
     conjugates `t^-1 g t`, `t` in `supp b`, gives the general case.

## 3. Small-degree census over `F_2` (guidance only)

`experiments/thompson-f/ore_census.py` does exact `F_2` linear algebra in the positive
monoid, with homogeneous `u, v` of degree `D` and letters `<= L`. Outputs are in
`experiments/thompson-f/ore_census_small_degrees.jsonl`.
- **`P_(2,2)`:** 130305 unordered pairs from `F_2[S_(3,5)]`.
  - `D = 2, L = 5`: 126144 have no solution.
  - `D = 3, L = 6`: 122745 have no solution.
- **`Q`-type systems:** five of the seven forms, and all seven, have no common multiple
  at `D = 4, L = 7`.
- **Reading.** Over `F_2`, §2 item 4 proves these systems solvable, so their solutions have
  degree `> 4` or letters `> 7`. Small-degree failure carries no information about
  non-Ore witnesses. This matches the tower-size lower bounds.

## 4. The strongest open shapes after this pass

1. **Two genuine trinomials.** A non-Ore witness must have both sides outside the
   `O_1`-product class. The smallest listed candidates are `Q_4` over a field `≠ F_2`
   with at least two forms having all three coefficients nonzero, and generic `P_(2,2)`
   pairs.
2. **Multi-bump elements.** Is `(1 + lambda g) R` Ore against everything when `g` has two
   or more bumps? One-bump elements of every slope are settled (§2 item 5).
   - *Reduction.* By the coset test, `(1 + lambda g) R ∩ b R ≠ 0` whenever some finite
     `S ⊆ F` gives fewer than `|S|` cosets `<g> h s` with `h` in `supp b` and `s` in `S`.
     Each such coset imposes one linear condition on `w = sum_(s in S) c_s s`, so some
     `w ≠ 0` has `b w` in `(1 + lambda g) R`.
   - *Obstacle.* The one-bump proof builds `S` from the shift `phi`. For multi-bump `g`, no
     such `S` is known against `b` whose support moves an interior fixed point of `g`.
3. **Evacuation with capacity 2** on the triple-of-trees fragments `Γ_n` (survey Thm 4.1),
   checked on finite fragments by König.
