# Thompson's group F: which certificate shapes survive

Lane `thompson-f-amenability`, 2026-09-12. This is the second pass after
`thompson-f-amenability-map-2026-09-12.md`. Its sources were read from extracted PDFs on
MSI:

- V. Guba, *Amenability problem for Thompson's group F: state of the art*,
  arXiv:2305.07113v4 (J. Groups Complexity Cryptology 15 (2023)), all 24 pages;
- V. Guba, *Cayley graphs of R. Thompson's group F: new estimates for the density*,
  arXiv:2210.12304v1, abstract and §1;
- D. Kielak, appendix to Bartholdi, arXiv:1605.09133v2, Theorem A.1 with proof;
- U. Haagerup and K. K. Olesen, *Non-inner amenability of the Thompson groups T and V*,
  arXiv:1609.05086, §4.

## 1. The certificate shapes, and where each one currently stands

| Shape | Proves | Status on this graph |
|---|---|---|
| Følner sets | amenable | explicit families die at every fixed tower (`thompson-f-folner-function-exceeds-every-tower`); best density in `{x_0, x_1}` is `> 3.5`, not `4` (Guba, arXiv:2210.12304) |
| Closed-walk counts | non-amenable | dead: no finite list certifies (`thompson-f-moment-data-cannot-certify-nonamenability`) |
| Pure evacuation scheme (flow of capacity 1) | non-amenable | dead for `{x_0, x_1, x_1 x_0^-1}` and `{x_0, x_1, x_2}`: Cheeger constant `< 1` (survey Thms 2.5, 2.6, 2.8) |
| Evacuation scheme with capacity `C >= 2`, bounded flow with inflow `>= epsilon` | non-amenable | open, and equivalent to non-amenability (survey Props 1.3, 2.3) |
| Non-Ore pair `a u = b v` | non-amenable | open, and equivalent (Kielak Thm A.1). Excluded so far: binomial pairs `(1 - a, 1 - c)` and `(1 - h, binomial)` (`thompson-f-binomial-pairs-have-common-multiples`, new here); `(1 - x_0, anything)` (`thompson-f-one-minus-x0-is-ore-with-every-element`, Guba 2022, with an independent counting proof here); homogeneous degree-1 pairs `P_(1,m)` for all `m`; `P_(2,1)` (survey Thms 3.10, 3.11, 3.14) |
| Non-Ore system `Q_k` (`k+1` linear forms in `x_0, x_1, x_2` with no common right multiple) | non-amenable | `Q_3` excluded (survey Cor 3.13, from a set with `|AY| < 4/3 |Y|`); `Q_4` named by Guba as a possible negative candidate |
| `(1 - x_1) u = b v` with only zero solutions | non-amenable | **dead** (new here): survey Question 3.20 has a positive answer. Every `1 - h` with `h` conjugate to `x_0^{+-1}`, `x_1^{+-1}` or `(x_1 x_0^-1)^{+-1}` meets every principal right ideal (`thompson-f-one-minus-x1-is-ore-with-every-element`) |
| System `(1 - g_1) u_1 = ... = (1 - g_m) u_m` with only zero solutions | non-amenable | dead when all `g_i` are conjugates of `x_0^{+-1}` or `x_1^{+-1}` (nested supports; new here, extending survey Cor 3.21). Open for `g_i` with overlapping, non-nested supports |
| Bounded-coefficient series identity `sum_g g = (1 - x_0) S_1 + (1 - x_1) S_2` | non-amenable | open, and equivalent (survey Thm 3.22) |
| Regular-subword bound on relations (Wajnryb--Witowicz) | non-amenable | open; the withdrawn arXiv attempt was incorrect (survey §4.3(3)) |
| Simplicity of `C*_r(T)` | non-amenable | equivalent: Haagerup--Olesen Thm 4.5 give one direction, and they cite Le Boudec--Matte Bon for the converse. Only the Haagerup--Olesen direction was read here |
| Finitely supported Liouville measure | amenable | dead (`thompson-f-random-walks-are-not-liouville`) |
| Proximal-action / strong-amenability argument | amenable | dead (`thompson-f-is-not-strongly-amenable`) |

## 2. The new unconditional results on this graph

1. **Binomial pairs** (`thompson-f-binomial-pairs-have-common-multiples`). For all `a, c`
   in `F \ {1}`, `(1 - a) R ∩ (1 - c) R ≠ 0`.
   - The kernel of the Fox map `(u, v) -> u (a - 1) + v (c - 1)` on `K[<a,c>]^2` is
     `(N/[N,N]) ⊗ K`, where `N` is the relation subgroup. Brin--Squier forces `N ≠ 1`.
   - Corollary: if `v` lies in `(1 - t^-1 h t) R` for every `t` in `supp b`, then `b v`
     lies in `(1 - h) R`. So `1 - h` meets every binomial.
2. **`1 - x_0` against everything, by counting**
   (`thompson-f-one-minus-x0-is-ore-with-every-element-proof`).
   - Normalize `b` modulo `<x_0>` to letters `>= 1`, then shift by conjugation.
   - A linear dependence among `phi^k(b')` gives `b (sum_k x_0^k r_k)` in `(1 - x_0) R`.
   - Counting normal forms of degree `L/2` in the window `[1, L]` gives
     `(N+1) |A| ~ (L/2) |A|` unknowns against at most `(4^(D+1)/3) |A|` constraints.
   - The same argument gives `1 - x_1` against every `b` supported in one right coset of
     `F_[1/2,1]`.

3. **Question 3.20, answered** (`thompson-f-one-minus-x1-is-ore-with-every-element-proof`).
   - Every conjugate of `x_1^{+-1}` has support `(p, 1)` and is the `x_0` of `F_[p,1]`,
     via conjugation plus `y -> 2y - 1`.
   - Ordering a finite family by `p` and applying survey Theorem 3.18 inside `F_[p,1]`,
     innermost first, gives a nonzero common right multiple of all `1 - g_i`.
   - Then `t (1 - t^-1 h t) = (1 - h) t` turns a common multiple of the conjugates
     `t^-1 x_1 t` (`t` in `supp b`) into a nonzero element of `(1 - x_1) R ∩ b R`.
   - The mirror automorphism covers `x_1 x_0^-1`, hence `x_0 - x_1`.

## 3. The strongest open shapes, ranked by how finite the next step is

1. **`1 - h` for `h` with compact or multi-component support.** Example: `h` in `F'`.
   The conjugates have supports `(p, q)` in general position. The induction above needs
   laminar supports (nested or disjoint), and disjoint pieces commute, so laminar
   families of elements that are an `x_0` of their own interval also work. The smallest
   open case is three augmentation binomials whose supports pairwise overlap without
   nesting.
2. **`Q_4` and `P_(2,2)`.** These are finite-dimensional per degree, so exact linear
   algebra over `F_2` is a legitimate census of small degrees. Section 4 records the
   census. A zero census is only guidance, not a non-Ore certificate.
3. **Evacuation with capacity 2.** The Γ_n triple-of-trees fragments (survey Thm 4.1) are
   the natural finite search space. By Prop 2.4 (König), a scheme with constant `C` on
   every fragment suffices.

## 4. Census (pending)

Exact `F_2` linear algebra on MSI (`experiments/thompson-f/ore_census.py`). Results will
be recorded here.
