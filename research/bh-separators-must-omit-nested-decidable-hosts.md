---
rg: 2
id: bh-separators-must-omit-nested-decidable-hosts
kind: claim
title: A property separating Boone–Higman must omit a simple Kazhdan group with solvable word problem inside a finitely presented group with solvable word problem, and the only hereditary decision-problem separators are word-problem complexity bounds
requires:
  - hereditary-approximation-disproofs-of-boone-higman
  - fg-groups-have-simple-kazhdan-hosts-of-same-wp-degree
  - clapham-fp-embedding-preserves-word-problem
  - complexity-bounded-host-classes-are-not-universal
  - fp-simple-groups-with-arbitrarily-complex-word-problem
  - simple-envelope-forces-solvable-word-problem
  - odometer-2v-is-fp-simple-and-contains-bs12
distinct_from:
  hereditary-approximation-disproofs-of-boone-higman: that sets up separation and kills approximation properties (sofic, MF); this adds the host-transfer constraint on every separator and kills the hereditary decision-problem properties stronger than solvable word problem, leaving complexity bounds.
  fp-simple-groups-with-arbitrarily-complex-word-problem: that is the complexity consequence of Boone–Higman as an open root; this places it as the unique surviving decision-problem separator and shows Kuznetsov-profile bounds reduce to it.
---

**ESTABLISHED** (lane proof, elementary; inputs cited below; not independently
reviewed). No priority claimed.

Setting: `P` is a class of groups closed under isomorphism and subgroups. As in
`hereditary-approximation-disproofs-of-boone-higman`, `P` **separates**
Boone–Higman if (S1) every finitely presented simple group lies in `P` and (S2)
some finitely generated group with solvable word problem does not. By that node,
a separation is exactly a disproof of `boone-higman-conjecture`.

## 1. Host transfer (every separator sees finite presentation and simplicity together)

If `P` separates, there are groups `K <= C` with

- `K` infinite, finitely generated, simple, with property (T) and FA, and solvable word problem;
- `C` finitely presented with solvable word problem;
- `K ∉ P` and `C ∉ P`.

*Proof.* Take `G ∉ P` from (S2). By `fg-groups-have-simple-kazhdan-hosts-of-same-wp-degree`,
`G <= K` with `K` as stated and `WP(K) <=_T WP(G)`, so `WP(K)` is solvable. By
`clapham-fp-embedding-preserves-word-problem`, `K <= C` with `C` finitely presented and
`WP(C)` solvable. If `K` or `C` lay in `P`, so would `G`. `∎`

So a separator contains every group that is finitely presented **and** simple, but
omits a simple decidable group and a finitely presented decidable group from one
nested pair. No property that holds for all finitely presented groups with solvable
word problem, or for all finitely generated simple (even Kazhdan) groups with
solvable word problem, can separate.

## 2. Hereditary decision problems beyond the word problem do not separate

Each class below is closed under subgroups: a decision procedure for a finitely
generated `S` restricts to its finitely generated subgroups by rewriting generators.
Each fails (S1), witnessed by one finitely presented simple group.

| class `P`: every finitely generated subgroup has … | fails (S1) at | source |
|---|---|---|
| decidable torsion problem (is `g` of finite order?) | `2V` | Belk–Bleak, arXiv:1405.0982, abstract (read 2026-09-18): "the torsion problem for elements of the Brin–Thompson group 2V is undecidable"; `2V` is finitely presented and simple (Brin 2004, 2005; not re-read) |
| decidable membership in its finitely generated subgroups | `V` | `V×V <= V` (commuting copies supported on the halves `0C`, `1C`), `F_2 <= V`, and Mihailova (1958): `F_2 × F_2` has a finitely generated subgroup with undecidable membership (classical, not re-read) |
| solvable conjugacy problem | `V` | `F_2 × F_2 <= V` as above; C. F. Miller III (1971): `F_2 × F_2` has finitely generated subgroups with unsolvable conjugacy problem (classical, not re-read) |

Plain "solvable conjugacy problem" is not subgroup-closed, so only the hereditary
form is a candidate, and it dies at `V`. A Turing-degree invariant cannot separate
either: every finitely presented simple group and every input has degree `0`
(`simple-envelope-forces-solvable-word-problem`).

## 3. What survives among decision problems: complexity bounds, and nothing else of Kuznetsov type

For recursive `T`, let `P_T` be the class of groups all of whose finitely generated
subgroups have a word-problem algorithm within `C·T(C·l) + C·l + C` for some finite
generating set and constant `C`. It is subgroup-closed (rewriting multiplies length by
a constant), and (S2) holds for every `T` by
`complexity-bounded-host-classes-are-not-universal`. Hence:

**`P_T` separates Boone–Higman iff every finitely presented simple group meets the bound
`T`**, i.e. iff the `T`-instance of `fp-simple-groups-with-arbitrarily-complex-word-problem`
fails. That root is OPEN. Zaremsky, arXiv:2305.15176v2 (read 2026-09-18), p. 3, expects it
to hold ("a priori there is not any reason to doubt that arbitrarily large, recursive Dehn
functions are possible"); the only superpolynomial Dehn lower bounds known are his at least
exponential examples (p. 1–2), and the hardest known word problem is coNP-complete
(`nV`, Birget arXiv:1902.03852).

**Kuznetsov-profile bounds reduce to `P_T`.** For a finitely presented simple
`S = <X | R>` and a fixed generator `x ≠ 1`, put
- `δ_S(n)`, the Dehn function;
- `ν_S(n) = max` over `1 ≠ w`, `|w| <= n`, of the least `N` such that
  `x = Π_(i<=k) u_i w^(±1) u_i^(-1)` holds with `k, |u_i| <= N` and the resulting relator has
  area at most `N`.

Both are finite, since `x ∈ <<w>>`. Kuznetsov's two searches halt on input `w` of length `n`
within a recursive function `Φ(n, δ_S(n), ν_S(n))`. Van Kampen diagrams of area `<= δ` have
diameter `<= n + K·δ`, so conjugators are bounded and the search is finite. So any hereditary
class defined by bounds `δ_S, ν_S <= F` for a recursive `F` lies inside `P_T` with
`T(n) = Φ(n, F(n), F(n))`, and it separates only if `P_T` does. A separation through the
Kuznetsov algorithm is therefore a separation through word-problem complexity.

## 4. Where a refutation could still come from

A disproof must supply a subgroup-closed `P` that contains every finitely presented simple
group, including:
- the nonsofic `L^x` (`fp-simple-nonsofic-group`);
- `2V`, with undecidable torsion problem;
- `V`, with Mihailova and Miller subgroups;
- groups containing `BS(1,2)`, with exponentially distorted cyclic subgroups
  (`odometer-2v-is-fp-simple-and-contains-bs12`);
- groups containing Kazhdan `GL_n(Z)`, `n >= 3` (Scott 1984; not re-read);
- groups containing the Grigorchuk group (Röver 1999; not re-read).

It must also omit a nested pair `K <= C` as in §1. The candidates left are:
1. complexity bounds (§3), where the open side is
   `fp-simple-groups-with-arbitrarily-complex-word-problem` and is expected false;
2. approximation properties not known to force soficity, with open sides (H1)/(H2) of
   `hereditary-approximation-disproofs-of-boone-higman`;
3. a genuinely new invariant. It must use finite presentation and simplicity jointly in a way
   that is not a function of the Kuznetsov profile. No candidate is known.

This bounds the red-team side. It does not refute Boone–Higman, and it does not decide it.
