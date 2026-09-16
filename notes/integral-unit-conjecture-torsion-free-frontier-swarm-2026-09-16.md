# Frontier swarm note: integral-unit-conjecture-torsion-free (2026-09-16)

Agent: `hi-fron-integral-unit-conjecture-torsi`. Angle: FRONTIER, which means
mapping the open holes under the root and attacking the one with the best
leverage and tractability.

## 1. Angle and choice of hole

The root `integral-unit-conjecture-torsion-free` (Higman's integral unit
conjecture over `Z`) has one real open hole in the graph, the root itself.

The recorded attacks on it all concentrate on the Promislow group `P`, through:
- the mod-2 dichotomy;
- the fixed-inverse-support ansatz;
- the kernels of definite shadows.

The other branches either are established literature imports or reduce the
group quantifier to fixed test groups, which does not simplify the statement.

I did not attack `Z[P]` directly, since that front is already heavily worked.
Instead I asked where a counterexample must live: which groups can the
elementary unique-product arguments rule out, and what is left over?

The answer is the reduction below. It concentrates the root on finitely
generated torsion-free groups with no nontrivial homomorphism to a group with
unique products (UP). I call these groups UP-null and the class `T_UP`. I
recorded it as a new hole with an honest statement of what it does not do.

## 2. State of the art (sources)

- **Gardam, arXiv:2102.11818 and arXiv:2312.05240v2**, via graph nodes
  `unit-conjecture-fails-over-complex-numbers` and
  `gardam-complex-units-citation`.
  - The Promislow group `P` is torsion-free, and `F_2[P]` has nontrivial units
    (Gardam 2021).
  - `C[P]` has nontrivial units, with coefficients in `Z[zeta_8]`; see the
    Corollary recorded in `gardam-complex-units-citation`.
  - The question over `Z` and `Q` remains open.
  - I did not re-fetch these papers this session and relied on the graph
    nodes.
- **Gardam, "Group rings of infinite groups", Bonn lecture notes, winter
  semester 2023/2024 (groig.pdf).** I read the extracted text for:
  - Remark 1.8 (locality);
  - Prop 1.9 and Thm 1.10;
  - Prop 1.20 (Strojnowski: UP implies two unique products);
  - Cor 1.21;
  - Prop 1.24 (left-orderable implies UP);
  - Thm 1.29, Cor 1.31 and Example 1.32.

  I used these as background. The artifact reproves everything it uses except
  Connell's theorem.
- **Connell, "On the Group Ring", Canad. J. Math. 15 (1963) 650-685, Thm 8.**
  `R[G]` is prime iff `R` is prime and `G` has no nontrivial finite normal
  subgroup. It was used via the graph node
  `connell-group-ring-primality-citation`; I did not read the paper.
- **Oinert, arXiv:1904.04847** (v1 9 Apr 2019, v2 2 May 2019, v3 20 Jul 2023),
  on units and zero divisors of group rings of extensions by UP groups.
  - I read the abstract only; the DOI page 10.1515/jgth-2023-0110 returned 405.
  - The extension-by-UP-quotient idea it describes is subsumed by the reduction
    here. No theorem numbers are cited.
- **Tarizadeh, arXiv:2309.02880** (v1 6 Sep 2023, v3 16 Jul 2025): abstract
  only, background on unit and zero-divisor questions in group rings. Not used
  in proofs.
- **Garg-Mineyev, arXiv:2501.07646** (v1 13 Jan 2025, v2 8 Sep 2025): abstract
  only, not used.
- **Tabei, arXiv:2608.02982v1**, via the root node: not re-fetched.

The web-search budget was exhausted during this session, so I did no further
literature search. I found no source recording the specific reduction to
UP-null groups in this form. I claim no novelty, because the
component-along-a-quotient argument is standard (compare Oinert's abstract).

## 3. What was proven

Full proofs are in
`research/artifacts/up-quotient-unit-reduction-2026-09-16.md`.

**Definitions.**
- A group `K` is *UP-null* if every homomorphism from `K` to a group with
  unique products is trivial.
- `T_UP` is the class of finitely generated, torsion-free, UP-null groups.

**Theorem (artifact, Section 4).** Let `R` be an integral domain. Suppose
that for every `K` in `T_UP`, every unit of `R[K]` is `lambda k`, with
`lambda` a unit of `R` and `k in K`. Then for every torsion-free group `G`:
- `R[G]` has no zero divisors;
- every unit of `R[G]` is trivial.

The proof uses Connell's primality theorem once, over `Frac(R)`. The proof:
- **Lemma 1, components along a homomorphism.** For `phi: K -> M` and
  `x, y in R[K]`, `(xy)_(q)` is the sum of `x_(a) y_(b)` over `ab = q`.
- **Lemma 2, Strojnowski.** In a UP group, if `|A||B| >= 2`, then `AB` has at
  least two unique products. The artifact gives a full proof.
- **Lemma 3, zero divisors.** Take a support-minimal zero-divisor pair and
  translate both supports to contain `1`. The group they generate is in
  `T_UP`: a nontrivial UP quotient would give a unique product, whose
  component factorizes as a smaller zero-divisor pair.
- **Lemma 4, zero divisor gives a unit.** Let `xy = 0` in `R[K]` with `K`
  torsion-free. By Connell, `Frac(R)[K]` is prime, so some `gamma = y k x` is
  nonzero. Then `gamma^2 = 0`, and `1 + gamma` is a nontrivial unit of `R[K]`.
- **Lemma 5, normalized units.** If `R[G]` is a domain and `u v = 1` with
  `1 in supp u`, then `<supp u ∪ supp v>` is in `T_UP`.
- **Lemma 6 (new in the artifact, Connell-free).** A UP group has no zero
  divisors and only trivial units over any integral domain. It follows from
  Lemmas 2, 3 and 5 by minimal support.

**Corollary, the route.** With `R = Z`, the new hole plus
`connell-group-ring-primality` implies the root. This is the route
`integral-unit-conjecture-from-no-up-quotient-case`.

The converse is trivial, since the hole is a special case of the root. So the
new hole is equivalent in truth value to the root. I did not add a converse
route, because it would create a cycle.

**Proposition 5.2, honest limitation.** A torsion-free group has unique
products iff it has no nontrivial finitely generated UP-null subgroup. So the
reduction proves the conjecture unconditionally on no group outside the UP
groups. Its content is structural: every counterexample lives on an explicit
UP-null group generated by supports.

**Proposition 5.3, `P` is in `T_UP`.** This is the claim
`promislow-group-has-no-unique-product-quotient`, proved by route
`promislow-no-up-quotient-from-complex-units`. It needs only that `P` is
torsion-free and that `C[P]` has a nontrivial unit
(`unit-conjecture-fails-over-complex-numbers`).
- **`P` is not UP.** This is Lemma 6 with `R = C`.
- **The finite-index abelian subgroup.** From the relators, `x = a^2`,
  `y = b^2` and `z = (ab)^2` pairwise commute. `L = <x, y, z>` is normal of
  index at most 4, and the conjugation sign patterns are `+--`, `-+-`, `--+`.
- **Homomorphisms to a UP group `M`.** Let `N` be the kernel.
  - If `N ∩ L = 1`, then `N` is finite, hence trivial. So `P` embeds in `M`
    and is UP, a contradiction.
  - Otherwise `N` contains `x^(2i)`, `y^(2j)` or `z^(2k)` for some nonzero
    exponent. By torsion-freeness of `M`, `phi(x)`, `phi(y)` or `phi(z)` is
    trivial, and the relators then force `phi` to be trivial.

**Consequences recorded in the artifact.**
- **Nothing is removed on `P`.** The reduction does not simplify `Z[P]`.
- **`T_UP` is not closed under finite index.** `L` maps onto `Z`, and no
  translate of a nontrivial unit of `C[P]` lies in `C[L]`.
- **The complex analogue of the hole is false.** `P` is in `T_UP` and `C[P]`
  has nontrivial units.
- **Other coefficient rings.**
  - Over `R = Q` the Theorem applies as stated.
  - Over `F_2` and over `C` the hypothesis fails already on `P`, so the
    Theorem is vacuous there.

**Experiment (consistency check only).**
`experiments/up-quotient-unit-reduction-2026-09-16/promislow_affine_action.py`
checks, in exact rational arithmetic:
- the relators in the affine model `a(v) = diag(1,-1,-1) v + (1/2,1/2,0)`,
  `b(v) = diag(-1,1,-1) v + (0,1/2,1/2)`;
- the translations `x, y, z` by `e1`, `e2`, `-e3`;
- the conjugation sign table.

The log ends "ALL CHECKS PASS: True". No proof depends on it.

## 4. Approaches tried and where each dies

(to be filled)

## 5. What to try next

(to be filled)

## 6. Files

(to be filled)
