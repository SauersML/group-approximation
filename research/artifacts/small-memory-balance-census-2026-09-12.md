# Small-memory census of unbalanced rules

Lane `w4-bal-census`, 2026-09-12. Handwritten, nothing was run. Supports
`binary-unbalanced-rules-on-sidon-memory-are-not-pre-injective` and
`binary-three-address-injective-automata-have-balanced-rules`, and records where
`every-injective-ca-has-uniform-single-site-output-law` is still open for small memory.

Every exclusion here uses the group law pointwise. It builds two configurations that differ at
one or two sites and have equal images. The only thing it has to avoid is a finite list of
relations among short words in the memory elements, and each such relation is either absorbed by
a second construction or makes the memory group amenable. No fibre counts are used. That matters
because numeric window relations (translation totals, decoder decay) are satisfiable by
unbalanced measures on nonamenable groups, and a finite decoder identity with local counting also
holds on the end-fixing tree.

## 1. Conventions and reductions

- `tau(x)(g) = mu((x(g m))_(m in M))`, with `M` a finite subset of `G`, `mu : A^M -> A`, and
  `q = |A|`. The rule `mu` is **balanced** if every symbol has exactly `q^(|M|-1)` preimages.
- Under uniform input the single-site output law of `tau` is `mu` applied to independent uniform
  symbols, with `M` a set of distinct elements. A bijective automaton preserves the uniform
  measure (`bijective-ca-preserve-uniform-bernoulli-measure`), so a bijective `tau` has a
  balanced rule.
- **(R1) Collisions and unread addresses.** A realization with colliding addresses is a rule on
  fewer distinct elements. Dropping an unread coordinate multiplies every preimage count by `q`,
  so it keeps the balance status.
- **(R2) Translation.** Memory `gM` with the same rule is `tau` followed by the bijective automaton
  `y -> y(. g)`. So WLOG `1 in M`.
- **(R3) Restriction.** `A^G` is the product of `A^(kH)` over left cosets of `H = <M>`, and `tau`
  acts coset by coset as the same automaton over `H`. So `tau` is injective, or pre-injective,
  over `G` iff it is over `H`.
- **(R4) Symmetries.** Permuting addresses, precomposing with a global symbol permutation
  `x -> pi o x`, and postcomposing with a symbol permutation preserve injectivity,
  pre-injectivity and balance. Negating single coordinates is NOT a symmetry.
- **(R5) Amenable memory groups.** If `<M>` is amenable, then an injective `tau` is surjective
  (Gromov–Weiss, since amenable groups are sofic), hence bijective, hence balanced. This is used
  for cyclic, dihedral and abelian `<M>`.
- **Flips.** For `q = 2`, flipping `x` at `h` changes only the patterns at the sites `h m^-1`
  (`m in M`). At `h m^-1` coordinate `m` reads `x(h)`, and coordinate `m' != m` reads
  `x(h m^-1 m')`. Coordinate `m` of `mu` is **blind** at a pattern `r` on `M \ {m}` if
  `mu(0, r) = mu(1, r)`.

## 2. Two addresses

**Theorem 2.1.** For every alphabet and every group, an injective automaton with `|M| <= 2` has a
balanced rule.

*Proof.* By (R2) `M = {1, a}`, so `<M>` is cyclic, and (R5) applies. QED

## 3. Sidon memory over the binary alphabet

**Definition.** `M` is **Sidon in `G`** if the elements `m^-1 m'` (`m, m' in M`, `m != m'`) are
distinct for distinct ordered pairs. This is invariant under left translation of `M`. A
three-element `{1, a, b}` is Sidon in the free group on `a, b`. `{1, a, b, ab}` is Sidon in no
group, since `a^-1 (ab) = b = 1^-1 b`.

**Lemma 3.1.** Let `q = 2` and `mu` unbalanced. Then every coordinate `m` is blind at some pattern
`r_m` on `M \ {m}`.

*Proof.* Otherwise `mu(0, r) != mu(1, r)` for every `r`, so `mu(x) = x_m + mu(0, x|_(M \ {m}))`
mod 2. Each `r` then contributes exactly one preimage of `1`, and there are `2^(|M|-1)` of them. QED

**Theorem 3.2.** Let `q = 2`, `mu` unbalanced, and `M` Sidon in `G`. Then `tau` is not
pre-injective, so it is not injective.

*Proof.* Fix `h`. The sites `h m^-1 m'` with `m != m'` are pairwise distinct by the Sidon
property, and none equals `h`. Take any `x` with `x(h m^-1 m') = r_m(m')` for all such pairs, and
let `x'` be `x` flipped at `h`. The sites reading `x(h)` are the `h m^-1`. At `h m^-1` the other
coordinates read `r_m`, where coordinate `m` is blind. So `tau(x) = tau(x')`, and
`x`, `x'` differ at one site. QED

**Corollary 3.3.** A binary injective automaton with an unbalanced rule has a relation
`m^-1 m' = n^-1 n'` with `(m, m') != (n, n')`, `m != m'`, `n != n'` among its memory elements.
For a design with a forward-sufficient table `E`, the relation must hold in `U_E`, even when the
memory letters `1, x_m` are distinct there. Distinct letters are the case in which
`unbalanced-effective-rule-certifies-strictness` makes `U_E` non-surjunctive. So a binary refuting
design needs a relator of length at most four of this shape among its memory letters.

**Remark 3.4 (larger alphabets).** For `q >= 3` the same argument gives each coordinate a blind
*pair* `{c, d}`: some rest pattern at which `x_m -> mu` is not injective. If no coordinate had one,
`mu` would be a permutation in each fixed coordinate direction and hence balanced. But a
single-site change `c -> d` needs one pair that works for all coordinates at once, and the pairs
need not agree.
- **Example.** Over `F_3`, take `L(x, y, z) = x + y + z` and change the value at `(0, 1, 2)` from `0`
  to `1`.
- **Blind pairs.** Coordinate `x` is blind only for `{0, 1}`, at `(y, z) = (1, 2)`. Coordinate `y`
  only for `{1, 2}`, at `(x, z) = (0, 2)`. Coordinate `z` only for `{0, 2}`, at `(x, y) = (0, 1)`.
- **Unbalanced.** Symbol `1` has 10 preimages and `0` has 8.
- **Consequence.** No single-site change of any configuration is invisible, over any group. This
  is where the flip method stops (Section 5).
