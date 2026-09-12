# Small-memory census of unbalanced rules

Lane `w4-bal-census`, 2026-09-12. Handwritten, nothing was run. Supports
`binary-unbalanced-rules-on-sidon-memory-are-not-pre-injective` and
`three-address-binary-injective-rules-are-balanced`, and records where
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
- **Example (corrected in the second landing).** Over `F_3`, take `L(x, y, z) = x - y + z` and
  change the value at `(0, 2, 2)` from `0` to `1`. Call the result `R`. Its diagonal is `c -> c`, so
  constant configurations do not collide.
- **Blind pairs.** Coordinate `x` is blind only for `{0, 1}`, at `(y, z) = (2, 2)`. Coordinate `y`
  only for `{1, 2}`, at `(x, z) = (0, 2)`. Coordinate `z` only for `{0, 2}`, at `(x, y) = (0, 2)`.
- **Unbalanced.** Symbol `1` has 10 preimages and `0` has 8.
- **Consequence.** No single-site change of any configuration is invisible, over any group. This
  is where the flip method stops (Section 5).
- **Why the first version was replaced.** The first landing used `x + y + z` patched at `(0, 1, 2)`.
  That rule sends every constant to `0`, so it dies by constant tests and illustrated nothing.

## 4. The binary three-address census

**Theorem 4.1.** Over every group and for every placement of at most three memory elements, an
injective automaton on two symbols has a balanced rule.

*Reductions.* By (R1) and Theorem 2.1 we may assume `M = {1, a, b}` with three distinct elements,
`mu` reads all three coordinates, and `G = <a, b>` (R2, R3). Coordinates `(x, y, z)` read the
addresses `(1, a, b)`. Put `T = mu^-1(1)` and `w = |T|`. By output negation, `w in {1, 2, 3}`.

### Step 1: constant tests, independent of the group

- **(C1) Constants.** `tau` sends the constant `c` to the constant `mu(ccc)`. Injectivity needs
  `mu(000) != mu(111)`. By global negation (R4), `000 in T` and `111` is not in `T`.
- **(C2) One flip of a constant.** Flipping the constant `1` at `h` changes only the sites `h`,
  `h a^-1`, `h b^-1`, and these see `111 - e_m`. The flip is invisible unless `T` contains a
  weight-two vector. Flipping the constant `0` is always visible when `w <= 3`.
- **Survivors,** up to permuting addresses:
  - `w = 1`: none;
  - `w = 2`: `T = {000, 110}`;
  - `w = 3`: `T = {000, 110, q}` with `q in {100, 001, 101}`. The swap `x <-> y` identifies `010`
    with `100`, and `011` with `101`.

### Step 2: flips with prescribed surroundings

A flip at `h` is invisible when three conditions hold:
- the pattern `(., x(ha), x(hb))` at `h` is blind in `x`;
- the pattern `(x(ha^-1), ., x(ha^-1 b))` at `ha^-1` is blind in `y`;
- the pattern `(x(hb^-1), x(hb^-1 a), .)` at `hb^-1` is blind in `z`.

The six words `a, b, a^-1, a^-1 b, b^-1, b^-1 a` are nontrivial. A choice of values is
inconsistent only when a site forced to `0` equals a site forced to `1`, and that is a relation
among these words.

**(2) `T = {000, 110}`.**
- Blind sets: `x` and `y` are blind iff `z = 1`; `z` is blind iff `x != y`.
- Choice: put `x(hb) = x(ha^-1 b) = 1` and `x(hb^-1) != x(hb^-1 a)`.
- Failure: this fails only if both `hb^-1` and `hb^-1 a` lie in `{hb, ha^-1 b}`, that is, if
  `a = b^2`, or `b^2 = 1` and `(b^-1 a)^2 = 1`.
- Amenable: then `<M>` is cyclic, or generated by the involutions `b` and `b^-1 a` and so dihedral.
  (R5) applies.

**(3a) `T = {000, 100, 110}`.**
- Blind sets: `x` is blind iff `(y, z) != (1, 0)`; `y` iff `(x, z) != (0, 0)`; `z` iff
  `(x, y) = (0, 1)`.
- Choice A: `x(ha) = 0`, `x(ha^-1) = 1`, `x(hb^-1) = 0`, `x(hb^-1 a) = 1`. It conflicts only if
  `a^2 = 1`.
- Choice B: `x(hb) = 1`, `x(ha^-1) = 1`, `x(hb^-1) = 0`, `x(hb^-1 a) = 1`. It conflicts only if
  `b^2 = 1`.
- Both fail only if `a^2 = b^2 = 1`, and then the group is dihedral.

**(3b) `T = {000, 110, 001}`.**
- Blind sets: `x` is blind iff `(y, z) = (1, 1)`; `y` iff `(x, z) = (1, 1)`; `z` iff `(x, y) != (1, 1)`.
- Choice: put `x = 1` on `h {a, b, a^-1, a^-1 b}`, and `x = 0` on whichever of `hb^-1`, `hb^-1 a`
  lies outside that set.
- Failure: both lie inside only if `ab = 1`, `a = b^2` or `b = a^2` (all cyclic), or if `b^2 = 1`
  and `(b^-1 a)^2 = 1` (dihedral).

**(3c) `T = {000, 110, 101}`.**
- Blind sets: `x` is blind iff `(y, z) = (1, 1)`; `y` iff `(x, z) = (0, 1)`; `z` iff `(x, y) = (0, 1)`.
- Single flip: it needs `x = 1` on `h {a, b, a^-1 b, b^-1 a}` and `x = 0` on `h {a^-1, b^-1}`. That
  conflicts only if `a^2 = 1`, `b^2 = 1`, `ab = 1`, `b = a^2` or `a = b^2`.
- If `a^2 = b^2 = 1`, the group is dihedral.
- If `a^2 = 1`, flip `h` and `ha` together. The case `b^2 = 1` is the same, because `T` is invariant
  under `y <-> z`.
  - The sites reading `h` or `ha` are `h`, `ha`, `hb^-1` and `hab^-1`.
  - At `h` and `ha` both the `x`- and `y`-coordinates flip. Since `mu(u, v, 0) = [u = v]` is
    invariant under flipping both, put `x(hb) = x(hab) = 0`.
  - At `hb^-1` and `hab^-1` only `z` flips. Put `x(hb^-1) = x(hab^-1) = 0` and
    `x(hb^-1 a) = x(hab^-1 a) = 1`.
  - None of these sites is `h` or `ha`.
  - A 0-site equals a 1-site only if `b^2 = a`, `aba = b^-1` or `ab = ba`. Then `<M>` is cyclic,
    dihedral or abelian.

Every survivor is excluded, and every exclusion either produces two configurations with equal
images or makes `<M>` amenable. QED

**Remarks.**
- **Pre-injectivity.** Outside the listed amenable relation cases, each construction gives two
  configurations that differ at one or two sites. So the automaton is not even pre-injective
  there.
- **Design form.** Suppose a binary three-address design with an unbalanced rule had a
  forward-sufficient `E` whose table group keeps the letters `1, x_a, x_b` distinct. Its
  realization over `U_E` would be injective with an unbalanced rule, contradicting Theorem 4.1. So
  the letters collide. This is the case `q = 2`, `|M| = 3` of
  `unbalanced-forward-tables-identify-memory-letters`.

## 5. Where the method stops

### 5.1 Common blind pairs and affine patches

**Proposition 5.1 (common blind pair).** Let `q >= 3` and let `M` be Sidon in `G`. Suppose some
pair `{c, d}` is a blind pair of every coordinate. Then `tau` is not pre-injective.

*Proof.* As in Theorem 3.2, with `x(h)` changed from `c` to `d`. QED

**Proposition 5.2 (avoidable patches).** Let `A = F_q` with `q >= 3`. Let
`lambda_0(x) = sum_m c_m x_m` be linear and `lambda = lambda_0 + c_0` affine, and let `mu` agree
with `lambda` on every pattern in which a fixed symbol `s` does not occur. If `tau_mu` is injective
over `G`, then the linear automaton `tau_(lambda_0)` is injective over `G`. So either:
- `tau_(lambda_0)` is a linear strict automaton over `G`; or
- it is bijective, and `sum_m c_m m` is a unit of `F_q[G]`.

*Proof.*
- **Collision from a kernel element.** Let `d != 0` with `tau_(lambda_0)(d) = 0`. Because `q >= 3`,
  we can choose `x(g)` outside `{s, s - d(g)}` for every `g`. Then neither `x` nor `x + d` takes the
  value `s`, so `tau_mu = tau_lambda` on both. Also
  `tau_lambda(x + d) = tau_lambda(x) + tau_(lambda_0)(d) = tau_lambda(x)`, so `tau_mu` is not
  injective.
- **The dichotomy.** A bijective linear automaton has a linear automaton as inverse. With
  `tau_C tau_A = tau_(CA)`, both composites give `CA = AC = 1`.

QED

Over two symbols there is no room to avoid a symbol, and Proposition 5.2 says nothing.

### 5.2 The smallest open rules

**Three symbols, three addresses.** Call a rule **rigid** if no pair is blind in all three
coordinates.
- **What is excluded.** By Proposition 5.1, a rule that is not rigid is excluded on Sidon
  placements.
- **Example.** The rule `R` of Remark 3.4 is rigid and passes the constant tests, and no single-site
  change of any configuration is invisible for it.
- **What Proposition 5.2 gives.** Its only patched pattern contains the symbol `2`. So an
  injective realization of `R` over `G` needs one of two things:
  - `1 - a + b` is a unit of `F_3[G]`; or
  - `G` carries a linear strict automaton.
- **The filter alone does not decide `R`.** Units of this shape exist. Over `Z x Z/3` with
  `b = ac` and `c^3 = 1`, `1 - a + ac = 1 - a(1 - c)` and `(a(1 - c))^3 = 0`. That group is
  amenable, so `R` is not injective there, but the unit shows that Proposition 5.2 cannot exclude
  `R` by itself.
- **What stays open.** `R` over a nonsofic 2-generated group in which `1 - a + b` is a unit. There,
  any collision must use the patched pattern in a closed finite perturbation or an infinite one.
  No mechanism is known. This is the claim `ternary-three-address-injective-automata-have-balanced-rules`.

**Two symbols, four addresses.**
- **What is excluded.**
  - Theorem 3.2 excludes Sidon placements.
  - The constant tests of Section 4 apply.
  - Parity patched at one cell dies. If the patched cell is not constant, both constants map to
    `0`. If it is `0000`, a flip of the constant `0` is invisible, and `1111` is symmetric.
- **Where a census starts.** At placements that are Sidon in no group, such as `{1, a, b, ab}`.
  - Coincidences: `a^-1 (ab) = b` and `(ab)^-1 a = b^-1`.
  - Constraints: the single flip needs blind patterns with `r_1(b) = r_a(ab)` and
    `r_ab(a) = r_b(1)`. Rules whose blind patterns violate these need double flips or more.
- **Open claim.** This is `binary-four-address-injective-automata-have-balanced-rules`.

## 6. Consolidation note

Section 4 first landed as its own claim, `binary-three-address-injective-automata-have-balanced-rules`
(9aaae6d677). The same statement had landed six minutes earlier as
`three-address-binary-injective-rules-are-balanced` (w3-bal-design, 5a73418397, artifact
`unbalanced-design-memory-collisions-2026-09-12.md`, Section 2). The duplicate claim was deleted.
Section 4 stays as a second, independent proof of that claim, through the route
`binary-three-address-balance-census-proof`.
- **Their proof:** the rectangle relation, one glued involution, and a double flip.
- **This proof:** constant tests leave four rule classes, prescribed flips exclude each class, and a
  double flip settles the class `{000, 110, 101}`.

## 7. Constant backgrounds for one moved entry (check of w3-bal-design's witness)

This section checks the witness of `constant-background-kills-unit-linear-defect-rules` (w3-bal-design), applies
it to `R`, and records a weaker exception for patterns that use every symbol.

**Setting.**
- `A = F_q`, `ell = sum_m c_m x_m` linear, `L = sum_m c_m m` in `F_q[G]`.
- `mu(w) = ell(w) + t [w = p]` with `t != 0`, so `tau_mu(x) = tau_ell(x) + t D(x)`, where `D(x)` is the
  indicator of the sites whose window shows `p`.
- `L` is a unit with inverse `K` supported on `N`. Put `y = tau_K(delta_1)`. Then `y(g) = k_(g^-1)`, so `y` is
  supported on `N^-1`, and `tau_ell(y) = tau_(LK)(delta_1) = delta_1`.

**Witness.** Fix a symbol `c`. Let `x = p + t y` on `M` and `x = c` off `M`, and put `x' = x - t y`. Then:
- `x'|_M = p`, and `x|_M != p`, because `ell(y|_M) = tau_ell(y)(1) = 1`, so `y|_M != 0`;
- `tau_mu(x) = tau_mu(x')` iff `D(x') - D(x) = delta_1`;
- `x != x'`, and they differ only on `N^-1`, so a collision also refutes pre-injectivity.

**Which windows can show `p`.** `x` equals `c` off `M`, and `x'` equals `c` off `M ∪ supp(y)`. A translate `hM`
can show `p` only if `p_m = c` at every address `m` whose site `hm` lies outside that set.
- **`p` omits `c`.** Only translates inside the set can show `p`. For `x` this forces `hM = M`. With `1 in M` and
  `|M| = 3`, `hM = M` for `h != 1` forces `M = {1, h, h^2}`, so `<M>` is cyclic. So outside the amenable case
  `D(x) = 0`, and the only exceptions are translates `hM`, `h != 1`, lying in `M ∪ supp(y)` with
  `x'|_(hM) = p`.
- **`p` has distinct entries.** At most one address has `p_m = c`. So only translates with at most one site
  outside `M ∪ supp(y)`, at that address, can show `p`. Each of the `q` choices of `c` gives its own finite
  exception set, and any empty one gives a collision.

**For `R = x - y + z` with `(0,2,2)` moved to `1`.** Here `p` omits `1`, `t = 1`, and `L = 1 - a + b`.
- **Non-unit.** By `avoidable-patches-of-affine-rules-inherit-linear-injectivity`, an injective `R` makes
  `tau_ell` injective and not surjective. So `G` already carries a linear strict automaton.
- **Unit.** `R` is not injective unless some translate of `{1, a, b}` other than itself lies in
  `M ∪ supp(y)` and shows `(0,2,2)` in `x'`.

**Rigid rules with repeated pairs.** w3-bal-design's corollary covers distinct pairs. If two pairs coincide,
the moved pattern can use every symbol while the augmentation stays nonzero.
- **Example.** `x + y + 2z` with the value at `(0,1,2)` moved from `2` to `0`.
- **Its data.** Pairs `{0,1}`, `{1,2}`, `{1,2}`; identity diagonal; counts `10, 9, 8`; augmentation `1`.
- **What applies.** The distinct-entries case above, not the omitted-symbol case.
