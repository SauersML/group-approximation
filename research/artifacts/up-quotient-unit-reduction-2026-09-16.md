# Higman's unit conjecture reduces to groups with no nontrivial unique-product quotient (lane hi-fron, 2026-09-16)

**Target.** `integral-unit-conjecture-torsion-free`.

**Result.** The route `integral-unit-conjecture-from-no-up-quotient-case` gives

    integral-units-trivial-on-groups-without-up-quotients  +  connell-group-ring-primality
        ==>  integral-unit-conjecture-torsion-free .

The new hole is Higman's conjecture restricted to the class `T_UP` defined in
Section 1: finitely generated torsion-free groups with no nontrivial
homomorphism into a group with unique products. The converse implication is
trivial, since the hole is a special case of the root. So this is an exact
reorganization of the root, not a proof of any new case. It removes every
group that has a nontrivial unique-product quotient. It does not remove the
Promislow group `P` (Remark 5.3).

**Novelty.** None claimed. The extension step is the unique-product grading
argument. Oinert (arXiv:1904.04847v3, abstract, read 2026-09-16) solves the
unit and zero-divisor problems for rings graded by unique product groups
without nontrivial homogeneous zero divisors; the body of that paper was not
read. The passage from zero divisors to units is the argument of Proposition
1.9 in Gardam's Bonn lecture notes. The only thing
added here is the minimal-support normalization, which puts both reductions
into one class of finitely generated groups.

**Trust surface.** Connell's theorem enters the reduction once, in Lemma 4,
through the established literature-import claim `connell-group-ring-primality`.
Strojnowski's lemma (Lemma 2) is proved in full below, and so is everything
else in Sections 1 to 4. Proposition 5.3 (`P` lies in the class) additionally
uses the established citation claim `unit-conjecture-fails-over-complex-numbers`
for two facts: `P` is torsion-free, and `C[P]` has a nontrivial unit.

## Contents

1. Definitions and notation
2. Components along a homomorphism
3. Lemmas
4. The reduction theorem
5. Remarks: the dichotomy, what the class removes, `P`, other coefficients, zero divisors
6. What this does not do
7. Sources

## 1. Definitions and notation

- **Rings.** `R` is a ring with `1`. When `R` is an *integral domain* it is
  also commutative with `0 != 1` and has no zero divisors. `R^x` is its unit
  group. For `R = Z`, `R^x = {+-1}`.
- **Trivial units.** A unit of `R[G]` is *trivial* if it equals `lambda g`
  with `lambda in R^x` and `g in G`.
- **Supports.** For `x = sum_g x_g g in R[G]`, `supp x = {g : x_g != 0}` and
  `|x| = |supp x|`. Left and right translation by group elements do not change
  `|x|`.
- **Unique products.** For finite nonempty `A, B` in a group `Q`, an element
  `q in AB` is a *unique product* of `(A, B)` if exactly one pair
  `(a, b) in A x B` has `ab = q`. The group `Q` *has unique products* (UP) if
  every such pair `(A, B)` has at least one unique product.
  - A subgroup of a UP group has UP, because the condition quantifies over
    finite subsets.
  - A UP group is torsion-free. If `g` has order `n >= 2`, take `A = B = <g>`:
    every element of `AB = <g>` has `n` representations.
- **The class.** `T_UP` is the class of finitely generated torsion-free groups
  `K` such that every homomorphism from `K` to a group with unique products is
  trivial. The image of a homomorphism into a UP group is a UP group, so
  equivalently the trivial group is the only quotient of `K` with unique
  products.

## 2. Components along a homomorphism

Let `phi : G -> Q` be a homomorphism. For `x in R[G]` and `q in Q`, put

    x_(q) = sum over g in supp x with phi(g) = q of  x_g g ,

so `x = sum_q x_(q)`. The set of classes where `x_(q) != 0` is
`phi(supp x)`. Also `|x_(q)| <= |x|`, with equality for some `q` only if
`phi(supp x) = {q}`.

**Lemma 1 (components).** Let `x, y in R[G]`, `A = phi(supp x)` and
`B = phi(supp y)`. For every `q in Q`,

    (xy)_(q) = sum over (a, b) in A x B with ab = q  of  x_(a) y_(b) .

In particular, if `q = ab` is a unique product of `(A, B)`, then
`(xy)_(q) = x_(a) y_(b)`.

*Proof.* Expand `xy = sum_(a,b) x_(a) y_(b)`. Every group element in the support
of `x_(a) y_(b)` has the form `gh` with `phi(g) = a` and `phi(h) = b`, so it lies
in `phi^-1(ab)`. Taking the part supported on `phi^-1(q)` gives the formula.
QED

## 3. Lemmas

**Lemma 2 (Strojnowski: two unique products).** Let `Q` have unique products
and let `A, B` be finite nonempty subsets of `Q` with `|A| |B| >= 2`. Then
`(A, B)` has at least two distinct unique products.

This is Gardam's lecture notes, Proposition 1.20. The proof there was checked
line by line and is reproduced with the case split made explicit.

*Proof.* Suppose `(A, B)` has exactly one unique product `a_0 b_0`.

*Normalization.* The map `(a, b) -> (a_0^-1 a, b b_0^-1)` is a bijection
`A x B -> A' x B'`, where `A' = a_0^-1 A` and `B' = B b_0^-1`. It multiplies
every product by `a_0^-1` on the left and `b_0^-1` on the right, so it matches
unique products with unique products, and `|A'| |B'| = |A| |B|`. So we may
assume `1 in A`, `1 in B`, and that `1 = 1 * 1` is the only unique product.

*Consequence.* For every `(a, b) in A x B` other than `(1, 1)`, there is
`(a', b') in A x B` with `a'b' = ab` and `a' != a` (hence `b' != b`).
- If `ab = 1`, then `1` has the two representations `(a, b)` and `(1, 1)`,
  which contradicts its being a unique product. So `ab != 1`.
- Then `ab` is not a unique product, so it has a second representation
  `(a', b') != (a, b)`.
- `a' = a` would force `b' = b`, so `a' != a`.

*The contradiction.* Put `C = B^-1 A = {b^-1 a}` and `D = B A^-1 = {b a^-1}`.
Both are finite and nonempty. We show that no element of `CD` is a unique
product of `(C, D)`, which contradicts UP.

Fix `x in CD` with a representation `x = cd`. Choose `a_1, a_2 in A` and
`b_1, b_2 in B` with `c = b_1^-1 a_1` and `d = b_2 a_2^-1`. We produce
`(c', d') in C x D` with `c'd' = x` and `c' != c`.

1. **Case `(a_1, b_2) != (1, 1)`.** Take `(a_1', b_2')` with
   `a_1' b_2' = a_1 b_2` and `a_1' != a_1`. Put `c' = b_1^-1 a_1'` and
   `d' = b_2' a_2^-1`. Then `c'd' = b_1^-1 (a_1' b_2') a_2^-1 = x`, and
   `c' != c`.
2. **Case `(a_1, b_2) = (1, 1)` and `(a_2, b_1) != (1, 1)`.** Here
   `x = b_1^-1 a_2^-1 = (a_2 b_1)^-1`. Take `(a_2', b_1')` with
   `a_2' b_1' = a_2 b_1` and `b_1' != b_1`. Put `c' = b_1'^-1 * 1`, which lies
   in `C` because `1 in A`, and `d' = 1 * a_2'^-1`, which lies in `D` because
   `1 in B`. Then `c'd' = (a_2' b_1')^-1 = x`, and `c' != b_1^-1 = c`.
3. **Case `(a_1, b_2) = (a_2, b_1) = (1, 1)`.** Here `x = 1` and `c = 1`. Since
   `|A| |B| >= 2`, there is `a in A \ {1}` or `b in B \ {1}`.
   - With `a`: put `c' = a` (which is `1^-1 a`, in `C`) and `d' = a^-1` (which
     is `1 * a^-1`, in `D`).
   - With `b`: put `c' = b^-1` and `d' = b`.

   In both cases `c'd' = 1` and `c' != 1`.

So `x` has two representations. QED

**Lemma 3 (minimal zero divisors).** Let `R` be any ring and `G` a group. Suppose
`R[G]` has nonzero `x, y` with `xy = 0`, and choose such a pair with `|x| + |y|`
minimal. Choose `g in supp x` and `h in supp y`, and put

    x' = g^-1 x ,   y' = y h^-1 ,   K = < supp x'  ∪  supp y' > .

Then:
1. `x', y'` are nonzero elements of `R[K]` with `x'y' = 0`,
   `|x'| + |y'| = |x| + |y|` and `1 in supp x' ∩ supp y'`;
2. every homomorphism from `K` to a group with unique products is trivial;
3. if `G` is torsion-free, then `K` is in `T_UP`.

*Proof.* **Item 1.** `x'y' = g^-1 (xy) h^-1 = 0`, translation preserves
supports' sizes, and `1 = g^-1 g in supp x'`, and likewise for `y'`.

**Item 2.** Let `phi : K -> Q` be nontrivial with `Q` UP.
- Since `K` is generated by `S = supp x' ∪ supp y'`, some `s in S` has
  `phi(s) != 1`.
- Put `A = phi(supp x')` and `B = phi(supp y')`. Then `1 in A ∩ B` and
  `phi(s) in A ∪ B`, so `|A| >= 2` or `|B| >= 2`.
- UP gives a unique product `q = ab` of `(A, B)`. By Lemma 1, applied in
  `R[K]`, `0 = (x'y')_(q) = x'_(a) y'_(b)`.
- Both factors are nonzero, because `a in A` and `b in B`.
- By Section 2, `|x'_(a)| + |y'_(b)| < |x'| + |y'| = |x| + |y|`, since
  `|A| >= 2` or `|B| >= 2`.

These factors lie in `R[K]`, which is contained in `R[G]`, so this contradicts
minimality.

**Item 3.** `K` is generated by the finite set `S`, and it is a subgroup of
`G`. QED

Lemma 3 uses one unique product, not Lemma 2.

**Lemma 4 (a zero divisor yields a nontrivial unit).** Let `R` be an integral
domain and `K` a torsion-free group. If `R[K]` has nonzero `x, y` with `xy = 0`,
then `R[K]` has a nontrivial unit.

*Proof.* **Primeness.** Let `F` be the fraction field of `R`. `K` is
torsion-free, so its only finite subgroup is `1`. By Connell's theorem
(`connell-group-ring-primality`, applied with the field `F` as coefficient
ring), `F[K]` is prime: the product of two nonzero two-sided ideals is nonzero.

**A nilpotent element.** View `x, y` in `F[K]` and apply primeness to the
ideals generated by `y` and by `x`. Their product is spanned by the elements
`p y t x p'` with `p, t, p' in F[K]`, so `y t x != 0` for some `t in F[K]`.
Writing `t = sum_k t_k k` gives `y t x = sum_k t_k (y k x)`, so `y k x != 0`
for some `k in K`. Put `gamma = y k x`, which lies in `R[K]`. Then

    gamma != 0 ,    gamma^2 = y k (x y) k x = 0 ,

so `(1 + gamma)(1 - gamma) = 1 = (1 - gamma)(1 + gamma)`, and `1 + gamma` is a
unit.

**Nontriviality.** Suppose `1 + gamma = lambda h` with `lambda in R^x` and
`h in K`.
- **If `h = 1`.** Then `gamma = (lambda - 1) * 1`. Since `gamma != 0`,
  `lambda != 1`, so `gamma^2 = (lambda - 1)^2 * 1 != 0`, because `R` is a domain.
  This is a contradiction.
- **If `h != 1`.** Then `gamma = lambda h - 1` and
  `gamma^2 = lambda^2 h^2 - 2 lambda h + 1`. `K` is torsion-free, so
  `h^2 != 1`, and `h != 1`. So the coefficient of `1` in `gamma^2` is `1`,
  which is nonzero. This is a contradiction.

QED

**Lemma 5 (normalized units see no unique-product quotient).** Let `R` be a
ring and `G` a group such that `R[G]` has no zero divisors. Let `u, v in R[G]`
with `uv = vu = 1` and `1 in supp u`, and put `K = <supp u ∪ supp v>`. Then
every homomorphism from `K` to a group with unique products is trivial.

*Proof.* Let `phi : K -> Q` with `Q` UP, and put `A = phi(supp u)` and
`B = phi(supp v)`.

**Case `|A| |B| >= 2`.**
- By Lemma 2, `(A, B)` has two distinct unique products, so one of them,
  `q = ab`, satisfies `q != 1`.
- By Lemma 1, `(uv)_(q) = u_(a) v_(b)`.
- `uv = 1` is supported on `phi^-1(1)`, so `(uv)_(q) = 0`.
- So `u_(a) v_(b) = 0` with both factors nonzero, which is a zero divisor in
  `R[G]`. This case is impossible.

**Case `|A| = |B| = 1`.**
- `A = {1}` because `1 in supp u`. Let `B = {b}`.
- Then `uv = u_(1) v_(b)` is supported on `phi^-1(b)`. But `uv = 1`, so `b = 1`.
- So `phi` is trivial on the generating set `supp u ∪ supp v`, hence on `K`.

QED

**Lemma 6 (unique products give trivial units, without Connell).** Let `R` be
an integral domain and `G` a group with unique products. Then `R[G]` has no
zero divisors, and every unit of `R[G]` is trivial.

This is the classical fact recorded as Corollary 1.21 in Gardam's notes, where
the proof is left as an exercise. Here it follows from Lemmas 3 and 5.

*Proof.* **No zero divisors.** Suppose `xy = 0` with `x, y != 0`, and take the
minimal pair and the group `K` of Lemma 3.
- `K` is a subgroup of `G`, so it has unique products, and the identity
  `K -> K` is a homomorphism into a UP group. By Lemma 3 item 2 it is trivial,
  so `K = 1`.
- Then `x', y'` are nonzero elements of `R[K] = R` with `x'y' = 0`, which is
  impossible in a domain.

**Trivial units.** Let `uv = vu = 1`. Choose `g in supp u` and put
`u' = g^-1 u` and `v' = v g`.
- Then `u'v' = v'u' = 1` and `1 in supp u'`.
- `R[G]` has no zero divisors, so Lemma 5 applies to `u', v'`. The identity of
  `K = <supp u' ∪ supp v'>` is a homomorphism into a UP group, so `K = 1`.
- So `u', v' in R` with `u'v' = 1`, hence `u' = lambda in R^x` and
  `u = g u' = lambda g`.

QED

Lemma 6 is only a sufficient condition. `P` lacks unique products
(Remark 5.3), and whether `Z[P]` or `Q[P]` has a nontrivial unit is open
(`integral-unit-conjecture-torsion-free`,
`rational-unit-conjecture-torsion-free`).

## 4. The reduction theorem

**Theorem.** Let `R` be an integral domain. Suppose that for every group `K`
in `T_UP`, every unit of `R[K]` is trivial. Then for every torsion-free group
`G`, every unit of `R[G]` is trivial.

*Proof.* Fix a torsion-free group `G`.

**Step 1: `R[G]` has no zero divisors.** Suppose `xy = 0` with `x, y != 0`.
- Take the minimal pair and the group `K` of Lemma 3. By Lemma 3 item 3,
  `K` is in `T_UP`, and by item 1, `R[K]` contains the nonzero elements
  `x', y'` with `x'y' = 0`.
- `K` is torsion-free and `R` is a domain, so by Lemma 4, `R[K]` has a
  nontrivial unit.
- This contradicts the hypothesis applied to `K`.

**Step 2: units.** Let `u in R[G]` be a unit, with `uv = vu = 1`.
- Choose `g in supp u` and put `u' = g^-1 u` and `v' = v g`. Then
  `u'v' = g^-1 (uv) g = 1`, `v'u' = v u = 1`, and `1 in supp u'`.
- Put `K = <supp u' ∪ supp v'>`. It is generated by a finite set, and it is
  torsion-free as a subgroup of `G`.
- By Step 1, `R[G]` has no zero divisors, so Lemma 5 applies to `u', v'`:
  every homomorphism from `K` to a UP group is trivial. So `K` is in `T_UP`.
- `u'` and `v'` lie in `R[K]` and are inverse to each other there, so `u'` is a
  unit of `R[K]`. By the hypothesis, `u' = lambda k` with `lambda in R^x` and
  `k in K`.
- So `u = g u' = lambda (gk)` is trivial.

QED

**Corollary (the route).** Take `R = Z`, so `R^x = {+-1}`. If every unit of
`Z[K]` is `+-k` for every `K` in `T_UP`
(`integral-units-trivial-on-groups-without-up-quotients`), then every unit of
`Z[G]` is `+-g` for every torsion-free `G`
(`integral-unit-conjecture-torsion-free`). The proof uses Connell's theorem
once, in Lemma 4 over the field `Q`, and nothing else from the literature.

**Converse.** Every group in `T_UP` is torsion-free, so the root implies the
hole. The hole and the root are therefore equivalent. No converse route is
recorded, because it would create a cycle through open claims.

**Locality check.** The class `T_UP` quantifies over finitely generated
groups only. Both steps pass from `G` to finitely generated subgroups, so the
theorem needs no hypothesis on `G` beyond torsion-freeness. This matches
Remark 1.8 of Gardam's notes (the conjectures only depend on finitely
generated subgroups).

## 5. Remarks

### 5.1 The dichotomy for a counterexample

Let `G` be torsion-free and let `Z[G]` have a nontrivial unit. The proof of
the theorem produces a group `K` in `T_UP` and one of two certificates:
1. **Zero-divisor branch.** `Z[G]` has zero divisors. Then `K` is generated by
   `supp x' ∪ supp y'` for a support-minimal pair with `x'y' = 0` and
   `1 in supp x' ∩ supp y'`, and `Z[K]` has the nontrivial unit
   `1 + y' k x'` of Lemma 4.
2. **Unit branch.** `Z[G]` has no zero divisors. Then `K` is generated by
   `supp u' ∪ supp v'` for a normalized unit `u'` with inverse `v'` and
   `1 in supp u'`, and `u'` is a nontrivial unit of `Z[K]`.

In both branches the certificate lives in `Z[K]` with `K` in `T_UP`.

### 5.2 What the class removes

**Properties of the members.** Let `K` be a nontrivial group in `T_UP`.
- **`K` does not have unique products**, since the identity of `K` is a
  nontrivial homomorphism into `K`.
- **`K` has no nontrivial left-orderable quotient.** Left-orderable groups have
  unique products (Gardam's notes, Proposition 1.24: with `b_0 = max B`, the
  maximum of `AB` is a unique product). Free groups, torsion-free nilpotent
  groups and torsion-free one-relator groups are locally indicable (Gardam's
  notes, Example 1.32), hence left-orderable (Theorem 1.29 there). So none of
  them is a nontrivial quotient of `K`.
- **`K` has finite abelianization.** `K` is finitely generated, so an infinite
  abelianization would give a surjection onto `Z`.
- **`K` is not locally indicable**, because `K` itself does not map onto `Z`.

**Proposition 5.2 (unique products, local form).** A torsion-free group `G`
has unique products if and only if no nontrivial subgroup of `G` lies in
`T_UP`.

This is the unique-product analogue of the Burns--Hale theorem (Gardam's notes,
Theorem 1.29). It is folklore-level; no source was checked for it.

*Proof.* **Only if.** Subgroups of a UP group have UP, and a nontrivial member
of `T_UP` does not.

**If.** Suppose `G` does not have UP. Choose finite nonempty `A, B` in `G` such
that `(A, B)` has no unique product, with `|A| + |B|` minimal.
- **Normalize.** For `a_0 in A` and `b_0 in B`, the pair
  `(a_0^-1 A, B b_0^-1)` also has no unique product, since translation matches
  representations bijectively. So assume `1 in A ∩ B`.
- **Nontriviality.** Put `K = <A ∪ B>`. If `K = 1`, then `A = B = {1}`, and
  `1 = 1 * 1` is a unique product. So `K != 1`. `K` is finitely generated
  and torsion-free.
- **No UP quotient.** Let `phi : K -> Q` be nontrivial with `Q` UP.
  - Some element of `A ∪ B` has nontrivial image. Since `1 in A ∩ B`, this
    gives `|phi(A)| >= 2` or `|phi(B)| >= 2`.
  - Let `q = ab` be a unique product of `(phi(A), phi(B))`. Put
    `A_a = A ∩ phi^-1(a)` and `B_b = B ∩ phi^-1(b)`. Both are nonempty, and
    `|A_a| + |B_b| < |A| + |B|`.
  - By minimality, `(A_a, B_b)` has a unique product `c = a_1 b_1`.
  - Let `c = a'b'` with `a' in A` and `b' in B`. Then
    `phi(a') phi(b') = phi(c) = q`, so `phi(a') = a` and `phi(b') = b` by the
    uniqueness of `q`. So `(a', b')` lies in `A_a x B_b`, and
    `(a', b') = (a_1, b_1)`.
  - So `c` is a unique product of `(A, B)`, which is a contradiction.

So `K` is a nontrivial member of `T_UP`. QED

**Consequence for the reduction.** By the proof of the theorem, Higman's
conjecture holds on a torsion-free `G` as soon as it holds on the members of
`T_UP` inside `G`. If there are none besides `1`, then by Proposition 5.2 `G`
has unique products, and Lemma 6 already gives trivial units. **So the
reduction proves the conjecture unconditionally on no group outside the
unique-product groups.** What it does is concentrate every potential
counterexample into a finitely generated member of `T_UP` inside the host.

### 5.3 The Promislow group lies in `T_UP`

**Proposition 5.3.** The Promislow group

    P = < a, b | b^-1 a^2 b = a^-2 ,  a^-1 b^2 a = b^-2 >

lies in `T_UP`: every homomorphism from `P` to a group with unique products is
trivial.

**Input.** The established citation claim
`unit-conjecture-fails-over-complex-numbers`: `P` is torsion-free, and `C[P]`
has a nontrivial unit (Gardam, arXiv:2312.05240v2, Theorem A). Nothing else is
imported. This proposition is recorded as the claim
`promislow-group-has-no-unique-product-quotient`, with the route
`promislow-no-up-quotient-from-complex-units`.

*Proof.* **(a) Finiteness and torsion.** `P` has two generators, and it is
torsion-free by the input.

**(b) `P` does not have unique products.** `C` is an integral domain and `C[P]`
has a nontrivial unit, so Lemma 6 shows that `P` is not UP.

**(c) Relations in `P`.** Put `x = a^2`, `y = b^2` and `z = (ab)^2`. Everything
below follows from the two relators.
- **`x` and `y` are inverted.** The first relator says `b^-1 x b = x^-1`.
  Inverting both sides gives `b^-1 x^-1 b = x`, that is, `b x b^-1 = x^-1`.
  In the same way, `a^-1 y a = y^-1` and `a y a^-1 = y^-1`.
- **`x` and `y` commute.** `y x y^-1 = b (b x b^-1) b^-1 = b x^-1 b^-1 = x`.
- **Conjugation by `ab`.** `(ab) x (ab)^-1 = a (b x b^-1) a^-1 = a x^-1 a^-1 = x^-1`,
  since `a` commutes with `x = a^2`. Likewise
  `(ab) y (ab)^-1 = a (b y b^-1) a^-1 = a y a^-1 = y^-1`, and `ab` commutes
  with `z = (ab)^2`.
- **`z` commutes with `x` and `y`**, since conjugation by `z` is conjugation by
  `ab` applied twice.
- **`a z a^-1 = z^-1`.** Right-multiplying by `a` and then by `bab`, this is
  equivalent to `a^2 b a b · b a b = 1`. Now
  `a b^2 a = (a y a^-1) a^2 = y^-1 x`, so

      a^2 b a b b a b = x b (a b^2 a) b = x b y^-1 x b = x y^-1 (b x b^-1) b^2 = x y^-1 x^-1 y = 1 ,

  using `b y^-1 = y^-1 b`, `b x b^-1 = x^-1`, `b^2 = y` and `xy = yx`.
- **`b z b^-1 = z^-1`.** Write `b = a^-1 (ab)`. Then
  `b z b^-1 = a^-1 (ab) z (ab)^-1 a = a^-1 z a`. From `a z a^-1 = z^-1` we get
  `a^-1 z^-1 a = z`, hence `a^-1 z a = z^-1`.

Conjugation signs on `(x, y, z)`, where `+` means fixed and `-` means inverted:

| conjugating element | `x` | `y` | `z` |
|---|---|---|---|
| `a` | + | - | - |
| `b` | - | + | - |
| `ab` | - | - | + |

So `L = <x, y, z>` is abelian and normal in `P`, and every element of `L` can
be written `x^i y^j z^k`.

**(d) `[P : L] <= 4`.** In `P/L` the images of `a`, `b` and `ab` square to `1`.
So the image of `ab` equals its inverse, the image of `ba`. The quotient is
abelian, generated by two involutions, and has order at most `4`.

**(e) The homomorphisms.** Let `phi : P -> Q` with `Q` UP, put `N = ker phi`,
and write `alpha = phi(a)` and `beta = phi(b)`. `Q` is torsion-free.
- **Case `N ∩ L = 1`.** Then `N` maps injectively into `P/L`, so `N` is
  finite. `P` is torsion-free, so `N = 1`. Then `phi` is injective, and `P`
  is isomorphic to a subgroup of `Q`, hence has UP. This contradicts (b).
- **Case `N ∩ L != 1`.** Take `m = x^i y^j z^k in N`, `m != 1`, so
  `(i, j, k) != (0, 0, 0)`. `N` is normal, so by the table
  - `m (a m a^-1) = x^(2i)` lies in `N`,
  - `m (b m b^-1) = y^(2j)` lies in `N`,
  - `m ((ab) m (ab)^-1) = z^(2k)` lies in `N`.

  So `phi(x)^(2i) = phi(y)^(2j) = phi(z)^(2k) = 1`. Since `Q` is torsion-free,
  `phi(x) = 1` if `i != 0`, `phi(y) = 1` if `j != 0`, and `phi(z) = 1` if
  `k != 0`. At least one of these holds.
- **Each of them forces `phi = 1`.** The relators give
  `beta^-1 alpha^2 beta = alpha^-2` and `alpha^-1 beta^2 alpha = beta^-2`.
  - If `phi(x) = alpha^2 = 1`, then `alpha = 1`. The second relator gives
    `beta^4 = 1`, so `beta = 1`.
  - If `phi(y) = beta^2 = 1`, then `beta = 1`. The first relator gives
    `alpha^4 = 1`, so `alpha = 1`.
  - If `phi(z) = (alpha beta)^2 = 1`, then `beta = alpha^-1`. The first relator
    becomes `alpha alpha^2 alpha^-1 = alpha^-2`, so `alpha^4 = 1` and
    `alpha = beta = 1`.

QED

**Consistency check.** `experiments/up-quotient-unit-reduction-2026-09-16/promislow_affine_action.py`
checks the relators and the sign table in exact rational arithmetic, for the
affine maps `a(v) = diag(1,-1,-1) v + (1/2, 1/2, 0)` and
`b(v) = diag(-1,1,-1) v + (0, 1/2, 1/2)` of `R^3`. Its log
(`promislow_affine_action-run-2026-09-16.log`) ends with `ALL CHECKS PASS: True`.
The images of `x`, `y` and `z` are the translations by `e_1`, `e_2` and `-e_3`.
This is a check in one representation. The proof above derives (c) from the
relators and does not use the representation, or its faithfulness.

**Consequences.**
- **Nothing is removed on `P`.** The hole restricted to `P` is the root
  restricted to `P`. Every attempt on `Z[P]` recorded under the root transfers
  unchanged, and dies at the same place.
- **The complex analogue of the hole is false.** By Proposition 5.3 and the
  input, some member of `T_UP` has a nontrivial unit over `C`, with
  coefficients in `Z[zeta_8]`. So a proof of the hole must use the integrality
  of the coefficients, as the root's attempt "Reduction alone" already
  requires.
- **`T_UP` is not closed under finite index.** `P` is infinite and
  torsion-free, so `L` is a nontrivial finitely generated torsion-free abelian
  group, and it maps onto `Z`. A reduction that could pass to finite-index
  subgroups would remove `P`. It cannot. Let `u` be a nontrivial unit of
  `C[P]` and suppose `w = g^-1 u` lies in `C[L]`.
  - `w` is invertible in `C[L]`. Let `pi` be the projection of `C[P]` onto
    `C[L]` that keeps the coefficients on `L`. It satisfies `pi(w t) = w pi(t)`
    and `pi(t w) = pi(t) w` for `t in C[P]`. So `w pi(w^-1) = 1 = pi(w^-1) w`.
  - `L` is abelian and torsion-free, hence left-orderable, hence UP. By Lemma 6,
    `w = lambda h`, so `u = lambda gh` is trivial, which is a contradiction.

  So no translate of a nontrivial unit of `C[P]` lies in `C[L]`.

### 5.4 Other coefficient rings

The theorem holds for every integral domain `R`.
- **`R = Q`.** Rational units trivial on `T_UP` imply
  `rational-unit-conjecture-torsion-free`, with the same proof.
- **`R = C` and `R = F_2`.** The hypothesis of the theorem is false, since
  `P` is in `T_UP` and has nontrivial units over these rings. Over `C` this is
  the input of 5.3. Over `F_2` it is the Corollary of arXiv:2312.05240 recorded
  in `gardam-complex-units-citation`, and originally Gardam's 2021
  counterexample. The theorem is then vacuous.

The rational version is not recorded as a node. It adds no new open content
beyond the integral one, since on `P` the two are equivalent
(`rational-units-rescale-to-integral-units`).

### 5.5 The zero-divisor analogue

Let `R` be an integral domain. If `R[K]` has no zero divisors for every `K` in
`T_UP`, then `R[G]` has no zero divisors for every torsion-free `G`. This is
Step 1 of the theorem with Lemma 4 removed. It uses only Lemma 3, so it needs
neither Connell's theorem nor Lemma 2.

Combining this with Step 2 gives a Connell-free form of the reduction: the
root follows from two statements over `T_UP`, namely (i) `Z[K]` has no zero
divisors, and (ii) every unit of `Z[K]` is trivial whenever `Z[K]` is a domain.
Statement (i) is a second open hole, so this form is not recorded.

It is not recorded as a node. The graph already carries established
constraints of the same type on the support subgroup of a zero divisor
(`zero-divisor-support-subgroup-host-constraints`, item 2;
`small-non-up-left-support-has-no-orderable-quotient`). Lemma 3 adds that,
for a support-minimal pair, the whole generated group, not only a subset
pair, has no nontrivial UP quotient.

### 5.6 Approaches this subsumes, and one that fails

- **Transfinite descent along the rational derived series.** A first plan was
  to pass from `G` to the kernel of `G -> G^ab tensor Q` and iterate
  transfinitely. Lemma 5 needs just one UP quotient and a finitely generated
  support group, so the descent is unnecessary: a finitely generated group
  with infinite abelianization is not in `T_UP`.
- **Extensions by UP quotients.** If `N` is normal in `G`, `G/N` has UP and
  `R[G]` has no zero divisors, then Lemma 5 applied to `K -> G/N` shows that a
  normalized unit and its inverse are supported in `N`. So the units of `R[G]`
  are `g w` with `w` a unit of `R[N]`. This is the unique-product grading
  argument (compare Oinert's abstract).
- **Weaker quotient properties (fails).** One could try to replace UP by a
  property such as "`Z[Q]` is a domain with trivial units". The argument then
  dies at coefficient cancellation. In Lemma 1, `(uv)_(q)` is a sum over all
  representations `q = ab`. Without a unique product, no single term
  `u_(a) v_(b)` is forced to vanish, and the sum can vanish while every term is
  nonzero. No replacement lemma was found.

## 6. What this does not do

- **No new case.** By Proposition 5.2 and Lemma 6, the only torsion-free groups
  on which this argument proves Higman's conjecture outright are the groups with
  unique products, where it was classical.
- **No progress on `P`.** `P` lies in `T_UP` (Proposition 5.3), so the hole
  contains the one group on which the root is being attacked.
- **Not easier in truth value.** The hole and the root are equivalent (Section
  4, Converse). The gain is structural: every counterexample is pushed into a
  finitely generated torsion-free group with finite abelianization, no
  nontrivial left-orderable quotient and no nontrivial UP quotient, and it is
  generated by the supports of the unit and its inverse (Section 5.1).
- **No classification of `T_UP`.** No list of the members of `T_UP` among
  Bieberbach groups, one-ended hyperbolic groups or Kazhdan groups was
  attempted beyond `P`. In particular, it was not checked which other
  three-dimensional Bieberbach groups lie in `T_UP`.

## 7. Sources

Read or fetched on 2026-09-16 unless noted.
- **J. Oinert**, *Units, zero-divisors and idempotents in rings graded by
  torsion-free groups*, arXiv:1904.04847 (v1 9 Apr 2019, v2 2 May 2019,
  v3 20 Jul 2023). Abstract only. The journal page
  (doi:10.1515/jgth-2023-0110) returned HTTP 405 and was not read.
- **A. Tarizadeh**, *Homogeneity of zero-divisors, units and idempotents in a
  graded ring*, arXiv:2309.02880 (v1 6 Sep 2023, v3 16 Jul 2025). Abstract
  only; it generalizes the zero-divisor conjecture to rings graded by
  torsion-free groups.
- **M. Garg and I. Mineyev**, *On zero-divisors and units in group rings of
  torsion-free CAT(0) groups*, arXiv:2501.07646 (v1 13 Jan 2025, v2 8 Sep
  2025). Abstract only; it concerns explicit counterexample searches over
  `F_2` and is not used.
- **G. Gardam**, *Group rings of infinite groups*, lecture notes, University
  of Bonn (course of winter semester 2023/2024),
  <https://www.math.uni-bonn.de/people/gardam/notes/groig.pdf>. The PDF was
  downloaded and its text extracted crudely. Statements consulted: Remark 1.8
  (locality), Proposition 1.9 (unit conjecture implies zero-divisor
  conjecture, via Theorem 1.10), Theorem 1.10 (Connell, over a field),
  Proposition 1.20 (Strojnowski), Corollary 1.21 (UP implies the unit
  conjecture, proof left as an exercise), Proposition 1.24 (left-orderable
  implies UP), Theorem 1.29 (Burns--Hale), Corollary 1.31 (Higman) and Example
  1.32.
- **I. G. Connell**, *On the Group Ring*, Canad. J. Math. 15 (1963), 650--685,
  Theorem 8, as recorded in `connell-group-ring-primality-citation`. Not read
  here; used only through the established graph claim
  `connell-group-ring-primality`.
- **G. Gardam**, arXiv:2312.05240v2, used only through
  `unit-conjecture-fails-over-complex-numbers` and
  `gardam-complex-units-citation`.
- **Tabei**, arXiv:2608.02982v1, used only through the root node.
- **Novelty search.** The web-search budget of this session ran out, so no
  further search for the minimal-support normalization or Proposition 5.2 was
  possible. Treat both as probably known.

