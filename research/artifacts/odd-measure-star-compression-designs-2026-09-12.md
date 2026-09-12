# Star compression designs in the odd-measure crossed product

Lane `w3-corner-crossed`, 2026-09-12. Supports the claims
`thompson-action-on-odd-measures-is-essentially-free` and
`star-compression-designs-need-weight-four-colliding-columns`.

Notation follows `research/artifacts/ternary-lift-signed-thompson-crossed-product-2026-09-12.md`:
* `B = F_3[H] eps_- ~= C(M_-, F_3) ⋊_alg V`, with `H = E ⋊ V` the signed Thompson group.
* `lambda` is normalized Haar measure on `M_-`, the odd finitely additive `F_2`-measures.
* `U_C = {mu in M_- : mu(C) = 1}` and `q_[0] = 1_(U_[0])`.
* The open target `odd-measure-crossed-product-unit-below-cylinder-idempotent` asks for
  `c' q_[0] b' = eps_-` with `b', c' in B`.

Everything is over `F_3`.

## 1. The involution and star designs

* On `F_3[H]` the linear map `[g] -> [g^-1]` is an algebra anti-automorphism. It fixes `eps_-`,
  since `z = z^-1`, and every `[tau_C]`, since `tau_C^2 = 1`. So it fixes every function in
  `C(M_-, F_3)`, and on `B` it reads `(f[g])* = [g^-1] f = (f o g)[g^-1]`.
* **Definition.** A *star compression design* is `x in B` with `x* x = eps_-` and `q_[0] x = x`.
* **Lemma 1.1.** A star design solves the target, with `b' = x` and `c' = x*`:
  `c' q_[0] b' = x* q_[0] x = x* x = eps_-`. QED
* **Scope.** A solution of the target need not be a star design. Over `F_3` nothing forces
  `c' = b'*`. Theorem 4.1 constrains star designs only.

## 2. Columns

Write `x = sum_(g in F) a_g [g]`, with `F` a finite subset of `V` and `a_g in C(M_-, F_3)`.

* `q_[0] x = x` iff `supp a_g ⊂ U_[0]` for every `g`.
* `x* x = sum_(g,h) (a_g a_h) o g . [g^-1 h]`. So `x* x = eps_-` iff for every `mu` and `k`:

      sum over g in F with gk in F of  a_g(g mu) . a_(gk)(g mu)  =  [k = 1].        (2.1)

* **Columns.** For `mu in M_-` put `col(mu) = sum_(g in F) a_g(g mu) delta_(g mu)`, a finitely
  supported `F_3`-valued function on the orbit `V mu`, with pairing `<u,v> = sum_p u(p) v(p)`.
* **Lemma 2.1.** If `nu` has trivial stabilizer, then `<col(nu), col(k nu)> = [k = 1]` for all `k`.
  *Proof.* Common points are `g nu = h k nu`, i.e. `g = hk` by freeness, so the pairing is
  `sum_h a_(hk)(hk nu) a_h(hk nu)`. Substituting `h' = hk`, this is the left side of (2.1) at the
  point `nu` with `k^-1`. QED
* **Counting functions.**
  * `c(mu) = #{g in F : a_g(g mu) != 0}`, the column weight;
  * `n(nu) = #{g in F : a_g(nu) != 0}`, the image multiplicity.
* Nonzero squares in `F_3` equal `1`, so (2.1) at `k = 1` says `c(mu) ≡ 1 mod 3`. In particular
  `c(mu) >= 1` for every `mu`.

## 3. Essential freeness

**Proposition 3.1.** For `g != 1` in `V`, `Fix(g) = {mu in M_- : g mu = mu}` is `lambda`-null.

*Proof.*
* `M = Hom(C(X, F_2), F_2)` is the Pontryagin dual of the countable elementary abelian group
  `C(X, F_2)`, and `lambda` is Haar measure on `M` restricted to the index-two coset `M_-`.
* `(g mu)(1_C) = mu(1_(g^-1 C)) = mu(1_C o g)`. So `g mu = mu` iff `mu` vanishes on
  `D_g = {f o g + f : f in C(X, F_2)}`, and `Fix(g)` lies in the annihilator `Ann(D_g)`.
* For a subspace `D`, `Ann(D)` has Haar measure `2^(-dim D)` if `dim D` is finite, and `0` if it is
  infinite. Choose a basis of `C(X,F_2)` extending one of `D`; then `M ~= F_2^N` with product measure
  and `Ann(D)` is a coordinate subgroup.
* `g != 1` moves some `x`, so `g^-1 x != x`. By continuity choose a cylinder `C` containing `x` with
  `C cap g^-1 C = empty`. For disjoint subcylinders `C_j` of `C`, the vectors
  `1_(C_j) + 1_(g^-1 C_j)` are linearly independent, because their restrictions to `C` are disjoint
  nonzero indicators. `C` has infinitely many disjoint subcylinders, so `dim D_g = infinity`.
* So `Ann(D_g)` is null in `M`, and `Fix(g)` is null in `M_-`. QED

So `V` acts essentially freely on `(M_-, lambda)`: off a null set, every orbit is a copy of `V`.

## 4. The weight theorem

**Theorem 4.1.** Let `x` be a star design, with `F`, `c`, `n` as in Section 2.
1. `∫ c dlambda = ∫ n dlambda`, and `n` vanishes off `U_[0]`.
2. The collision set `A = {nu : n(nu) >= 2}` satisfies `∫_A n dlambda >= 1/2`, so `lambda(A) > 0`.
3. For a.e. `nu in A` and distinct `g, g' in F` with `a_g(nu) a_(g')(nu) != 0`, the columns
   `col(g^-1 nu)` and `col(g'^-1 nu)` are distinct and share at least two points. The products of
   their entries over the shared points sum to `0` in `F_3`.
4. `W = {mu : c(mu) >= 4}` satisfies `∫_W c dlambda >= 1/2`, so `lambda(W) >= 1/(2|F|)`.

*Proof.*
1. By `V`-invariance of `lambda`,
   `∫ c = sum_g lambda(g^-1 supp a_g) = sum_g lambda(supp a_g) = ∫ n`.
   Each `supp a_g` lies in `U_[0]`.
2. Since `c >= 1`, `∫_(U_[0]) n >= 1`. Off `A`, `n <= 1`, so `∫_(U_[0] \ A) n <= lambda(U_[0]) = 1/2`.
   Hence `∫_A n >= 1/2`.
3. Remove the null set `N = union_(k in V, k != 1) Fix(k)`. It is a countable union of null sets
   (Proposition 3.1), and it is `V`-invariant, so every point of an orbit off `N` satisfies Lemma 2.1.
   Put `mu = g^-1 nu`
   and `mu' = g'^-1 nu`. They are distinct, since `mu = mu'` would put `nu` in `Fix(g' g^-1)`. Both
   columns contain `nu`, and by Lemma 2.1 their pairing is `0`. A single shared point would give a
   product of two nonzero elements of `F_3`, which is nonzero. So they share at least two points.
4. For a.e. `nu in A` and every `g` with `a_g(nu) != 0`, part 3 gives `mu = g^-1 nu` a column
   meeting another column in at least two points. So `c(mu) >= 2`, and `c ≡ 1 mod 3` gives
   `c(mu) >= 4`. Counting pairs `(g, mu)` with `g mu in A` and `a_g(g mu) != 0`:
   `∫_A n = sum_g lambda(A cap supp a_g) = ∫ #{g : g mu in A, a_g(g mu) != 0} dlambda(mu)`.
   The integrand is at most `c(mu)` and vanishes a.e. off `W`, so `∫_W c >= ∫_A n >= 1/2`.
   Finally `c <= |F|`. QED

**Consequences.**
* **Cancellation-free designs do not exist.** If distinct columns never share a point, then
  `n <= 1` a.e., contradicting part 2. This extends Proposition 4 of the crossed-product artifact
  from honest monomial partial isometries to arbitrary multi-point columns.
* **Weight four is forced where the mass is.** A signed column with `k` nonzero entries has norm
  `k mod 3`, so norm `1` needs `k in {1, 4, 7, ...}`. Columns of weight at least four carry at least
  half of the total mass `∫ c dlambda`.
* **Collisions cancel in pairs or triples.** Two colliding columns share two points with products of
  opposite sign, or three with equal products (`1 + 1 + 1 = 0`), and so on.
* **Average image multiplicity on `U_[0]` is at least `2`.** This follows from part 1 with `c >= 1`
  and `lambda(U_[0]) = 1/2`.

## 5. Finite certificates, difference-free designs, and where it stops

Supports the open claim `odd-measure-crossed-product-has-star-compression-design` and the route
`star-compression-design-solves-odd-measure-target`.

**Finite certificate.**
* Each `a_g` depends on `mu` through finitely many clopen values.
* Let `P` be a finite clopen partition of `X` refining `[0]`, every clopen the `a_g` read, and their
  translates by the finitely many elements of `F^-1 F`.
* Then `q_[0] x = x` and (2.1) for every `k in F^-1 F` are identities of `F_3`-valued functions on the
  finite set `M_-^P` of odd vectors. For `k` outside `F^-1 F`, (2.1) is empty.
* So a star design is a finite object: the elements of `F` as prefix-code pairs, and truth tables of
  the `a_g` on `M_-^P`. Checking it is a finite computation inside `H`, whose word problem is
  decidable. This fits the one-decidable-host rule.

**Corollary 5.0 (small memory sets are dead).** Every star design has `|F| >= 4`. This holds because
`c <= |F|` and Theorem 4.1(4) needs `lambda(c >= 4) > 0`. So designs with two or three terms are dead,
including those whose differences are involutions.

**Proposition 5.1 (difference-free designs are dead).** Suppose the map `(g, g') -> g^-1 g'` on
ordered pairs of distinct elements of `F` is injective. In particular no difference is an involution,
since `(g, g')` and `(g', g)` have inverse differences. Then `F` carries no star design.

*Proof.* The component of `x* x` at `k = g^-1 g'` has the single term `(a_g a_(g')) o g`, so it
vanishes iff `a_g a_(g') = 0`. So the coefficient supports are pairwise disjoint, `n <= 1`
everywhere, and Theorem 4.1(2) fails. QED
* **Reading.** In group terms, Theorem 4.1(3) says a collision at the base point `mu` needs the
  difference `k` for at least two pairs `(h, hk)` contributing at `mu`. So memory sets must contain
  repeated differences, not merely nonamenable projections.

**Where it stops.**
* No star design is known.
* **Gadgets.** The natural gadgets are weight-four signed columns. Over `F_3` the four rows of the
  `4 x 4` Hadamard matrix are orthonormal, since each norm is `4 = 1` and the pairings are `0`; three
  shared points with equal products also cancel. A design must chain such gadgets through the
  nonamenable part of `V`, with every image inside `U_[0]`.
* **Over `Z`.** A periodic window of length four with signs `p` needs `p_3 p_0 = 0` at shift three,
  which is impossible. This is consistent with amenability forbidding compressions.
* **Beyond Theorem 4.1.** Obstructions reduce to the `F_3`-linear soficity gate of `E ⋊ V`
  (Section 7(a) of the crossed-product artifact). General solutions with `c' != b'*` escape the square
  counting entirely.
