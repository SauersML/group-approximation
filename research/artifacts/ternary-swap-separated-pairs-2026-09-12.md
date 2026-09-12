# The ternary anti-central corner equation is a swap-separated one-sided pair

Lane `gk-kdf-structure`, 2026-09-12. Supports the Cairn claim
`ternary-twisted-algebra-has-swap-separated-one-sided-pair`, its two routes into and out of
`ternary-anti-invariant-swap-corner-is-full`, and the Attempts added there.

## 0. Setting

Conventions follow `ternary-leavitt-swap-problem-splits-at-central-involution`:

* `R = L_(F_3)(1,2)`, `G = R^x`, `S = F_3[G]` and `pi : S -> R` the evaluation;
* `z = -1`, `eps_(+-) = 2(1 +- [z])`, and `S_- = eps_- S`;
* `w = s0 t1 + s1 t0`, `d = s0 t0 - s1 t1`, `e = 2(1 + [w])` and `e_- = eps_- e`.

From that claim (Section 7 of `research/artifacts/invariant-output-descent-and-sensitivity-2026-09-12.md`):

    d^2 = 1,   d w d = z w,   [d] e_- [d] = eps_- - e_-.                      (0.1)

Three consequences are used below.

    [w] e_- = e_- [w] = e_-,   [w][d] = [d][z][w],   e_- [d] e_- = 0,   (1 + [w])^2 = 2(1 + [w]).   (0.2)

* The second identity is `w d = d z w`, obtained by multiplying (0.1) on the left by `d`.
* The third follows because `e_- [d] = [d](eps_- - e_-)` is orthogonal to `e_-`.
* On `S_-` the central element `[z]` acts as `-1`, and `S_- ~= S/(1 + [z])S`. So `S_-` is the
  twisted group algebra of `PG = G/<z>` in which the lift of `z` equals `-1`.

The open claim `ternary-anti-invariant-swap-corner-is-full` asks for

    (C)   b, c in S_-   with   c e_- b = eps_- .

## 1. The reformulation

**Theorem 1.** The following are equivalent.

* **(C)** `c e_- b = eps_-` has a solution in `S_-`.
* **(P)** There are `a, c` in `S_-` with `c a = eps_-` and `c [w] a = 0`.
* **(E)** There is an idempotent `p` in `S_-` with `p ~ eps_-` and `p [w] p = 0`.
* **(X)** There are `a, c` in `S_-` with `c a = eps_-` such that `eps_- - m^2` is a unit of
  `S_-`, where `m = c [w] a`.

*Proof.*

**(P) => (C).** Put `b = a` and `c' = c(1 + [w])`. By (0.2) and `eps_- a = a`,

    c' e_- b = 2 c (1 + [w])^2 a = 4 c (1 + [w]) a = c a + c [w] a = eps_- .

**(C) => (P).** Put `b' = e_- b` and `c'' = c e_-`, so that `c'' b' = eps_-`. Put

    a = 2(b' + [d] b'),        chat = c'' + c'' [d].

* The cross terms vanish: `c'' [d] b' = c'' e_- [d] e_- b' = 0`.
* `[d]^2 = 1`, so `chat a = 2(c'' b' + c'' b') = 4 eps_- = eps_-`.
* `[w] b' = b'`, and `[w][d] b' = [d][z][w] b' = -[d] b'`, so `[w] a = 2(b' - [d] b')`.
* Hence `chat [w] a = 4(c'' b' - c'' b') = 0`.

**(P) <=> (E).**
* (P) => (E): `p = a c` is an idempotent equivalent to `eps_-`, and
  `p [w] p = a (c [w] a) c = 0`.
* (E) => (P): write `p = a c` with `c a = eps_-`. Then
  `c [w] a = (c a) c [w] a (c a) = c (p [w] p) a = 0`.

**(P) => (X).** Here `m = 0`.

**(X) => (P).** `a` has the left inverse `c`, and `[w] a` has the left inverse `c[w]`. The Gram
matrix of the two pairs is

    [ c    ] [ a , [w] a ]  =  [ eps_-  m     ]
    [ c[w] ]                   [ m      eps_- ]

because `c [w] a = m` and `c [w] [w] a = c a`. Put `u = (eps_- - m^2)^(-1)` and

    c' = u (c - m c [w]).

Then `c' a = u (eps_- - m^2) = eps_-` and `c' [w] a = u (m - m c a) = 0`. QED

**Corollary 2 (nilpotent cross terms suffice).** A one-sided pair `c a = eps_-` in `S_-` whose
swap cross term `m = c [w] a` is nilpotent gives a solution of (C), hence a strict linear
automaton on the full shift over `G`
(`anti-invariant-swap-corner-refutes-ternary-surjunctivity`).

## 2. What changes

**Any image works.**
* The image pair `(s0, t0)` satisfies (P) in `R`: `t0 s0 = 1` and `t0 w s0 = t0 s1 = 0`.
  The idempotent `s0 t0` satisfies (E), since `s0 t0 . w s0 t0 w = s0 t0 s1 t1 = 0`.
* A solution of (P) need not lift the image solution `b = s0 + s1`, `c = 2(t0 + t1)` of the
  Attempts on `ternary-anti-invariant-swap-corner-is-full`.
* Right translation `a -> a[g]`, `c -> [g^-1] c` (`g` in `G`) and left translation by
  `h` in `C_G(w)` both preserve (P). So only the class of `p` under these translations matters.

**Two sub-problems: a one-sided pair and its swap cross term.**
* Condition (X) splits the lift in two. First, `S_-` must fail direct finiteness through a pair
  `(a, c)`. Second, the swap cross term `m = c[w]a` must leave `eps_- - m^2` invertible.
* If `pi(a) = s0` and `pi(c) = t0`, then `m` lies in `ker pi`. The kernel must then supply both
  the one-sided inverse defect and a cross term with `1 - m^2` invertible, for example a
  nilpotent one.

**Characteristic three and the anti-central summand are both essential.**
* In any group algebra `k[H]` over a field, (P) with `eps_- = 1` is impossible: the augmentation
  gives `eps(c) eps(a) = 1` and `eps(c) eps(a) = 0`.
* The same holds on the central summand `S_+ = F_3[PG]`, which has an augmentation.
* `S_-` has no unital map to a commutative ring (part 2 of the split claim), so the
  augmentation argument does not apply there.
* The proof of (C) => (P) uses `d w d = z w` with `z = -1` acting as `-1`. On `S_+` the element
  `d` commutes with `w`, and the argument fails.

**A form suited to search.** In `S = F_3[G]`, (P) says: find `a, c` with

    c a - 1  in  (1 + [z]) S,        c [w] a  in  (1 + [z]) S .

These are two coefficient conditions over signed supports in `PG`. By Corollary 2, the second
may be relaxed to nilpotency of `eps_- c[w]a`.

## 3. Sharpening the cross-term form (added later on 2026-09-12)

For all `a, c` in `S_-`, (0.2) and `eps_- a = a` give

    c (1 + [w]) e_- a = c (1 + [w]) a .

So if `u = c(1 + [w]) a` is a unit, then `c'' = u^(-1) c (1 + [w])` satisfies `c'' e_- a = eps_-`.
Hence

    (C)  <=>  some a, c in S_- have c (1 + [w]) a a unit of S_- .

For a one-sided pair `c a = eps_-` this unit is `eps_- + m`, with `m = c[w]a`. The condition
`eps_- + m` invertible is weaker than (X), since `eps_- - m^2 = (eps_- - m)(eps_- + m)`.

What this form is and is not:
* It is (C) itself, up to normalization.
* A one-sided pair with a controlled cross term is a special solution, not a relaxation.
* Theorem 1 remains the statement that every solution of (C) yields one with `m = 0`.

## 4. Support no-go

Let `H <= G` contain `z` and `w`, and put `S_-(H) = eps_- F_3[H] <= S_-`.

**Theorem 3.** Let `rho : H -> GL_n(k)`, `n >= 1`, be a representation over a field of
characteristic three with `rho(z) = -1`.
1. No `a, c` in `S_-(H)` satisfy `c a = eps_-` and `c [w] a = 0`.
2. If `rho(w)` has eigenvalue `-1`, no `b, c` in `S_-(H)` satisfy `c e_- b = eps_-`.

*Proof.* Extend `rho` linearly to `F_3[H]`. Then `rho(eps_-) = 2(1 - rho(z)) = 1`.
1. `rho(c) rho(a) = 1` in `M_n(k)` makes `rho(a)` invertible, so `rho(c) rho(w) rho(a) = 0`
   forces `rho(w) = 0`. That is impossible.
2. `rho(e_-) = 2(1 + rho(w))`, and `rho(c) rho(e_-) rho(b) = 1` forces `1 + rho(w)` to be
   invertible. QED

**Corollary 4 (where supports cannot live).** In each of the following cases Theorem 3 applies.
* **Finite orbit.** Some left `R`-module has a nonzero vector with finite `H`-orbit. Its
  `F_3`-span is a finite-dimensional representation, and `z = -1` acts as `-1` on every
  `R`-module.
  * *All-ones stabilizer.* An example is the Cantor module of locally constant `F_3`-valued
    functions on `2^N`, with `(s_i f)(x) = f(sigma x)` on `[i]`, `0` off `[i]`, and
    `(t_i f)(y) = f(i y)`. Its all-ones vector is fixed by Thompson's `V` and by `w`. So no
    swap-separated pair is supported in the all-ones stabilizer together with `z`.
  * *Swap sign line.* The vector `v_- = 1_[0] - 1_[1]` has `w v_- = -v_-`. So no corner
    solution is supported in the stabilizer of the line `F_3 v_-`. That stabilizer contains
    every `s0 x t0 + s1 y t1` and `s0 x t1 + s1 y t0` with `x, y` fixing the all-ones vector.
* **Finite quotients.** Some finite quotient `H -> Q` does not kill `z`, and for part 2 does not
  kill `w`. Then the regular representation of `Q` cut by `eps_-` of the image of `z` is nonzero,
  and there `z` acts as `-1`. If both images are nontrivial, `w` has eigenvalue `-1` there,
  because `2(1 - zbar) . 2(1 - wbar) != 0`.

So the subgroup generated by the supports, `z` and `w` must satisfy three conditions:
* `z` lies in every finite-index subgroup;
* no nonzero vector of any `R`-module has a finite orbit;
* no characteristic-three representation sends `z` to `-1`.

These filters kill supports that
`subgroup-supported-one-sided-inverse-rigidity` cannot reach: nonsofic subgroups that still have
finite quotients or finite orbits.

## 5. Scope

* Theorem 1 is an exact reformulation. It constructs no solution and excludes none.
* **Gate.** `projective-ternary-group-is-f3-linear-sofic` (via stable finiteness) would refute
  (C), and so (P).
* **Obstructions still ruled out.**
  * *Trace.* `tr(p) = tr(eps_-) = 2` and `tr(p + [w]p[w]) = 1` in `F_3`, which is unordered.
  * *Finite-dimensional representations.* Every one factors through augmentation on `S_+` and
    vanishes on `S_-`, because `G` has no nontrivial finite-dimensional representations. That
    uses simplicity of `PG` and perfectness of `G`, which are recorded elsewhere and not
    re-proved here.
