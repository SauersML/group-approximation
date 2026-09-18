---
rg: 2
id: p22-double-parabolic-is-not-lef-proof
kind: route
title: Relations P1-P3 make Ad g map the right-orbit group of x_13(1) into itself, pigeonhole or Zariski closure makes it onto, and the centralizing element x_12(1) then kills the head
target: p22-double-parabolic-is-not-lef
requires: []
artifacts:
  - experiments/p22-conjugation-pigeonhole-2026-09-17/pigeonhole_check.py
  - experiments/p22-conjugation-pigeonhole-2026-09-17/integral_check.py
---

Notation is as in the target. Everything is proved here. The only citations
are textbook facts about linear algebraic groups: a closed subgroup has
finitely many components, and dimension is monotone on irreducible closed
sets. Both artifacts exit 0.
* `pigeonhole_check.py` checks every matrix identity below exactly over
  `J = F_2<S,T|TS=1>`, in the normal form `S^i T^j`.
* `integral_check.py` checks the signed identities exactly over
  `J_Z = Z<S,T|TS=1>`.

## Step 0. The universal ring

Let `J_Z = Z<S,T | TS = 1>`. It has `Z`-basis `S^i T^j` with `i, j >= 0`,
because `TS -> 1` is a confluent rewriting system with no overlaps. Put
`Q = 1 - ST`. Then:
* `Q^2 = Q`, since `(ST)^2 = S(TS)T = ST`;
* `QS = S - STS = 0`;
* `TQ = T - TST = 0`;
* `Q != 0`, since `ST` is a basis monomial other than `1`.

For a ring `R` with `ts = 1`, the rule `S -> s`, `T -> t` defines a ring
map `J_Z -> R`, which sends `Q` to `q = 1 - st`. It induces a group map
`P_{2,2}(J_Z) -> P_{2,2}(R)` that sends each elementary letter to the same
letter. So every identity among words in elementary matrices that holds over
`J_Z` holds over `R`. `integral_check.py` verifies all the identities of
Steps 1-2 over `J_Z`. Hand verification follows. Over `R`, `h = x_13(q)` is
nontrivial exactly when `st != 1`.

## Step 1. The Levi element g

Write `x_ij(a) = 1 + a e_ij`, so `x_ij(a)^{-1} = x_ij(-a)`. In the rank-two
block on indices 1,2, the Whitehead element is
`w = x_12(s) x_21(-t) x_12(s)`. It works out to `[[q, s],[-t, 0]]`:
* `x_12(s) x_21(-t) = [[1-st, s],[-t, 1]]`;
* multiplying by `x_12(s)` on the right gives
  `[[q, qs + s],[-t, -ts + 1]] = [[q, s],[-t, 0]]`, using `qs = 0`.

Next, `K = x_21(1) x_12(-1) x_21(1) = [[0,-1],[1,0]]`. Hence
`u2 := wK = [[s, -q],[0, t]]`. Its inverse is
`K^{-1} w^{-1} = [[t, 0],[-q, s]]`. Check directly:
* `u2 [[t,0],[-q,s]] = [[st + q, -qs],[-tq, ts]] = I`;
* `[[t,0],[-q,s]] u2 = [[ts, -tq],[-qs, q + st]] = I`.

Put `g = diag(u2, 1_2)`. It lies in the left Levi `EL_2(R) x 1` of `P`.

## Step 2. The relations

In the notation `n(Y)`, with `E_11` the matrix unit:
* `u = x_13(1) = n(E_11)`;
* `e = x_12(1) = diag(x(1), 1)`, in the left Levi;
* `r1 = diag(1, B1)` with `B1 = [[1,-1],[0,1]]`, so
  `B1^{-1} = [[1,1],[0,1]]`;
* `r2 = diag(1, B2)` with `B2 = [[1,0],[-s,1]] [[1,-1],[0,1]]`, so
  `B2^{-1} = [[1,1],[0,1]] [[1,0],[s,1]] = [[1+s, 1],[s, 1]]`.

Levi conjugation acts by `diag(A,B) n(Y) diag(A,B)^{-1} = n(A Y B^{-1})`.
Each relation follows.
* **(P1)** `g` is in the left Levi and `r1, r2` are in the right Levi.
  These factors commute.
* **(P2)** `g u g^{-1} = n(u2 E_11) = n(s E_11) = x_13(s)`, because the first
  column of `u2` is `(s, 0)`. Also:
  * `r_i u r_i^{-1} = n(E_11 B_i^{-1})`, which is `n` of the first row of
    `B_i^{-1}` placed in row 1;
  * these rows are `(1+s, 1)` for `i = 2` and `(1, 1)` for `i = 1`;
  * `n` is additive, so `(r2 u r2^{-1})(r1 u r1^{-1})^{-1} = n((s,0) in row 1) = x_13(s)`.
* **(P3)** `[e,u] = 1`, because `x_12(1)` and `x_13(1)` commute (Steinberg:
  `[x_12, x_13] = 1`, since `2 != 3` and `1 != 3`). Also `[e,r_i] = 1`,
  because `e` is in the left Levi.
* **(H)** `g^{-1} u g = n(u2^{-1} E_11)`, and the first column of `u2^{-1}`
  is `(t, -q)`. So `g^{-1} u g = x_13(t) x_23(-q)`. Now `e = x_12(1)`
  commutes with `x_13(t)`, and `e x_23(b) e^{-1} = x_13(b) x_23(b)`. Hence
  `e (g^{-1}ug) e^{-1} = x_13(t - q) x_23(-q)`, and
  `[e, g^{-1}ug] = x_13(t-q) x_23(-q) x_23(q) x_13(-t) = x_13(-q) = h^{-1}`.

## Step 3. Pigeonhole in a finite image

**Lemma 3.** Let `G` be a group containing elements `g, e, u, r1, r2` that
satisfy (P1)-(P3). Put `R = <r1, r2>` and let
`A = < r u r^{-1} : r in R >`. Then:
* (i) `g A g^{-1} <= A`;
* (ii) `e` centralizes `A`;
* (iii) if `g A g^{-1} = A`, in particular if `A` is finite, then
  `[e, g^{-1} u g] = 1`.

*Proof.*
* (i) Take `r in R`. By (P1), `g` commutes with `r`, so
  `g (r u r^{-1}) g^{-1} = r (g u g^{-1}) r^{-1}`. By (P2) this equals
  `(r r2) u (r r2)^{-1} . ((r r1) u (r r1)^{-1})^{-1}`, which lies in `A`.
  So `g` maps each generator of `A` into `A`.
* (ii) By (P3), `e` commutes with `u` and with `R`, hence with every
  `r u r^{-1}`.
* (iii) If `A` is finite, the map `x -> g x g^{-1}` is injective from `A`
  into `A`, hence onto. So `g A g^{-1} = A`, which gives `g^{-1} A g = A`.
  Then `g^{-1} u g` lies in `A` and commutes with `e` by (ii). QED.

## Step 4. Zariski closure in a linear image

**Lemma 4.** Let `k` be a field and let `rho : G -> GL_n(k)` be a
homomorphism, with `G, g, e, u, R, A` as in Lemma 3. Then
`rho([e, g^{-1} u g]) = 1`.

*Proof.* Let `K` be the Zariski closure of `rho(A)`. It is a closed
subgroup of `GL_n` over the algebraic closure of `k`. Let `c` be conjugation
by `rho(g)`. It is an automorphism of the variety `GL_n`.
* **`c` maps `K` into `K`.** By Lemma 3(i), `c(rho(A)) <= rho(A)`. As `c`
  is a homeomorphism in the Zariski topology, `c(K) = closure of c(rho(A))`,
  which lies in `K`.
* **`c(K)` is all of `K`.** `c(K)` is a closed subgroup of `K` isomorphic to
  `K`. Its identity component `c(K^0)` is an irreducible closed subset of
  the irreducible `K^0`, of the same dimension, so `c(K^0) = K^0`. Then
  `c(K)` is a union of `[K : K^0]` cosets of `K^0` inside `K`, which has
  exactly that many, so `c(K) = K`.
* **The head dies.** Hence `rho(g)^{-1} K rho(g) = K`, and
  `rho(g^{-1} u g)` lies in `K`. The centralizer of `rho(e)` is Zariski
  closed and contains `rho(A)` by Lemma 3(ii), so it contains `K`. Therefore
  `rho(e)` commutes with `rho(g^{-1} u g)`. QED.

Finite-dimensional unitary representations are the case `k = C`. Lemma 4
does not require `A` to be finite, and it covers every Loewy length.

## Step 5. Assembly of the theorem

**Proof of parts (a) and (b).** Parts (a) and (b) of the target are Lemmas
3 and 4. They apply to any homomorphism from `Gamma_pig`.

**Proof of part (c).**
* **The relations hold in `P`.** By Step 2 they hold in `P_{2,2}(R)`, so
  `Gamma_pig -> P_{2,2}(R)` is a homomorphism. It sends the word
  `[e, g^{-1}ug]` to `h^{-1}`.
* **Finite quotients and linear representations.** Any finite quotient of
  `P` restricts to a finite image of `Gamma_pig`, and Lemma 3 kills
  `h^{-1}`. A finite-dimensional representation of `P` over any field is
  handled by Lemma 4 in the same way.
* **Non-linearity.** If `st != 1`, then `h != 1`. So `P` is not residually
  finite, and it has no faithful finite-dimensional representation.

**`P` is not LEF.** Write words in the ten letters `g, e, u, r1, r2` and
their inverses. Let `W` be the finite set of all prefixes of:
* the 6 relator words (P1)-(P3);
* the word `[e, g^{-1}ug]`.

Take `F` to be the set of their values in `P`, together with `1` and the
ten letters. Suppose
`phi : F -> K` is injective and satisfies `phi(xy) = phi(x) phi(y)` whenever
`x, y, xy` all lie in `F`, with `K` a finite group. Then:
* by induction along prefixes, each relator evaluates in `K` to
  `phi(1) = 1`;
* so `phi` of the five generators satisfies (P1)-(P3) in the finite group
  `K`;
* the head word evaluates to `phi(h^{-1})`, which is not `phi(1) = 1`, by
  injectivity.

Lemma 3 says the head word evaluates to `1`. This is a contradiction, so
`P` is not LEF.

**`Gamma_pig` is not residually finite.** It is finitely presented. Its
element `[e, g^{-1}ug]` is nontrivial, since its image in `P_{2,2}(J)` is
nontrivial, and it dies in every finite quotient. QED.

## Step 6. EL_4 and general rings

* **`EL_4`.** `P_{2,2}(R)` is a subgroup of `EL_4(R)`, and LEF passes to
  subgroups. So `EL_4(R)` is not LEF whenever `ts = 1 != st`.
* **`EL_n`.** The same holds for `EL_n(R)` with `n >= 4`, via the corner
  embedding.
* **No Steinberg presentation.** The finite presentation of `St_4(J)` is
  never used. The finitely presented group is `Gamma_pig` itself.

## Step 7. The operator-norm gap (why this is not (HC))

**Lemma 7a (the orbit group in P).** In `P`, `A = n(E_11 V)`, where `V` is
the additive span of the rows `(1,0) B^{-1}` for `B` in the right block of
`R`. `V` is stable under right multiplication by that block. On `A`,
`Ad g` is `n(E_11 v) -> n(E_11 s v)`. This map is injective and has image
`n(E_11 sV)`, which is a proper subgroup of `A`.

*Proof.*
* **Form of `A`.** Every `r u r^{-1}` equals `n(E_11 (1,0) B^{-1})`, and
  `n` is additive.
* **Action of `g`.** Take `v` in `V`. Then
  `g n(E_11 v) g^{-1} = n(u2 E_11 v) = n(E_11 s v)`, since `u2 E_11 = s E_11`.
* **Injective.** If `s v = 0`, then `v = t s v = 0`.
* **Not onto.** `(1,0)` lies in `V`. Suppose `(1,0) = s v` with `v` in
  `R^2`. Then `s a = 1` for the first entry `a` of `v`. That gives
  `t = t s a = a`, and then `s t = 1`, a contradiction. QED.

So the orbit group is a Baumslag-Solitar-type configuration inside the
abelian radical: an injective, non-surjective endomorphism, left
multiplication by `s`, that is implemented by conjugation.

**Lemma 7b (necessary shape of every head survivor).** Let `sigma` be a
unitary representation of `P`, or any `*`-representation of `C*(P)`, with
`sigma(h) != 1`. Put `D = C*(sigma(A))`. It is abelian, since `A <= N`, so
`D = C(Y)`. Then `Ad sigma(g)` restricts to a unital injective
`*`-endomorphism of `D` that is not onto. Its dual `f : Y -> Y` is a
continuous surjection that is not injective.

*Proof.*
* By Lemma 3(i), `Ad sigma(g)` maps the generators of `D` into `D`, so it
  maps `D` into `D`. It is injective because it is an automorphism of
  `B(H)`.
* Suppose it were onto. Then `Ad sigma(g)^{-1}` maps `D` onto `D`, so
  `sigma(g^{-1}ug)` lies in `D`.
* `sigma(e)` commutes with `sigma(A)` by Lemma 3(ii), hence with `D`. So it
  commutes with `sigma(g^{-1}ug)`, and `sigma(h) = 1`. This contradicts the
  hypothesis.
* Gelfand duality turns an injective, non-surjective unital map into a
  surjective, non-injective `f`. QED.

**Remarks.**
* Lemma 7b applies to `lambda_P`, which keeps `h`. There `Y` is the dual
  group of `V` and `f` is dual to left multiplication by `s`.
* Proper unital endomorphisms of abelian subalgebras implemented by
  unitaries occur in quasidiagonal algebras. For example, `Ad t` maps
  `C*(a)` onto `C*(a^2)` in `C*(BS(1,2))`, which is quasidiagonal
  (amenable and residually finite).
* So Lemma 7b is no obstruction in the norm corona. The pigeonhole kills
  exactly the models in which the hull of `sigma(A)` is co-Hopfian under
  `Ad sigma(g)`. That covers finite groups, Zariski closures, and compact
  Lie groups, but not abelian `C*`-algebras with infinite spectrum.
* The MF question for `P_{2,2}(J)` therefore remains open, exactly as
  stated in `p22-head-survival-forces-regular-weak-containment`. By Lemma 7b
  it is now sharpened: an MF survivor must realize `f` non-injectively, and
  by Step 5 it cannot be LEF.
