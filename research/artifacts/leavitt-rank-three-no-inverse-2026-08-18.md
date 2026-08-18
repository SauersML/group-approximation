# The explicit rank-three Leavitt lift has no one-sided inverse

2026-08-18.  Full proof for `leavitt-rank-three-support-group-is-virtually-free`,
`subgroup-supported-one-sided-inverse-rigidity` and
`leavitt-rank-three-lift-has-no-one-sided-inverse`.

`leavitt-rank-three-lift-inverse-support-thirteen` said that any `B` with
`t~ B = 1` has `|supp B| >= 13`, imported from the Dykema--Heister--Juschenko
ULIE enumeration, which reaches only `n <= 11`.  The bound is now vacuous:
**there is no such `B` at any support.**  The same holds for the lift of
`s_0`, and for the compression `e t~ e` inside the corner `eAe`.  The
mechanism is that the whole support of the lift sits inside one *virtually
free* subgroup of `R^x`, and a virtually free group cannot host the Leavitt
defect.

## 0. Notation

```text
R  = L_(F_2)(1,2) = F_2<s_0,s_1,t_0,t_1 | t_i s_j = delta_ij, s_0t_0+s_1t_1 = 1>,
G  = R^x,      A = F_2[G],      pi : A ->> R,  pi([u]) = u,
S  = [s_0 s_1] (row),   T = [t_0 ; t_1] (column),   ST = 1,  TS = I_2,
Psi: M_2(R) -> R, Psi(M) = S M T,      Phi = Psi^(-1) : R -> M_2(R), Phi(r) = T r S.
```

`Psi` and `Phi` are the mutually inverse self-similarity isomorphisms of
`leavitt-rank-three-unit-lift-proof` (`binaryMatrixRingEquiv`, kernel-checked),
so `Psi` restricts to a group isomorphism `GL_2(R) -> G`.

From `leavitt-rank-three-unit-lift`:

```text
U_1 = [[1,0],[t_1,1]],   U_2 = [[t_0+1,1],[1,0]],   U_3 = [[0,1],[1,1]],
V_1 = [[1,s_1],[0,1]],   V_2 = [[s_0+1,1],[1,0]],   V_3 = U_3,
u_i = Psi(U_i),  v_i = Psi(V_i),   t_0 = u_1+u_2+u_3,   s_0 = v_1+v_2+v_3,
t~ = [u_1]+[u_2]+[u_3],           s~ = [v_1]+[v_2]+[v_3]   in A.
```

Write `K = <u_1,u_2,u_3>` and `K_s = <v_1,v_2,v_3>`, subgroups of `G`.

## 1. u_3 is the corner idempotent's group element

`leavitt-corner-idempotent-unital-surjection` builds `e = [g] + [g^2]` from
`g = (1+x)(1+y)`, `x = s_0t_1`, `y = s_1t_0`.  These are the same element:

```text
Phi(x)_(ij) = t_i s_0 t_1 s_j = delta_(i0)delta_(1j),   so Phi(x) = E_12,
Phi(y)_(ij) = t_i s_1 t_0 s_j = delta_(i1)delta_(0j),   so Phi(y) = E_21,
Phi(g) = (I+E_12)(I+E_21) = [[0,1],[1,1]] = U_3          (characteristic two),
```

so `g = u_3 in K`.  (Directly: `u_3 = Psi(U_3) = s_0t_1 + s_1t_0 + s_1t_1
= x + y + 1 + s_0t_0 = (1+x)(1+y) = g`.)  Hence `e in F_2[K]` as well, and the
corner lane and the rank-three lane are supported in the *same* subgroup — a
coincidence the corpus had not recorded, and the reason section 5 below closes
both at once.

## 2. K and K_s are free products (C_2 x C_2) * C_3

Put `r = U_3`.  In characteristic two `r^2 = [[1,1],[1,0]]` and `r^3 = I`, so
`r` has order three.  Set

```text
q_0 = U_2 U_3 = [[1,t_0],[0,1]],        q_1 = U_3^(-1) U_1 U_3 = [[1,t_1],[0,1]],
```

both verified by direct multiplication.  Upper unitriangular `2x2` matrices
over any ring commute and square to the identity in characteristic two, so
`q_0^2 = q_1^2 = I` and `q_0q_1 = q_1q_0 = [[1,t_0+t_1],[0,1]]`.  The three
nonidentity elements are distinct because `t_0`, `t_1`, `t_0+t_1` are nonzero
in `R`, so `V = <q_0,q_1> = C_2 x C_2`.  Since `U_2 = q_0 r^(-1)` and
`U_1 = r q_1 r^(-1)`,

```text
<U_1,U_2,U_3> = <q_0,q_1,r>,
```

and there is a canonical surjection `(C_2 x C_2) * C_3 ->> <q_0,q_1,r>`.  It
is injective, as follows.

**The t-subalgebra is free.**  Grade `R` by `deg s_i = 1`, `deg t_i = -1`; the
defining relations are homogeneous, so different degrees are independent.  For
words `alpha, beta` of equal length `n`, `t_alpha s_beta = delta_(alpha beta)`;
hence `sum_(|alpha|=n) c_alpha t_alpha = 0` gives `c_beta = 0` on right
multiplication by `s_beta`.  So the words in `t_0,t_1` are linearly
independent and `F_2<t_0,t_1> subset R` is a free associative algebra.  (The
same argument on the other side, multiplying on the left by `t_alpha`, makes
`F_2<s_0,s_1> subset R` free.)

**Nagao specialization.**  Freeness lets us define an algebra map

```text
sigma : F_2<t_0,t_1> -> F_2[X],    t_0 |-> X,   t_1 |-> X^2,
```

without imposing a relation `R` did not already have.  Entrywise, `sigma`
carries `q_0,q_1,r` and their inverses — all of which have entries in
`F_2<t_0,t_1>` — into `GL_2(F_2[X])`:

```text
Q_0 = [[1,X],[0,1]],   Q_1 = [[1,X^2],[0,1]],   R_0 = [[0,1],[1,1]],
V' = <Q_0,Q_1> = { I, E_12(X), E_12(X^2), E_12(X+X^2) } = C_2 x C_2.
```

Nagao's theorem (H. Nagao, *On GL(2,K[x])*, J. Inst. Polytech. Osaka City
Univ. Ser. A **10** (1959) 117--121; Serre, *Trees*, II.1.6) gives

```text
GL_2(F_2[X]) = GL_2(F_2) *_(B(F_2)) B(F_2[X]),
```

`B` the upper triangular subgroup.  Now `V' <= B(F_2[X])` and
`V' cap B(F_2) = {I}`, because the three nonidentity elements of `V'` have
non-constant upper-right entries `X, X^2, X+X^2`.  And `C = <R_0> = C_3` lies
in `GL_2(F_2)` with `C cap B(F_2) = {I}`, since `B(F_2)` has order two while
`C` has order three.  Every nonempty alternating word in `V' \ {I}` and
`C \ {I}` is therefore reduced in the amalgam, so by the normal form theorem
it is not the identity.  Hence

```text
<V',R_0> = V' * C = (C_2 x C_2) * C_3.
```

The composite `(C_2 x C_2) * C_3 ->> <q_0,q_1,r> -> <V',R_0>` matches
generators, so it is an isomorphism; the first map is therefore injective and

```text
<U_1,U_2,U_3> = (C_2 x C_2) * C_3,     K = Psi(<U_1,U_2,U_3>) = (C_2 x C_2) * C_3.
```

**The same for K_s.**  `V_2V_3 = [[1,s_0],[0,1]]` and `V_1 = [[1,s_1],[0,1]]`,
so `<V_1,V_2,V_3> = <[[1,s_0],[0,1]], [[1,s_1],[0,1]], r>` — the identical
shape with `s_i` for `t_i`.  Since `F_2<s_0,s_1>` is free too, the
specialization `s_0 |-> X`, `s_1 |-> X^2` runs verbatim and
`K_s = (C_2 x C_2) * C_3`.

**Consequence used below.**  Both `K` and `K_s` embed in `GL_2(F_2[X])`, a
finitely generated linear group over a finitely generated commutative ring, so
they are residually finite by Malcev.  (Equivalently: a free product of finite
groups is residually finite, and is virtually free, hence sofic.  The
embedding is the cheaper statement and is all that is used.)

## 3. Residual finiteness gives direct finiteness of F_2[K]

Let `H` be residually finite and `k` a field.  If `ab = 1` in `k[H]`, then for
every finite-index normal `N <= H` the ring map `phi_N : k[H] -> k[H/N]` has
`phi_N(a)phi_N(b) = 1` in a finite-dimensional algebra, which is directly
finite, so `phi_N(ba - 1) = 0`.  A nonzero element of `k[H]` has finite
support, and residual finiteness separates finitely many points into distinct
cosets of some `N`, so `intersection_N ker(phi_N) = 0`.  Hence `ba = 1`.

So `F_2[K]` and `F_2[K_s]` are directly finite.  (Elek--Szabo's soficity
theorem would also serve; it is not needed, and avoiding it keeps this
argument free of any imported machinery.)

**Corners inherit it.**  If `S` is directly finite, `e = e^2 in S`, and
`a,b in eSe` satisfy `ab = e`, then `(a+1-e)(b+1-e) = ab + (1-e) = 1` since
`a(1-e) = (1-e)b = 0`; direct finiteness gives `(b+1-e)(a+1-e) = 1`, i.e.
`ba = e`.  So `e F_2[K] e` is directly finite for every idempotent
`e in F_2[K]`.

## 4. Coset-projection rigidity

**Lemma.**  Let `H <= G` be a subgroup with `F_2[H]` directly finite, let
`alpha in F_2[H]`, and let `f in F_2[H]` be an idempotent with
`f alpha = alpha f = alpha` (take `f = 1` for the whole algebra).  If some
`beta in F_2[G]` satisfies `alpha beta = f` **or** `beta alpha = f`, then
`alpha` has a two-sided inverse inside `f F_2[H] f`, and `pi(alpha)` is a unit
of `R`.

*Proof.*  Decompose `F_2[G] = directsum_(Hg) F_2[Hg]` over right `H`-cosets.
Left multiplication by `alpha in F_2[H]` preserves every summand, and
`f in F_2[H]`, so comparing components of `alpha beta = f` gives
`alpha beta_H = f` with `beta_H` the component of `beta` in `F_2[H]`.  Put
`b = f beta_H f`; then `alpha b = (alpha f) beta_H f = alpha beta_H f = f`.
Direct finiteness of `f F_2[H] f` (section 3) gives `b alpha = f`.  Applying
the ring map `pi` and writing `p = pi(f)`, an idempotent of `R`:
`pi(alpha)pi(b) = pi(b)pi(alpha) = p`.  For the left-sided hypothesis, run the
same argument with left cosets `gH` and right multiplication.  When `p = 1`,
`pi(alpha)` is a unit of `R`.  ∎

The point is that a one-sided inverse cannot escape the subgroup: whatever the
partner looks like, only its `H`-component matters, and inside `F_2[H]` the
one-sidedness collapses.

## 5. The theorem

`pi(t~) = t_0` and `pi(s~) = s_0`, and neither is a unit of `R`: a two-sided
inverse `c` of `t_0` would give `c = c(t_0s_0) = (ct_0)s_0 = s_0`, hence
`s_0t_0 = 1`; then `s_1t_1 = 1 + s_0t_0 = 0` in characteristic two and
`1 = (t_1s_1)^2 = t_1(s_1t_1)s_1 = 0`.  Likewise `s_0c = 1` forces
`c = t_0(s_0c) = (t_0s_0)c`... more directly, `s_0 c = 1` with `t_0s_0 = 1`
gives `c = (t_0s_0)c = t_0(s_0c) = t_0`, so `s_0t_0 = 1` and the same
contradiction.  This is `binary-leavitt-algebra-not-directly-finite`.

Apply the Lemma with `H = K`, `f = 1`, `alpha = t~`:

```text
t~ has no right inverse and no left inverse in F_2[G].
```

Apply it with `H = K_s`, `f = 1`, `alpha = s~`: likewise for `s~`.

Apply it with `H = K`, `f = e = [g]+[g^2]` — legitimate by section 1, `e` is
an idempotent of `F_2[K]` — and `alpha = a = e t~ e`, which satisfies
`ea = ae = a`.  Since `g^3 = 1` and `1+g+g^2 = 0` in `R`, `pi(e) = g+g^2 = 1`,
so `pi(a) = t_0`, and the Lemma would make `t_0` a unit:

```text
e t~ e has no one-sided inverse in e F_2[G] e.
```

## 6. What this does and does not settle

It does **not** decide Kaplansky's Direct Finiteness Conjecture, which remains
open in positive characteristic.  It closes one concrete mechanism.  Precisely:

* `leavitt-rank-three-lift-inverse-support-thirteen` is superseded — its
  conclusion now holds vacuously, and by a route that does not use the
  Dykema--Heister--Juschenko machine enumeration at all;
* the compression `a = e t~ e`, `b = e s~ e` named in the Attempts of
  `leavitt-corner-one-sided-lift-exists`, whose only remaining gap was the
  equation `ab = e`, is refuted: **no** `b` completes that `a`;
* the support-three lift of `s_0` is excluded as the right factor in
  `left-invertible-lift-of-s0-in-leavitt-group-algebra`.

What survives untouched is everything whose support is not confined to a
subgroup with directly finite group algebra.  The Lemma is exactly a
statement about that confinement, so the reading is sharp: **the Kaplansky
frontier for `F_2[R^x]` lies outside the virtually free part of `R^x`.**  That
is consistent with, and points back at, `openai-leavitt-unit-nonsofic` — the
whole reason this group was chosen is that it is *not* sofic, and the elements
built so far had accidentally landed in a sofic (indeed virtually free)
subgroup where no counterexample can live.

An exact bounded search of the corner was also run before this proof (radius
7, 4604 candidate group elements, no solution); the theorem replaces that
finite negative evidence, and the search is not relied on anywhere.

## 7. Checks

* `t_0 = u_1+u_2+u_3`: `U_1+U_2+U_3 = [[t_0,0],[t_1,0]]` in characteristic
  two, and `Psi([[t_0,0],[t_1,0]]) = s_0t_0t_0 + s_1t_1t_0 = (s_0t_0+s_1t_1)t_0
  = t_0`.
* `U_2` is invertible: `[[a,1],[1,0]]^(-1) = [[0,1],[1,a]]` in characteristic
  two, both orders checked.
* `q_0 = U_2U_3` and `q_1 = U_3^(-1)U_1U_3` were multiplied out entry by
  entry; `U_3^(-1) = U_3^2 = [[1,1],[1,0]]`.
* `sigma` is applied only to matrices whose entries lie in `F_2<t_0,t_1>`
  (resp. `F_2<s_0,s_1>`), including inverses, so it is a group homomorphism on
  the subgroup in question.
* The amalgam argument needs both intersections trivial; `B(F_2)` has order
  two, which is what kills `C cap B(F_2)`, and non-constancy of `X, X^2,
  X+X^2` is what kills `V' cap B(F_2)`.
* The Lemma's coset decomposition is by RIGHT cosets for a right inverse and
  by LEFT cosets for a left inverse; the summands are preserved by left
  (resp. right) multiplication by `F_2[H]` in the respective case.
* `pi(e) = 1` uses `1+g+g^2 = 0`, which is `U_3^2+U_3+I = 0`, checked
  entrywise.

## 8. What would falsify this

The self-similarity `Psi` and the explicit `U_i` (both already in the corpus
and the second kernel-checked); freeness of `F_2<t_0,t_1>` and
`F_2<s_0,s_1>` in `R`; Nagao's amalgam decomposition of `GL_2(K[x])`; and
Malcev's theorem.  Everything else is entrywise `2x2` arithmetic in
characteristic two, reproduced above.  The one step worth an independent check
is the identification `q_0 = U_2U_3`, `q_1 = U_3^(-1)U_1U_3`, since the whole
free-product structure is read off from it.
