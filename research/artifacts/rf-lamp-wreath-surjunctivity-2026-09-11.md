# Permutational wreath products with residually finite lamps over surjunctive groups are surjunctive

Lane `gottschalk-positive`, 2026-09-11. Supports the Cairn claims
`rf-lamp-wreaths-over-surjunctive-bases-are-surjunctive`,
`kun-thom-nonsofic-wreaths-are-surjunctive` and
`surjunctive-nonsofic-group-exists`.

## Statements

**Theorem 1.** Let `G` be a group, `X` a left `G`-set and `A` a residually
finite group. Put `N = direct_sum_(x in X) A` and
`W = A wr_X G = N semidirect G`, where `(g.n)(x) = n(g^-1 x)` and there are no
internal automorphism twists. Then `W` is surjunctive if and only if `G` is
surjunctive.

**Corollary 2.** Let `Gamma <= G` be infranormal and not normal, with both
groups Kazhdan and `G` residually finite. This includes Theorem E of Kun--Thom,
arXiv:2608.06222, where `Gamma = EL_r(F_q[x_1,...,x_d])` and
`G = EL_r(F_q[x_1^(+-1),...,x_d^(+-1)]) semidirect SL_d(Z)`, `r,d >= 3`. Then
`W = (Z/2Z) wr_(G/Gamma) G` is surjunctive and not sofic. In particular some
finitely generated surjunctive group is not sofic: surjunctivity does not
characterize soficity. Problem 1.1 of Bowen--Chapman, arXiv:2511.06586, asks
whether all surjunctive groups are sofic; this is a negative answer.

The proof uses no finite approximation of `W`, of `G/Gamma`, or of any coset
action. It reduces everything to surjunctivity of the subgroups
`G_U = intersection_(s in U) Stab_G(s)` for finite `U` in `X`. These are
subgroups of `G`, hence surjunctive when `G` is.

## Conventions and standard facts

A cellular automaton over a group `Lambda` with finite alphabet `B` has a
finite memory `M` in `Lambda` and a local rule `mu: B^M -> B`, and

```text
tau(x)(lambda) = mu( (x(lambda m))_(m in M) ).
```

It commutes with left shifts `(lambda'.x)(lambda) = x(lambda'^-1 lambda)`.
`Lambda` is surjunctive when every injective such map is surjective.

* **(F1)** Curtis--Hedlund--Lyndon holds for every group: a continuous map
  of `B^Lambda` commuting with left shifts is a cellular automaton. So the
  inverse of a bijective cellular automaton is one.
* **(F2)** A subgroup `Lambda_0` of a surjunctive group `Lambda` is
  surjunctive. A cellular automaton over `Lambda_0` defines one over `Lambda`
  with the same memory and rule. On each left coset `lambda Lambda_0` it acts
  as a copy of the original through `h -> lambda h`, so injectivity and
  surjectivity transfer in both directions.
* **(F3)** The image of `B^Lambda` under a continuous map is compact, hence
  closed.
* **(F4)** Residually finite groups are surjunctive (Lawton; see
  Ceccherini-Silberstein--Coornaert, *Cellular Automata and Groups*,
  Section 3.3).

A *finite-memory map* on `C^G` is `rho(y)(g) = mu_g( (y(gp))_(p in P) )`, with
`P` finite containing `1` and independent of `g`, and rules `mu_g` that may
depend on `g`.

## 1. Transplanting to coset spaces

Let `H <= W`, `Omega = H\W` with right action `(Hw).u = Hwu`, and
`pi: W -> Omega`, `pi(w) = Hw`. For a cellular automaton `tau = (M, mu)` over
`W` define

```text
tau_Omega(y)(omega) = mu( (y(omega . m))_(m in M) ),     y in B^Omega.
```

**Lemma 1.1.** `tau(pi^* y) = pi^*(tau_Omega y)`. Consequently `tau_Omega` is
injective whenever `tau` is.

*Proof.* `tau(pi^* y)(w) = mu((y(Hwm))_m) = tau_Omega(y)(Hw)`. If
`tau_Omega y = tau_Omega y'`, then `tau(pi^* y) = tau(pi^* y')`, so
`pi^* y = pi^* y'`, and `y = y'` because `pi` is onto. QED

**Lemma 1.2.** Let `𝓗` be a family of subgroups of `W` such that every finite
`F` in `W` is mapped injectively by some `pi_H`, `H in 𝓗`. If `tau_(H\W)` is
surjective for every `H in 𝓗`, then `tau` is surjective.

*Proof.* Let `z in B^W` and `F` finite. Choose `H` with `pi_H` injective on `F`
and `y in B^(H\W)` with `y(pi_H w) = z(w)` for `w in F`. Pick `y'` with
`tau_(H\W) y' = y`. By Lemma 1.1, `tau(pi_H^* y') = pi_H^* y`, which agrees with
`z` on `F`. So the image of `tau` is dense, and it is closed by (F3). QED

## 2. Marked-site coset spaces

For finite `S` in `X` and a normal subgroup `A_0` of finite index in `A`, put
`Abar = A/A_0` and

```text
H_(S,A_0) = { (n,1) in W : n(s) in A_0 for every s in S }.
```

**Lemma 2.1 (separation).** The family of all `H_(S,A_0)` satisfies the
hypothesis of Lemma 1.2.

*Proof.* Let `w = (n,g)` and `w' = (n',g')` be distinct elements of a finite
`F`. Then

```text
w' w^-1 = ( n' . ((g' g^-1) . n^-1), g' g^-1 ).
```

If `g' != g` it lies outside `N`. If `g' = g` it equals `(n' n^-1, 1)`, a
nontrivial element of `N`. Let `S` contain the supports of these finitely
many elements, and choose `A_0` of finite index avoiding their finitely many
nontrivial values. No `w' w^-1` then lies in `H_(S,A_0)`. QED

**Coordinates.** `(nu,1)(n,g) = (nu n, g)`, so `H(n,g) = H(n',g')` exactly
when `g = g'` and `A_0 n'(s) = A_0 n(s)` for all `s in S`. Thus

```text
Omega_S := H_(S,A_0)\W  ~=  Abar^S x G,     H(n,g) -> ((A_0 n(s))_s, g),
(a,g) . (n_1,g_1) = ( a . nu_(n_1)(g), g g_1 ),   nu_(n_1)(g)(s) = A_0 n_1(g^-1 s),
```

because `(n,g)(n_1,g_1) = (n.(g.n_1), g g_1)` and `(g.n_1)(s) = n_1(g^-1 s)`.

Fix a cellular automaton `tau` over `W` with memory `M` and rule `mu`, and
write `m = (n_m, g_m)` and `nu_m = nu_(n_m)`. For `U` in `S`, with the same
`A_0`, write `Omega_U = Abar^U x G` and `tau_U = tau_(Omega_U)`:

```text
tau_U(y)(a,g) = mu( ( y(a . nu_m(g)|_U, g g_m) )_(m in M) ).        (2.1)
```

For `U = empty`, `Omega_empty = G` and `tau_empty(y)(g) = mu((y(g g_m))_m)` is
an ordinary cellular automaton over `G`.

**Lemma 2.2 (strata).** Let `L = union_m supp(n_m)`, a finite set. For
`s in X` put

```text
Z_s = { g in G : g^-1 s in L },     G_s = Stab_G(s),
G_U = intersection_(s in U) G_s     (G_empty = G).
```

1. `Z_s` is a finite union of right cosets of `G_s`, and so is `Z_s F` for
   every finite `F` in `G`.
2. If `g` is not in `Z_s`, then `nu_m(g)(s) = 1` for every `m`.
3. `nu_m(kg)|_U = nu_m(g)|_U` for `k in G_U`. So `tau_U` commutes with the
   left translations `(l_k y)(a,g) = y(a, k^-1 g)`, `k in G_U`.

*Proof.* (1) `{g : g^-1 s = u}` is empty or equals `g_u G_u = G_s g_u` for any
`g_u` with `g_u u = s`, and right multiplication sends right cosets to right
cosets. (2) Each `supp(n_m)` is contained in `L`. (3) `(kg)^-1 s = g^-1 s` for
`s in U`. QED

**Lemma 2.3 (slices).** Let `V` be contained in `U`. For `lambda in Abar^(U\V)`
write `y_lambda(b,g) = y((b,lambda),g)`. If `g` lies in no `Z_s` with
`s in U\V`, then

```text
tau_U(y)((b,lambda), g) = tau_V(y_lambda)(b, g).
```

*Proof.* By Lemma 2.2(2), every `nu_m(g)` is trivial on `U\V`, and (2.1) reads
only the points `((b . nu_m(g)|_V, lambda), g g_m)`. QED

For a map `phi` of `B^(Omega_V)`, its slicewise extension `phi^[U]` on
`B^(Omega_U)` is `(phi^[U] y)_lambda = phi(y_lambda)`. Identifying
`B^(Omega_U)` with `C^G`, `C = B^(Abar^U)`, all maps above are finite-memory
maps on `C^G`.

## 3. The coset-region lemma

**Lemma 3.1.** Let `K <= G` be surjunctive, `C` a finite alphabet, and `rho`
an injective finite-memory map on `C^G` with memory `P`. Suppose:

* `R` in `G` is a finite union of right cosets of `K`;
* `rho(y)(g) = y(g)` for every `y` and every `g` not in `R`;
* `mu_(kg) = mu_g` for every `k in K` and `g in R`.

Then `rho` is bijective, and `rho^-1` is a finite-memory map which is the
identity off `R` and has left-`K`-invariant rules on `R`.

*Proof.* Write `R = K h_1 ⊔ ... ⊔ K h_r`. The set `RP` is a finite union of
right `K`-cosets, so `E = RP \ R = K e_1 ⊔ ... ⊔ K e_q`. Identify `R ⊔ E` with
`K x {1,...,r+q}` by `k h_i -> (k,i)` and `k e_j -> (k, r+j)`.

For `p in P`, `k h_i p` lies in the right coset `K h_i p`, which is one of the
`K h_(i')` or `K e_j`. If `f` is its chosen representative, then
`k h_i p = (k eta) f` with `eta = h_i p f^-1 in K` independent of `k`. By left
invariance, the output of `rho` at `k h_i` is a fixed function of the inputs at
the points `(k eta(i,p), label(i,p))`. Hence

```text
Psi( y|_R, y|_E ) = ( rho(y)|_R, y|_E )
```

is a cellular automaton over `K` with alphabet `C^(r+q)`, acting as the
identity on the `E`-labels.

*`Psi` is injective.* If `Psi(u,beta) = Psi(u',beta')`, then `beta = beta'`.
Extend `u ⊔ beta` and `u' ⊔ beta` by one common configuration outside `R ⊔ E`
to get `y` and `y'`. Off `R`, `rho(y) = y = y' = rho(y')`. On `R` the outputs
agree. Injectivity of `rho` gives `y = y'`, so `u = u'`.

Since `K` is surjunctive, `Psi` is bijective, and `Psi^-1` is a cellular
automaton over `K` by (F1).

*`rho` is onto.* Given `w in C^G`, let `(u,beta) = Psi^-1(w|_R, w|_E)`; then
`beta = w|_E`. Put `y = u` on `R` and `y = w` off `R`. Off `R`, `rho(y) = y = w`.
On `R`, `rho(y)|_R` depends only on `y|_(RP) = (u, w|_E)`, so it equals `w|_R`.

The formula `rho^-1(w)|_R = first component of Psi^-1(w|_R, w|_E)`, with
`rho^-1(w) = w` off `R`, gives the stated form of `rho^-1`. QED

## 4. Peeling the strata

Assume `G` is surjunctive. Fix an injective cellular automaton `tau` over `W`,
a finite `S` in `X`, and `A_0`. Fix a total order on the subsets of `S` that
refines cardinality.

**Proposition 4.1.** For every `U` in `S` there are a bijection `rho_U` of
`B^(Omega_U)` and a finite set `F_U` in `G` containing `1` such that:

* **(a)** `rho_U = Sigma_(U'_k) o ... o Sigma_(U'_1) o tau_U`, where
  `U'_1 < ... < U'_k` are the proper subsets of `U` and
  `Sigma_(U') = (rho_(U')^-1)^[U]`;
* **(b)** `rho_U(y)(a,g) = y(a,g)` for every `y`, every `a`, and every `g` not
  in `Q_U := intersection_(s in U) Z_s F_U^-1`;
* **(c)** `rho_U` and `rho_U^-1` are finite-memory maps commuting with left
  translations by `G_U`.

*Proof.* Induction on `|U|`.

**Base case.** For `U = empty`, `rho_empty = tau_empty` is an injective
cellular automaton over `G` (Lemma 1.1). It is bijective because `G` is
surjunctive, with inverse a cellular automaton by (F1). Condition (b) is
vacuous because `Q_empty = G`.

**Inductive step.** Let `|U| >= 1` and define `rho_U` by (a).
* Every `Sigma_(U')` is a bijective finite-memory map commuting with left
  translations by `G_(U')`, which contains `G_U`.
* `tau_U` is injective (Lemma 1.1) and commutes with the same translations
  (Lemma 2.2(3)).

So `rho_U` is an injective finite-memory map commuting with left translations
by `G_U`.

*Windows.* Let `P_0` contain `1` and all `g_m` (the memory of `tau_U`), and
let `P_j`, containing `1`, be the memory of `Sigma_(U'_j)`. Put `z_0 = tau_U y`
and `z_j = Sigma_(U'_j) z_(j-1)`. The value `z_k(.,g)` depends only on
`z_(k-1)` at the points `g P_k`, and so on down to `y` at `g P_k ... P_1 P_0`.
Put `P = P_k ... P_1 P_0` and

```text
F_U = P  union  ( union_(U' proper in U) P F_(U') ).
```

*Proof of (b).* Let `g` not lie in `Q_U`, and put
`V = { s in U : g F_U meets Z_s }`. Then `V != U`, and no point of `gP` lies in
`Z_s` for `s in U\V`, because `gP` is contained in `g F_U`.

1. **Proper subsets not contained in `V` do nothing on `gP`.** Suppose `U'`
   is not contained in `V`, and pick `s in U'\V`. A point `h in gP` in
   `Q_(U')` would satisfy `h F_(U')` meets `Z_s`. But `gP F_(U')` is contained
   in `g F_U`, which misses `Z_s`. So `h` is not in `Q_(U')`, and by (b) for
   `U'`, `Sigma_(U')` is the identity at `h` (the inverse of a map that fixes
   each coordinate off `Q_(U')` has the same property).
2. **On `gP`, `tau_U` is the slicewise `tau_V`.** By Lemma 2.3,
   `tau_U(y) = tau_V^[U](y)` at every point of `gP`.
3. **Subsets of `V` act slicewise.** For `U'` properly contained in `V`,
   `(rho_(U')^-1)^[U] = ((rho_(U')^-1)^[V])^[U]`.

Let `V = U'_(j_V)`. All proper subsets of `V` precede `V`, and no later
`U'_j` is a subset of `V`.

*Before stage `j_V`.* Induct on `j`, using (1)-(3) on the shrinking windows
`g P_k ... P_(j+1)`. The configuration `z_j` agrees on that window with the
slicewise extension of the `V`-setting partial composite of `tau_V` and the
already-applied `Sigma` for proper subsets of `V`. At `j = j_V - 1` that
composite is `rho_V`, so `z_(j_V - 1)` agrees with `rho_V^[U] y` on
`g P_k ... P_(j_V)`.

*At stage `j_V`.* `Sigma_V` at the points of `g P_k ... P_(j_V + 1)` reads only
that window, so `z_(j_V) = (rho_V^-1)^[U](rho_V^[U] y) = y` there.

*After stage `j_V`.* Every later `Sigma` is the identity at `g` by (1).
Therefore `rho_U(y)(.,g) = y(.,g)`.

*Proof of bijectivity and (c).* By Lemma 2.2(1), `Q_U` is a finite union of
right cosets of `G_U`: an intersection of right cosets of the `G_s`, `s in U`,
is empty or a right coset of `G_U`. Because `rho_U` commutes with left
translation by `G_U`, its rules at `kg` and `g` agree for `k in G_U`. By (F2),
`G_U` is surjunctive. Lemma 3.1, with `K = G_U`, `R = Q_U` and
`C = B^(Abar^U)`, shows that `rho_U` is bijective with a finite-memory inverse.
The inverse commutes with the same translations. QED

## 5. Proofs

*Proof of Theorem 1.*
* **Only if.** If `W` is surjunctive, so is its subgroup `G` (F2).
* **If.** Let `G` be surjunctive and `tau` an injective cellular automaton
  over `W`. For every `S` and `A_0`, Proposition 4.1 with `U = S` makes
  `rho_S = Sigma o tau_S` bijective, where `Sigma` is a composite of
  bijections. So `tau_S` is surjective. Lemmas 2.1 and 1.2 then show that
  `tau` is surjective. QED

*Proof of Corollary 2.*
* **Nonsofic.** Kun--Thom Theorem A proves `W` is not sofic.
* **Surjunctive.** Theorem E gives residual finiteness of `G`, hence
  surjunctivity by (F4). Theorem 1 with `A = Z/2Z` and `X = G/Gamma` makes `W`
  surjunctive.
* **Finitely generated.** `W` is generated by `G` and one lamp, since `G` acts
  transitively on `G/Gamma`, and `G` is finitely generated. QED

## Remarks

* **Iteration.** Finite iterated permutational wreath products with
  residually finite lamps over a surjunctive group are surjunctive.
* **Relation to the linear theorem.** Surjunctive groups have stably finite
  group algebras over finite fields. So Theorem 1 recovers the finite-field
  case of `rf-lamps-preserve-stable-finiteness-for-arbitrary-actions` when
  the base is surjunctive. The linear theorem, which covers all fields and
  assumes only stable finiteness of `k[G]`, is not superseded. Both proofs
  use marked lamp sites. The linear proof inducts through matrix algebras
  over stabilizer group algebras; this one inducts through right cosets of
  stabilizer intersections.
* **Relation to the sofic radical.** `sofic-radical-localizes-garden-of-eden-windows`
  constrains counting proofs. The argument here is not a counting proof. The
  nonsoficity of `W` lives in the coset action on `G/Gamma`, while
  surjunctivity only needs the stabilizer intersections `G_U`, which are
  subgroups of `G`.
* **What this does not settle.**
  * Gottschalk's conjecture.
  * Surjunctivity of the binary Leavitt unit group `L_(F_2)(1,2)^x`, which is
    not a permutational wreath product.
  * Surjunctivity of Kun--Thom group doubles `G *_Gamma G`.

  What it does show: the (T)-compression nonsoficity mechanism, in its
  permutational-wreath form over a surjunctive base, cannot produce a
  Gottschalk counterexample.
* **Relation to Bowen--Chapman.** arXiv:2511.06586 constructs a surjunctive
  non-cosofic invariant random subgroup of a free group, and records the group
  question as out of reach while no nonsofic group was known. Corollary 2 is
  the group version, available once Kun--Thom's nonsofic wreath products
  exist.
