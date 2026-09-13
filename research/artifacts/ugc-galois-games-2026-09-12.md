# Galois unique games: value, perfect completeness, symmetric SDP, and linear rounding

Date: 2026-09-12. Lane `ex-ugc`. Status: complete proofs of Theorems 1--4 and
Propositions 5--6 below. The quoted inputs are Bochner's theorem on finite
abelian groups and Bonami--Beckner hypercontractivity, the latter used only
in the tightness example of Section 6. **This neither proves nor refutes the
Unique Games Conjecture.** The literature check was bounded (Section 7).

## 1. The object

Let `G` be a finite group, `K <= G` a subgroup of order `k >= 2`, and `mu` a
symmetric probability measure on `G` (`mu(g) = mu(g^-1)`). Let `V = G/K` be
the set of left cosets `yK`, and fix a section `tau : V -> G` with
`tau(v) in v`. For `v in V` and `s in G` put

```text
c(v,s) = tau(s v)^-1 s tau(v)      (an element of K, since s tau(v) in s v = tau(s v) K).
```

The **Galois game** `Gal(G,K,mu)` is the unique game with vertex set `V`,
alphabet `K`, edge distribution "`v` uniform in `V`, `s ~ mu`, edge
`(v, s v)`", and constraint `f(s v) = c(v,s) f(v)` on that edge. Since
`c(s v, s^-1) = c(v,s)^-1` and `mu` is symmetric, the game is undirected.
Every constraint is a left translation of `K`, so this is a
`Max-2Lin(K)` instance on the Schreier graph of `mu` acting on `G/K`.
Changing `tau` relabels each vertex by a translation: it is a gauge change and
alters nothing below.

**The lift is a Cayley graph.** The map `(v,a) -> tau(v) a` is a bijection
`V x K -> G`. The edge `(v,s)` accepts `(a,b)` iff `b = c(v,s) a` iff
`tau(s v) b = s tau(v) a`. So the label-extended graph of the game is the left
Cayley graph `y ~ s y` of `(G,mu)`, and the fibres are the left cosets of `K`.
Conversely, suppose a unique game's label-extended graph is the left Cayley
graph of `(G,mu)` and its fibres are the left cosets of `K`. Then, up to gauge,
the game is `Gal(G,K,mu)`. This is the regular-cover case: the deck group `K`
acts on the right.

**Example (Khot--Vishnoi).** `G = F_2^N` with `N = 2^n`, `K` the Hadamard code
`{ (<z,j>)_(j in F_2^n) : z in F_2^n }`, of order `k = N`, and `mu` the
`epsilon`-noise measure (independent coordinate flips with probability
`epsilon`). This is the quotient construction behind the Khot--Vishnoi unique
games integrality gap; see Section 6.

## 2. Theorem 1: the value is transversal non-expansion

A **left transversal** of `K` is a set `T subset G` meeting every left coset
`yK` in exactly one point. Write `Phi_mu(T) = Pr_(t in T, s ~ mu)[s t notin T]`.

**Theorem 1.** `val Gal(G,K,mu) = max_T (1 - Phi_mu(T))`, the maximum over
left transversals of `K`.

*Proof.* A labeling `f : V -> K` gives `T_f = { t_v = tau(v) f(v) : v in V }`,
which is a left transversal. Every left transversal arises from exactly one
`f`. The edge `(v,s)` is satisfied iff `s t_v = t_(s v)`. Since `s t_v` lies in
the coset `s v`, whose unique point in `T_f` is `t_(s v)`, this holds iff
`s t_v in T_f`. As `v` is uniform in `V`, `t_v` is uniform in `T_f`. So the
value of `f` is `1 - Phi_mu(T_f)`. `square`

## 3. Theorem 2: perfect completeness is a free action

**Theorem 2.** Let `Lambda = <supp mu>`. Then `val Gal(G,K,mu) = 1` iff
`Lambda` acts freely on `G/K`, that is, iff `Lambda cap g K g^-1 = {e}` for
every `g in G`. When the Schreier graph is connected (`Lambda` transitive on
`G/K`) this says exactly that `Lambda` is a complement of `K`:
`Lambda K = G` and `Lambda cap K = {e}`.

*Proof.* By Theorem 1, value `1` means some left transversal `T` has
`s T subset T` for every `s in supp mu`. Since `G` is finite, `s T = T`, and so
`Lambda T = T`.

(`=>`) Take `t in T` and `lambda in Lambda cap t K t^-1`. Then `lambda t in T`
and `lambda t in t K`, so `lambda t = t` by the transversal property, and
`lambda = e`. Every coset has the form `tK` with `t in T`, and the conjugates
`t K t^-1` over `t in T` exhaust `{ g K g^-1 }`, because `gK = tK` gives
`g K g^-1 = t K t^-1`.

(`<=`) Suppose all stabilizers `Stab_Lambda(gK) = Lambda cap g K g^-1` are
trivial. For each `Lambda`-orbit `O` on `G/K`, pick one coset `g_O K` in `O`
and put `T = union_O Lambda g_O`. The set `Lambda g_O` meets the coset
`lambda g_O K` in `{ lambda' g_O : lambda'^-1 lambda in g_O K g_O^-1 }`, which
is `{lambda g_O}` by freeness. It meets no coset outside `O`. So `T` is a left
transversal with `Lambda T = T`, and its value is `1`. `square`

So perfect Galois games are exactly the free actions, and a Galois game is a
**gap** candidate only when `<supp mu>` has fixed points on `G/K` while some
transversal is nearly `mu`-invariant. This is the group-theoretic form of the
rigidity in `perfect-commuting-unique-game-is-classically-satisfiable`.

## 4. Theorem 3: the symmetric SDP is a positive-definite-function problem

The **basic SDP** has vectors `u_(v,a)` (`v in V`, `a in K`) with
`<u_(v,a), u_(v,a')> = 0` for `a != a'` and `sum_a |u_(v,a)|^2 = 1`. Its
objective is `E_(v,s) sum_a <u_(v,a), u_(s v, c(v,s) a)>`.

**Theorem 3.** If `mu` is conjugation-invariant, then

```text
SDP Gal(G,K,mu) = max { sum_g mu(g) phi(g) :  phi : G -> R positive definite,
                        phi(e) = 1,  phi(a) = 0 for all a in K \ {e} }.       (3.1)
```

*Proof.* (`>=`) By GNS, `phi(g) = <pi(g) xi, xi>` for a real orthogonal
representation `pi` and a unit vector `xi`. Put
`u_(v,a) = k^(-1/2) pi(tau(v) a) xi`. Within a vertex,
`<u_(v,a), u_(v,a')> = phi(a'^-1 a)/k`. This is `0` for `a != a'` and `1/k` on
the diagonal, so the constraints hold. On the edge `(v,s)`, write
`y = tau(v) a`. Then `tau(s v) c(v,s) a = s y`, and the edge term is
`k^-1 sum_a <pi(y) xi, pi(s y) xi> = k^-1 sum_a phi(y^-1 s^-1 y)`. Averaging over
`v` and summing over `a` makes `y` uniform on `G`. By symmetry and conjugation
invariance, `y^-1 s^-1 y ~ mu`. So the objective is
`sum_g mu(g) phi(g)`.

(`<=`) Given a feasible solution, set `w_y = u_(v,a)` for `y = tau(v) a` and
`M(y,y') = <w_y, w_y'>`. The feasible set, in terms of `M`, is: `M` positive
semidefinite; `M(y,y') = 0` for distinct `y,y'` in one left coset; and
`sum_(y in v) M(y,y) = 1` for each coset `v`. The objective is
`J(M) = (k/|G|) sum_y E_(s~mu) M(y, s y)`. For `g in G` put
`M^g(y,y') = M(g y, g y')`. Left multiplication maps cosets to cosets, so `M^g`
is feasible, and `J(M^g) = (k/|G|) sum_y E_s M(y, g s g^-1 y) = J(M)` by
conjugation invariance. The average `Mbar = E_g M^g` is feasible with the same
objective and is left-invariant. So `Mbar(y,y') = m(y^-1 y')` for a function
`m` on `G`. The diagonal is constant and sums to `1` over the `k` points of a
coset, so `m(e) = 1/k`. Put `phi = k m`. Then `phi` is positive definite, since
`Mbar` is PSD. Also `phi(e) = 1`, `phi(a) = 0` for `a in K \ {e}`, and
`J(Mbar) = E_s phi(s)`. Symmetry of `mu` lets us replace `phi` by its real
symmetric part without changing anything. `square`

The familiar gap certificate is (3.1) with `phi` a small mixture of
characters. For Khot--Vishnoi, `phi(y) = N^-1 sum_j (-1)^(y_j) = 1 - 2 wt(y)/N`.
This vanishes on nonzero Hadamard codewords (weight `N/2`) and gives
`SDP >= 1 - 2 epsilon`.

## 5. Theorem 4: over elementary abelian groups the SDP rounds with linear loss

**Theorem 4.** Let `G = F_p^N` for a prime `p`, `K <= G` of order `k = p^r`, and
`mu` symmetric. Suppose some `phi` as in (3.1) has `sum_g mu(g) phi(g) >= 1-epsilon`.
For instance, `SDP Gal(G,K,mu) >= 1-epsilon` supplies one (Theorem 3; `mu` is
conjugation-invariant because `G` is abelian). Then some **subgroup** complement
`T` of `K` satisfies

```text
val Gal(G,K,mu) >= 1 - Phi_mu(T) >= 1 - C_p epsilon log_p k,
C_p = 2p / ((p-1)(1 - cos(2 pi/p))),       C_2 may be taken 3/2.            (5.1)
```

Such a `T` can be found in time polynomial in `|G| |supp mu|`.

*Proof.* (i) **Bochner.** A real positive-definite function on the finite
abelian group `G` is `phi = sum_(chi in Ghat) w_chi chi`. Here
`w_chi = |G|^-1 sum_g phi(g) conj(chi(g)) >= 0`, `sum_chi w_chi = phi(0) = 1`, and
`w_chi = w_(conj chi)`.

(ii) **The label marginal is uniform.** Restriction `res : Ghat -> Khat` is a
surjective homomorphism. Put `nu = res_* w`, a probability measure on `Khat`.
For `a in K`, `phi(a) = sum_(psi in Khat) nu(psi) psi(a)`. So the Fourier
transform of `nu` is `delta_(a,0)`, and by Fourier inversion on `K`,
`nu(psi) = k^-1` for every `psi`.

(iii) **Most weight sits on high characters.** Put
`lambda_chi = sum_g mu(g) chi(g)`, which is real and at most `1`. Then
`sum_chi w_chi (1 - lambda_chi) <= epsilon`. For `eta > 0` let
`B = { chi : lambda_chi < 1 - eta }`; then `w(B) <= epsilon/eta`, and
`R = res(Ghat \ B)` has `|R|/k = nu(R) >= 1 - epsilon/eta`.

(iv) **A basis among high characters.** `Khat` is isomorphic to `F_p^r`, and a
proper subgroup has density at most `1/p`. Take `eta = 2p epsilon/(p-1)`
(for `p = 2`, `eta = 3 epsilon`). Then `|R|/k >= (p+1)/(2p) > 1/p` (`2/3` for
`p = 2`). So `R` spans `Khat` and contains a basis `psi_1, ..., psi_r`. Pick
`chi_i in Ghat \ B` with `res chi_i = psi_i`, so `lambda_(chi_i) >= 1 - eta`.

(v) **The complement.** Write `chi_i(y) = zeta^(Y_i(y))` with `Y_i : G -> F_p`
linear, and `Y = (Y_1, ..., Y_r) : G -> F_p^r`. If `a in K` has `Y(a) = 0`,
then every `psi_i` is trivial at `a`. Since they span `Khat`, `a = 0`. So `Y|_K`
is an isomorphism, `T = ker Y` has index `k` and meets `K` trivially, and every
coset `y + K` meets `T` exactly once. `T` is a left transversal.

(vi) **Its expansion.** `T` is a subgroup, so `t + s in T` iff `s in T`, and
`Phi_mu(T) = Pr_s[Y(s) != 0] <= sum_i Pr_s[chi_i(s) != 1]`. Every nontrivial
`p`-th root of unity `z` has `1 - Re z >= 1 - cos(2 pi/p)`. By Markov,
`Pr[chi_i(s) != 1] <= (1 - lambda_(chi_i))/(1 - cos(2 pi/p)) <= eta/(1 - cos(2 pi/p))`.
Summing over `r = log_p k` indices gives (5.1). For `p = 2` it gives
`r (3 epsilon)/2`.

(vii) **Algorithm.** The restrictions form a linear matroid on `Ghat`. The
greedy basis by decreasing `lambda_chi` maximizes the minimum `lambda` over bases.
So it achieves `min_i lambda_(chi_i) >= 1 - eta` whenever some basis does, and
it needs no SDP solve. `square`

**Remark.** The proof uses only the existence of a `K`-orthogonal
positive-definite certificate. Any such certificate for a Galois game over an
elementary abelian group, SDP or otherwise, therefore gives an explicit
*linear* labeling of value `1 - O_p(epsilon log k)`. Compare
Charikar--Makarychev--Makarychev for general unique games:
`1 - O(sqrt(epsilon log k))`.

## 6. Sharpness: the exponent hypothesis and the constant

**Proposition 5 (the exponent hypothesis cannot be dropped).** Take `G = Z_(2n)`,
`K = {0, n}`, and `mu` uniform on `{+1, -1}`. Then `Gal(G,K,mu)` is
`Max-2Lin(Z_2)` on the `n`-cycle with nontrivial holonomy. Its value is exactly
`1 - 1/n`, while `phi(x) = (1 + cos(pi x/n))/2` is admissible in (3.1) with
`sum mu phi = cos^2(pi/(2n)) = 1 - epsilon`, `epsilon = sin^2(pi/(2n)) <= pi^2/(4 n^2)`.
So `1 - val = 1/n >= (2/pi) sqrt(epsilon)`: over cyclic groups the loss is
square-root, not linear.

*Proof.* `G/K` is the `n`-cycle. Lifting once around it goes from `0` to `n`,
the nontrivial element of `K`. So the product of the constraints around the
cycle is nontrivial, and every labeling violates at least one of the `n` edges,
each of weight `1/n`. The arc `T = {0, ..., n-1}` violates exactly one. The
function `phi` is the character mixture `1/2 (chi_0) + 1/4 (chi_1 + chi_-1)`, so it
is positive definite, with `phi(0) = 1` and `phi(n) = 0`. `square`

**Proposition 6 (the linear rate is attained: Khot--Vishnoi).** In the example
of Section 1 (`G = F_2^N`, `N = 2^n`, Hadamard `K`, `epsilon`-noise `mu`), put
`t = epsilon n = epsilon log_2 k`. Then

```text
(1 - epsilon)^n  <=  val  <=  2^(-t/(1-epsilon)),     while   SDP >= 1 - 2 epsilon.
```

In particular, for `t <= 1`, `1 - t <= val <= 1 - t/2`. So `1 - val = Theta(epsilon log k)`,
matching Theorem 4 up to a constant. For `t -> infinity` it is the Khot--Vishnoi
gap.

*Proof.* The lower bound is Theorem 4's construction made explicit. The
characters `chi_(e_j)`, `j in F_2^n`, have `lambda = 1 - 2 epsilon`. Restricted to
`K` they give `z -> (-1)^(<z,j>)`, which are all characters of `K`. Taking `j`
over the standard basis gives `T = { y : y_(j_1) = ... = y_(j_n) = 0 }`, and
`1 - Phi(T) = (1-epsilon)^n`.

For the upper bound let `T` be any transversal, of density `alpha = 1/N`, and
`rho = 1 - 2 epsilon`. Then `1 - Phi(T) = N Stab_rho[1_T]`. Bonami--Beckner
hypercontractivity `|T_(sqrt rho) f|_2 <= |f|_(1+rho)` gives
`Stab_rho[1_T] = |T_(sqrt rho) 1_T|_2^2 <= alpha^(2/(1+rho))`, so
`1 - Phi(T) <= N^(-(1-rho)/(1+rho)) = 2^(-n epsilon/(1-epsilon))`. Finally `2^(-t)` is
convex and equals `1/2` at `t = 1`, so it is at most `1 - t/2` on `[0,1]`. `square`

## 7. Literature check (bounded) and scope

Searched on 2026-09-12: web queries on unique games over Cayley graphs and SoS
(2024), small-set expansion and UGC (2025), SoS integrality gaps for unique
games, and 2-to-1/2-to-2 games with perfect completeness (2025--2026). I also
used the repository's source record
`research/artifacts/unique-games-sos-algorithms-and-gaps-source-2026-09-12.md`.
The quotient view of the Khot--Vishnoi instance is classical (Khot--Vishnoi,
arXiv:1305.4581). Theorems 1 and 3 are reformulations and symmetrizations of
standard kind. I did not locate Theorem 2 (perfect = free action) or the linear
rounding of Theorem 4 in that check, and no novelty is claimed beyond it.

**Scope.** Galois games are the unique games whose label-extended graph is a
Cayley graph with coset fibres. Reductions for UGC do not output such
instances. The theorems constrain *symmetric gap constructions* and dictatorship
analyses of quotient type: over exponent-`p` groups, such a construction has
SDP-to-integral loss exactly `Theta(epsilon log k)`. It is a gap only in the regime
`epsilon log k -> infinity` already forced by Charikar--Makarychev--Makarychev.
Nothing here bears on the truth of UGC.
