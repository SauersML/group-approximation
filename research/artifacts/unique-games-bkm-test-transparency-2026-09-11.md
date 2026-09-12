# The Rich 2-to-1 noise test is no sounder than a derived unique game

Date: 2026-09-11. Status: complete mathematical proof of Theorem 1 and its
corollaries. **This is neither a proof nor a disproof of the Unique Games
Conjecture or of the Rich 2-to-1 Games Conjecture.** No proof-assistant
verification and no priority claim is made; see Section 7 for the limited
literature check.

## 1. Setting

Throughout, `Psi = (L cup R, E, [2n], [n], {pi_e})` is a 2-to-1 game on a
regular bipartite graph, as in Definition 1 of Braverman--Khot--Minzer,
*On Rich 2-to-1 Games*, ITCS 2021 (BKM below). For an edge `e=(u,v)` let
`P_e` be the perfect matching of `[2n]` into the fibers of `pi_e`. At a left
vertex `u` let

```text
F_u = { P_e : e is incident on u }                                   (1)
```

be the set of **distinct** matchings that occur at `u`. For matchings
`P != P'` write `d(P,P')` for the number of pairs of `P` that are not pairs
of `P'`, and put

```text
delta(u) = min { d(P,P')/n : P != P' in F_u }     (delta(u)=1 if |F_u|=1).
```

**The test.** `R_(rho,m)(Psi)` is the reduction of BKM Section 5, with
correlation `rho = 1 - epsilon`. The noise kernel on `Z_m` is
`K_rho(s,t) = rho 1_(s=t) + (1-rho)/m`, applied independently to coordinates.

1. Sample `v in R` uniformly, `a in Z_m^n` uniformly, and `b = K_rho(a)`.
2. Sample neighbours `u,w` of `v` independently and uniformly.
3. Put `A = pi_(u,v)^(-1)(a)` and `B = pi_(w,v)^(-1)(b)` in `Z_m^(2n)`, that is
   `A_i = a_(pi_(u,v)(i))` and `B_i = b_(pi_(w,v)(i))`.
4. Sample `x = K_rho(A)` and `y = K_rho(B)` independently. Accept iff
   `F_u(x) = F_w(y)`.

The assignment is a family of folded functions
`F_u : Z_m^(2n) -> Z_m`, `F_u(z + s 1) = F_u(z) + s`. The value of the output
unique game is the maximum acceptance probability over folded assignments.

**The derived unique game.** `UG_der(Psi)` has left vertices `(u,P)` with
`P in F_u`, right vertices `R`, and both alphabets of size `n`: a label of
`(u,P)` is one pair of `P`, and a label of `v` is an element of `[n]`. Each
edge `e=(u,v)` of `Psi` gives the edge `((u,P_e),v)`, with the same weight,
accepting `(p,j)` iff `pi_e(p) = j`. The pairs of `P_e` are exactly the fibers
of `pi_e`, so `pi_e` induces a bijection from the pairs of `P_e` onto `[n]`.
Hence `UG_der(Psi)` **is a unique game**. It is computable in time polynomial
in `|E|` and `n`.

Two lower bounds on its value are immediate.

```text
val(UG_der(Psi)) >= val(Psi).                                        (2)
val(UG_der(Psi)) >= kappa(Psi) = E_(e=(u,v)) [ 1 / s(u,P_e) ],       (3)
s(u,P) = number of edges at u whose matching is P.
```

For (2), label `(u,P)` by the pair of `P` containing the label of `u`. For
(3), fix any right labeling `beta`. For each class `(u,P)` pick one edge
`e* = (u,v*)` of the class and label `(u,P)` by the fiber
`pi_(e*)^(-1)(beta(v*))`. At least one edge per class is satisfied, so at `u`
the satisfied fraction is at least `|F_u|/deg(u)`, which is the average of
`1/s(u,P_e)` over the edges at `u`. Averaging over `u` gives (3), since the
graph is regular.

## 2. Results

**Theorem 1.** For every 2-to-1 game `Psi`, every `m >= 2` and every
`0 < rho < 1`,

```text
val(R_(rho,m)(Psi)) >= 1/m + (1-1/m) rho^3 val(UG_der(Psi))^2 - 2 e(Psi),   (4)
e(Psi) = max_u |F_u| exp(-rho^4 delta(u)^2 n / 32),
```

where a vertex with `|F_u| = 1` contributes `0` to the maximum.

**Corollary 2 (distinct matchings are killed outright).** If at every left
vertex the edges carry pairwise distinct matchings, then `kappa(Psi) = 1`,
so by (3) and (4)

```text
val(R_(rho,m)(Psi)) >= 1/m + (1-1/m) rho^3 - 2 e(Psi)
```

**whatever `val(Psi)` is.** For translation families on `GF(2)^k`
(`F_lin`), distinct directions share no pair, so `delta(u) = 1`,
`|F_u| <= 2n-1` and `e(Psi) <= (2n-1) exp(-rho^4 n/32)`.

**Corollary 3 (transparency).** Suppose a polynomial-time reduction maps an
NP-hard problem to 2-to-1 games `Psi` such that:

- YES instances have `val(Psi) >= 1-eta`;
- NO instances have `val(R_(rho,m)(Psi)) <= epsilon`;
- `e(Psi) <= xi` on every output instance.

Then the map `Psi -> UG_der(Psi)` is a polynomial-time reduction proving
that `Gap-Unique_n[1-eta, s]` is NP-hard, with

```text
s = sqrt( (epsilon + 2 xi) / ((1-1/m) rho^3) ).
```

So on learnable instances the long-code layer supplies no soundness: a
hardness proof that passes through `R` on such instances already contains a
proof of NP-hardness of `Gap-Unique[1-eta, O(sqrt(epsilon))]` for the unique
games `UG_der(Psi)`, with constant alphabet `n` and no long code.

*Proof.* Completeness is (2). For soundness, (4) gives
`(1-1/m) rho^3 val(UG_der)^2 <= epsilon - 1/m + 2 xi <= epsilon + 2 xi`.

**Corollary 4 (necessary condition on outer instances).** If
`kappa(Psi) >= kappa_0 > 0`, then

```text
val(R_(rho,m)(Psi)) >= 1/m + (1-1/m) rho^3 kappa_0^2 - 2 e(Psi).
```

BKM's soundness implication `val(Psi) <= eta => val(R(Psi)) <= epsilon`, for
small `epsilon` and learnable families, can therefore hold only on instances
where `val(UG_der)` tends to zero. In particular, at a typical left vertex
the matching classes must have unbounded multiplicity.

## 3. The decoder

**Lemma 5.** Fix `u`, a matching `P_0 in F_u` and a 2-to-1 map `pi` whose
fibers are `P_0`. Let `a` be uniform in `Z_m^n` and `x = K_rho(pi^(-1)(a))`.
This is the marginal law of the query `x` in step 4 when the sampled edge
`(u,v)` has matching `P_0`, because `b = K_rho(a)` is also uniform. For
`P in F_u` put

```text
S_P(x) = (1/n) sum_({i,i'} in P) 1(x_i = x_i'),
```

and let `D_u(x)` be the first maximizer of `S_P` over `F_u` in a fixed
order. Then

```text
Pr[D_u(x) != P_0] <= |F_u| exp(-rho^4 delta(u)^2 n / 32),   D_u(x + s 1) = D_u(x).
```

*Proof.* Call the `n` pairs of `P_0` blocks. The pairs of values
`(x_i, x_i')` on different blocks are independent, because `a` has
independent coordinates and the noise is independent. Within a block both
coordinates are independent `K_rho` copies of one uniform symbol. Since
`K_rho K_rho = K_(rho^2)`, they agree with probability `1/m + lambda`, where
`lambda = (1-1/m) rho^2 >= rho^2/2`. Coordinates in different blocks are
independent and uniform, so they agree with probability `1/m`.

For `P != P_0`, at most `(1-delta(u)) n` pairs of `P` are pairs of `P_0`.
Hence `E S_P <= 1/m + lambda (1-delta(u))`, while `E S_(P_0) = 1/m + lambda`.

- `S_(P_0)` is an average of `n` independent indicators, so by Hoeffding,
  `Pr[S_(P_0) <= 1/m + lambda - t] <= exp(-2 n t^2)`.
- `S_P` is a function of the `n` independent blocks. Changing one block
  changes at most two of its indicators, hence changes `S_P` by at most
  `2/n`. McDiarmid's inequality gives `Pr[S_P >= E S_P + t] <= exp(-n t^2/2)`.

Take the threshold `theta = 1/m + lambda (1 - delta(u)/2)` and
`t = lambda delta(u)/2`. Then `Pr[S_(P_0) <= theta] <= exp(-n lambda^2 delta^2/2)`
and `Pr[S_P >= theta] <= exp(-n lambda^2 delta^2/8)` for every `P != P_0`.
Outside these events `S_(P_0) > theta > S_P` for all `P != P_0`, so `P_0` is
the unique maximizer. A union bound over the `|F_u|` events gives the bound,
using `lambda^2 >= rho^4/4`.

Adding `s` to every coordinate changes no equality, which proves shift
invariance.

## 4. The folded labeling

Fix an optimal labeling of `UG_der(Psi)`: a pair `p(u,P)` of `P` for each
left vertex `(u,P)`, and `beta : R -> [n]`. Choose one member `q(u,P)` of
each pair `p(u,P)` and define

```text
F_u(z) = z_( q(u, D_u(z)) ).                                         (5)
```

By Lemma 5 the decoder is shift invariant, so `F_u(z + s 1) = F_u(z) + s`.
Thus (5) is a valid folded assignment, including on inputs where decoding
fails.

## 5. Proof of Theorem 1

Condition on `v,u,w`. Put `q = q(u, P_(u,v))`, `q' = q(w, P_(w,v))`,
`j = pi_(u,v)(q)` and `j' = pi_(w,v)(q')`. Consider the ideal outputs
`I = x_q` and `J = y_(q')`. Here `I` is a `K_rho` copy of `A_q = a_j`, and `J`
is a `K_rho` copy of `B_(q') = b_(j')`.

- If `j = j'`, then `J` given `I` has law `K_(rho^3)`, a composition of three
  symmetric kernels over a uniform symbol. Hence
  `Pr[I=J] = 1/m + (1-1/m) rho^3`.
- If `j != j'`, then `b_(j')` depends only on `a_(j')` and independent noise,
  and `a_j`, `a_(j')` are independent and uniform. So `I` and `J` are
  independent and uniform, and `Pr[I=J] = 1/m`.

Call an edge `e = (u,v)` *good* if `pi_e(p(u,P_e)) = beta(v)`, that is, if it
is satisfied in `UG_der(Psi)`. If both `(u,v)` and `(w,v)` are good, then
`j = beta(v) = j'`. Consequently

```text
Pr[I = J | v,u,w] >= 1/m + (1-1/m) rho^3 1(both edges good).
```

The query `x` has exactly the law of Lemma 5 for the matching `P_(u,v)`, so
`F_u(x) != I` with probability at most `e(Psi)`. The same holds for `y`,
since `b` is uniform. A union bound gives

```text
Pr[F_u(x) = F_w(y)] >= Pr[I = J] - 2 e(Psi).
```

This comparison needs no independence between the decoding events and the
selected symbols. Since `u` and `w` are independent given `v`,

```text
Pr_(u,w)[both good | v] = s_v^2,     s_v = Pr_(u in N(v)) [(u,v) good].
```

Because the graph is regular, sampling `v` uniformly and then a uniform
neighbour yields the uniform edge distribution. So `E_v s_v` is the value of
the chosen labeling of `UG_der(Psi)`, and Cauchy--Schwarz gives
`E_v[s_v^2] >= (E_v s_v)^2 = val(UG_der(Psi))^2`. Averaging proves (4). QED

## 6. Scope

- **The earlier affine obstruction is a special case.** In the source game
  `G_N` of `affine-long-code-test-has-no-uniform-soundness`, each left vertex
  sees each nonzero direction exactly once. Corollary 2 therefore applies,
  and its shifted coordinate `u b^2` is one particular pair choice. What
  Theorem 1 adds is that the low source value in that construction was never
  needed: the collapse happens on every instance with pairwise distinct
  learnable matchings.
- **What remains open about the published hard instances.** For
  translation-rich instances, which include the 2-to-1 instances produced by
  the Grassmann reductions, whether BKM's test is sound is exactly the
  question whether their derived unique games have small value in the NO
  case. This artifact does not compute `kappa` or `val(UG_der)` for the
  published reductions.
- **Unlearnable families are untouched.** When `|F_u| >= exp(c rho^4 delta^2 n)`
  the bound (4) says nothing. Full richness has `|F_u| = (2n-1)!!`, and
  distinct random matchings share few pairs, so Theorem 1 does not bear on
  BKM's theorem.
- **The design constraint on outer PCPs.** A route to UGC through `R` must do
  one of two things. Either it supplies 2-to-1 hardness whose left-vertex
  matchings cannot be decoded from one noisy pullback table, which needs
  entropy linear in `n`; or it proves NO-case hardness of `UG_der`, which is
  already a unique game.

## 7. Provenance

The selector-and-decoder idea goes back to Cairn's 2026-09-07 noisy direction
counterexample and its cyclic-alphabet decoder. The general statement, the
derived unique game and the transparency corollary were written by the fork
`ugc-2` on 2026-09-11. The description of the test was checked against the
text of BKM Section 5 (pp. 27:16--27:19), extracted from the proceedings PDF
at <https://drops.dagstuhl.de/storage/00lipics/lipics-vol185-itcs2021/LIPIcs.ITCS.2021.27/LIPIcs.ITCS.2021.27.pdf>.
BKM's Section 1.3 ("Making Games Richer?") floats a ladder
`F_lin = F_0 ⊆ ... ⊆ F_T = F_all` of successively richer families. Theorem 1
shows that no rung of polynomial size can feed the test directly.
Repository searches covered the unique-games region; no exhaustive
literature review was made.
