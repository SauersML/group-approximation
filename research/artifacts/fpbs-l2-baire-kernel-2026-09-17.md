# Baire kernel of the l2 gap on uniformly nonamenable marked groups (2026-09-17)

Agent `b-d-bs-reframer`, wave `swarm-0917`, family finite-models (space of
marked groups).

This note reframes `fpbs-nonamenability-bounds-critical-connectivity-operator`,
restricted to Cayley graphs, as a statement about compact spaces of marked
groups. It proves three things.

* A Baire dichotomy on every closed set of uniformly nonamenable marked groups
  (Theorem 2.1).
* A derived kernel `K_{k,eta}` whose emptiness is exactly the l2 gap
  conjecture on those groups, and on which, if nonempty, failures are comeager
  (Theorem 2.2).
* An explicit uniform patch: every marked group of girth at least `L(eta)`
  lies in a fixed `U_{M,delta}`, with explicit `M` and `delta` (Theorem 3.1).
  Hence the kernel lives on finitely many relator cylinders, and the *uniform*
  conjecture splits into finitely many independently falsifiable pieces
  (Section 4).

Nothing here proves the conjecture. Sections 2 and 4 are equivalences and
reductions; Section 3 is a theorem obtained by combining the imported
Benjamini–Nachmias–Peres bound with the Nachmias–Peres path count.

Notation is that of `research/artifacts/fpbs-l2-gap-local-limits-2026-09-17.md`
(the "local-limits note"): `tau_p`, `T_p`, the norm (0.1), `p_{2->2}`,
`U_{M,delta} = {G : ||T^G_{p_c(G)+delta}|| <= M}`, facts (F1)–(F4), Theorem
3.1 and Corollary 3.2.

## 1. The compact spaces `X_{k,eta}`

* `G_k` is the space of `k`-marked groups `(Gamma; s_1,...,s_k)`, with the
  Grigorchuk/Chabauty topology. It is compact and metrizable (a closed subset
  of the Cantor space of subsets of the free group `F_k`, via the kernel of
  `F_k -> Gamma`).
* To a marked group attach the simple Cayley graph `Cay(Gamma,S)`, where
  `S = {s_i^{+-1}} \ {e}`. Its degree is `d = |S|`. Convergence in `G_k`
  is convergence of the kernels on every finite set of words, so the rooted
  `r`-balls of the Cayley graphs eventually agree. This is the local
  convergence of the local-limits note.
* `rho(Gamma,S)` is the spectral radius of simple random walk on the Cayley
  graph, `rho = limsup_n p_n(o,o)^{1/n}`.

**Lemma 1.1.** For `k >= 1` and `eta in (0,1)` put

    X_{k,eta} := { (Gamma,S) in G_k : rho(Gamma,S) <= 1 - eta }.

Then `X_{k,eta}` is compact, every member is an infinite nonamenable group, and
`union_{eta>0} X_{k,eta}` is the set of all nonamenable `k`-marked groups.

*Proof.*

1. `p_{2(n+m)}(o,o) >= p_{2n}(o,o) p_{2m}(o,o)`, so by Fekete
   `rho = sup_n p_{2n}(o,o)^{1/(2n)}`.
2. `p_{2n}(o,o)` depends only on the rooted `n`-ball, hence is locally constant
   on `G_k`. A supremum of continuous functions is lower semicontinuous, so
   `{rho <= 1-eta}` is closed in the compact space `G_k`.
3. A finite graph has `rho = 1`, so members are infinite. Kesten's criterion
   (`rho < 1` iff nonamenable, for Cayley graphs of finitely generated groups)
   gives the last two statements. QED.

**Lemma 1.2.** For `M >= 1`, `delta > 0`, the set `U_{M,delta} cap X_{k,eta}`
is closed in `X_{k,eta}`. Also

    C_2 cap X_{k,eta} = union_{M,j in N} U_{M,1/j} cap X_{k,eta}

is `F_sigma` in `X_{k,eta}`, and `U_{M,delta} subseteq U_{M',delta'}` whenever
`M <= M'` and `delta' <= delta`.

*Proof.* Members of `X_{k,eta}` are infinite, locally finite and transitive,
so Theorem 3.1(c),(d) of the local-limits note apply to sequences in
`X_{k,eta}`. The inclusion is (F1): `||T_{p_c+delta'}|| <= ||T_{p_c+delta}||`.
QED.

**Lemma 1.3 (norm equals spectral radius).** On a vertex-transitive `d`-regular
graph the transition operator satisfies `||P||_{2->2} = rho`.

*Proof.*

1. `p_{2n}(o,o) = <delta_o, P^{2n} delta_o> <= ||P||^{2n}`, so `rho <= ||P||`.
2. For finitely supported `f`, Cauchy–Schwarz in
   `p_{2n}(x,y) = <P^n delta_x, P^n delta_y>` and transitivity give
   `||P^n f||^2 = sum_{x,y} f(x) f(y) p_{2n}(x,y) <= ||f||_1^2 p_{2n}(o,o)`.
   So `limsup_n ||P^n f||^{1/n} <= rho`.
3. `P` is self-adjoint. With `mu_f` its spectral measure at `f`,
   `||P^n f||^2 = int lambda^{2n} d mu_f`, so
   `lim ||P^n f||^{1/n} = max{|lambda| : lambda in supp mu_f}`. Hence
   `supp mu_f subseteq [-rho, rho]` for every finitely supported `f`.
4. These `f` are dense, so the spectral projection of `P` outside `[-rho,rho]`
   vanishes, and `||P|| <= rho`. QED.

## 2. Baire dichotomy and the kernel

**Theorem 2.1 (Baire dichotomy).** Let `k >= 1`, `eta in (0,1)`, and let
`Y subseteq X_{k,eta}` be nonempty and closed. Exactly one of the following
holds.

* (a) **Uniform patch.** There are `M >= 1`, `delta > 0` and a nonempty
  relatively open `V subseteq Y` with `V subseteq U_{M,delta}`.
* (b) **Generic failure.** `Y \ C_2` is a dense `G_delta` subset of `Y`. So
  the generic member of `Y`, in the Baire sense, has `p_c = p_{2->2}`.

*Proof.*

1. `Y` is a compact metrizable space, hence a Baire space.
2. By Lemma 1.2, `Y cap C_2 = union_{M,j} (Y cap U_{M,1/j})` is a countable
   union of relatively closed sets.
3. If (a) fails, then no `Y cap U_{M,delta}` has nonempty relative interior.
   Each is closed, so each is nowhere dense in `Y`. Then `Y cap C_2` is meager
   and `F_sigma`, so its complement `Y \ C_2` is `G_delta`. By the Baire
   category theorem it is dense. So (b) holds.
4. If (a) holds, then `V subseteq C_2` by Theorem 3.1(d) of the local-limits
   note, so `Y \ C_2` misses the nonempty open set `V` and is not dense. So (b)
   fails. QED.

**Derivative.** For closed `Y subseteq X_{k,eta}` let

    D(Y) := Y \ union { V : V relatively open in Y, V subseteq U_{M,delta} for some M >= 1, delta > 0 }.

`D(Y)` is closed. Put `Y_0 = X_{k,eta}`, `Y_{alpha+1} = D(Y_alpha)` and
`Y_lambda = intersection_{alpha<lambda} Y_alpha` at limit ordinals.

**Theorem 2.2 (the kernel).** Let `k >= 1` and `eta in (0,1)`.

* (i) There is a countable ordinal `alpha_0` with `Y_{alpha_0+1} = Y_{alpha_0}`.
  Put `K_{k,eta} := Y_{alpha_0}`. It is closed and `D(K_{k,eta}) = K_{k,eta}`.
* (ii) `X_{k,eta} \ K_{k,eta} subseteq C_2`. Equivalently,
  `X_{k,eta} \ C_2 subseteq K_{k,eta}`.
* (iii) `C_2 contains X_{k,eta}` if and only if `K_{k,eta}` is empty.
* (iv) If `K_{k,eta}` is nonempty, then `K_{k,eta} \ C_2` is a dense `G_delta`
  subset of `K_{k,eta}`.
* (v) Every `(Gamma,S) in X_{k,eta} \ K_{k,eta}` has `p_c < p_{2->2} <= p_u`.
* (vi) **Uniform version.** There are `M, delta` with
  `X_{k,eta} subseteq U_{M,delta}` if and only if `D(X_{k,eta})` is empty,
  that is, if and only if every point of `X_{k,eta}` has a neighbourhood
  contained in some `U_{M,delta}`.

*Proof.*

(i) `X_{k,eta}` is second countable. Fix a countable base `B`. Each strict
decrease `Y_{alpha+1} subsetneq Y_alpha` of closed sets is witnessed by a basic
set meeting `Y_alpha` but not `Y_{alpha+1}`, and a basic set that misses some
`Y_beta` misses all later ones. So strict decreases inject into `B`, and the
sequence stabilizes at a countable ordinal.

(ii) A point `x` removed at stage `alpha` lies in a relatively open
`V subseteq Y_alpha` with `V subseteq U_{M,delta}`, so `x in C_2` by Theorem
3.1(d) of the local-limits note.

(iii) If `K` is empty, then (ii) gives `X_{k,eta} subseteq C_2`. If `K` is
nonempty, apply (iv), which exhibits a point of `K` outside `C_2`.

(iv) `K` is nonempty and closed, and `D(K) = K` says that alternative (a) of
Theorem 2.1 fails for `Y = K`. So alternative (b) holds.

(v) (ii) together with `p_{2->2} <= p_u`, which is (F3) with (F1).

(vi) If `X_{k,eta} subseteq U_{M,delta}`, then `D(X_{k,eta})` is empty, taking
`V = X_{k,eta}`. Conversely, if `D(X_{k,eta})` is empty, the open sets
`V subseteq U_{M,delta}` cover the compact space `X_{k,eta}`. Take a finite
subcover `V_1,...,V_m` with constants `(M_i,delta_i)`, and put
`M = max M_i`, `delta = min delta_i`. By Lemma 1.2, every `V_i` lies in
`U_{M,delta}`. QED.

**Consequences for the target conjecture.**

* By (F1), `C_2` implies `||T_{p_c}|| < infinity`. So `K_{k,eta}` empty for
  all `k` and `eta` gives the l2 conjecture on every nonamenable Cayley graph,
  and hence `fpbs-benjamini-schramm-universal` through Corollary 3.2 (or
  `fpbs-critical-l2-implies-nonuniqueness`).
* Conversely, one point of `K_{k,eta}` forces a comeager set of failures of the
  gap class inside `K_{k,eta}`. A counterexample to the l2 gap on Cayley graphs
  is therefore never isolated: it comes with a perfect-type family.
* The ordinal `alpha_0` measures how non-uniform the constants are. The
  uniform conjecture (vi) is the case `alpha_0 = 0` with empty kernel. It is
  strictly stronger than (iii) as a statement, and it is the form Corollary
  3.2 can transplant to limits.
* This is a restatement, not progress on the l2 bound itself. Its use is
  structural: any local certificate of a *fixed* `(M,delta)` on an open set of
  marked groups shrinks `K`, and Section 3 supplies one on an explicit clopen
  set.

## 3. The high-girth uniform patch

Imported statements, quoted verbatim.

**(BNP)** Benjamini, Nachmias and Peres, *Is the critical percolation
probability local?*, arXiv:0901.4616, e-print source fetched 2026-09-17,
`localpc.tex`:

> \begin{theorem} \label{localpc} There exists an absolute constant $C>0$ such
> that if $G$ is a non-amenable regular graph with degree $d$ and girth $g$ such
> that the bottom of spectrum of $I-P$ is $\lambda_1>0$, then
> $$ p_c(G) \leq {1 \over d-1} + {C \log\big( 1 + {1 \over \lambda_1^2} \big) \over dg} \, .$$

The same theorem as quoted by Nachmias and Peres (below):

> There exists a universal constant $C>0$ such that if $G$ is a non-amenable
> regular graph with degree $d$, girth $g$ and spectral radius $\rho < 1$, then
> $$ p_c(G) \leq {1 \over d-1} + {C \log (1+ (1-\rho)^{-2}) \over dg} \, .$$

**(NP)** Nachmias and Peres, *Non-amenable Cayley graphs of high girth have
$p_c<p_u$ and mean-field exponents*, arXiv:1207.1480, e-print source fetched
2026-09-17.

> \begin{lemma} \label{nbwvssrw} For any graph $G$, vertices $x,y$ and
> $n \geq 0$ we have
> $$ \pnbw^n(x,y) \leq \sum_{j \geq n} \psrw^j(x,y) \, .$$

> since $d(d-1)^{n-1} \pnbw^n(x,y)$ is an upper bound on the number of simple
> paths of length precisely $n$ between $x$ and $y$.

Nachmias–Peres, Theorem 1 (`percthm`), states only `p_c < p_u` for transitive
graphs with spectral radius at most `rho` and girth at least `L`. The point of
Theorem 3.1 below is that the same inputs give a *uniform* l2 gap with explicit
constants, which is what Theorems 2.1–2.2 and Corollary 3.2 consume.

**Proposition 3.0 (walk-counting l2 bound, no girth hypothesis).** Let `G` be a
vertex-transitive `d`-regular graph with `d >= 3` and spectral radius
`rho < 1`. If `0 <= q` and `r := q(d-1)rho < 1`, then

    ||T_q|| <= 1 + (d/(d-1)) * r / ((1-r)(1-rho)).

In particular `p_{2->2}(G) >= 1/((d-1) rho)`.

*Proof.*

1. For `x != y`, the event `x <-> y` is contained in the union over simple paths
   from `x` to `y` of the event that the path is open. A simple path of length
   `n` is open with probability `q^n`. By (NP, path count),
   `tau_q(x,y) <= sum_{n>=1} q^n d(d-1)^{n-1} p_nbw^n(x,y)`. Also
   `tau_q(x,x) = 1`.
2. By (NP, Lemma `nbwvssrw`), entrywise

       tau_q <= I + sum_{n>=1} q^n d (d-1)^{n-1} sum_{j>=n} P^j =: B.

3. All matrices are entrywise nonnegative. By (0.1), `||T_q|| <= ||B||`,
   since `<f,T_q g> <= <f,B g>` for `f,g >= 0`.
4. By Lemma 1.3, `||P^j|| <= rho^j`, so `||sum_{j>=n} P^j|| <= rho^n/(1-rho)`.
5. Hence
   `||B|| <= 1 + (d/(d-1)) sum_{n>=1} r^n / (1-rho) = 1 + (d/(d-1)) r/((1-r)(1-rho))`.
6. For `q < 1/((d-1)rho)` this is finite, so `p_{2->2} >= q`. QED.

**Theorem 3.1 (high-girth uniform patch).** Let `C` be the absolute constant of
(BNP). For `eta in (0,1)` put

    L(eta) := max( 3, ceil( 4 C log(1 + eta^{-2}) / eta ) ),
    M(eta) := 1 + 3/eta^2,
    delta(k,eta) := eta / (4(2k-1)).

Let `k >= 2` and let

    P_{k,eta} := { (Gamma,S) in X_{k,eta} : no nontrivial freely reduced word of length < L(eta) in s_1,...,s_k is trivial in Gamma }.

Then `P_{k,eta}` is relatively clopen in `X_{k,eta}`, and

    P_{k,eta} subseteq U_{M(eta), delta(k,eta)}.

So every member has `p_c + eta/(4(2k-1)) <= p_{2->2} <= p_u`, with
`||T_{p_c + eta/(4(2k-1))}|| <= 1 + 3/eta^2`.

*Proof.*

1. **Clopen.** The condition concerns finitely many words, and "`w = e` in
   `Gamma`" is clopen in `G_k` for each word `w`.
2. **Degree and girth.** Since `L(eta) >= 3`, the words `s_i`, `s_i^2` and
   `s_i s_j^{+-1}` (`i != j`) are nontrivial. So the `2k` elements `s_i^{+-1}`
   are distinct and nontrivial, and the Cayley graph is `d`-regular with
   `d = 2k >= 4`. A cycle of length `g` in a Cayley graph gives a nontrivial
   freely reduced word of length at most `g` that is trivial (read the labels
   of a shortest cycle; it is reduced because the cycle does not backtrack). So
   the girth is at least `L(eta)`.
3. **Choice of `q`.** Let `rho = rho(Gamma,S) <= 1-eta` and
   `q := (1 + 1/rho) / (2(d-1))`. Then `r = q(d-1)rho = (1+rho)/2 < 1` and
   `1 - r = (1-rho)/2 >= eta/2`. Proposition 3.0 and `d/(d-1) <= 3/2` give

       ||T_q|| <= 1 + (3/2) * 1 / ((eta/2) * eta) = 1 + 3/eta^2 = M(eta).

   (Also `q < 1`: `rho >= 2 sqrt(d-1)/d`, the spectral radius of the `d`-regular
   tree, so `1/rho <= d/(2 sqrt(d-1)) < d - 2` for `d >= 4`, and then
   `q < (d-1)/(2(d-1)) < 1`.)
4. **Margin above `1/(d-1)`.** Since `1/rho >= 1/(1-eta) >= 1+eta`,
   `q - 1/(d-1) = (1/rho - 1)/(2(d-1)) >= eta/(2(d-1))`.
5. **BNP.** The graph is nonamenable and regular, `lambda_1 = 1 - rho`
   (Lemma 1.3, and `sup spec P = ||P||` for a positivity-preserving
   self-adjoint `P`, since `|<f,Pf>| <= <|f|,P|f|>`). So `lambda_1 >= eta` and
   `log(1 + lambda_1^{-2}) <= log(1 + eta^{-2})`. With `g >= L(eta)`,

       p_c <= 1/(d-1) + C log(1+eta^{-2}) / (d L(eta)) <= 1/(d-1) + eta/(4d) <= 1/(d-1) + eta/(4(d-1)).

6. **Conclusion.** By 4 and 5, `p_c + eta/(4(d-1)) <= 1/(d-1) + eta/(2(d-1)) <= q`.
   By (F1) and 3, `||T_{p_c+delta}|| <= ||T_q|| <= M(eta)` with
   `delta = eta/(4(d-1)) = eta/(4(2k-1))`. QED.

**Remarks.**

* `C` is not explicit in (BNP), so `L(eta)` is effective only up to that
  constant. The theorem needs only its existence.
* `k = 1` is vacuous: `X_{1,eta}` is empty (cyclic groups are amenable).
* The patch is clopen, so it adds no new limit points. Its value is that it
  removes `P_{k,eta}` from the kernel at the first stage.

**Corollary 3.2 (the kernel lives on short relators).**

    K_{k,eta} subseteq D(X_{k,eta}) subseteq X_{k,eta} \ P_{k,eta} = union_{1 <= |w| < L(eta)} Z_{k,eta,w},

where `w` ranges over nontrivial freely reduced words in `F_k` and
`Z_{k,eta,w} := {(Gamma,S) in X_{k,eta} : w = e in Gamma}`, which is relatively
clopen.

*Proof.* `P_{k,eta}` is open and contained in `U_{M(eta),delta(k,eta)}`, so it is
removed by `D`. QED.

## 4. The uniform conjecture splits into finitely many cylinders

**Uniform l2 gap conjecture** (`fpbs-uniform-l2-gap-marked-groups`, OPEN).
For every `k >= 2` and `eta in (0,1)` there are `M < infinity` and `delta > 0`
with `X_{k,eta} subseteq U_{M,delta}`.

**Cylinder pieces** (`fpbs-uniform-l2-gap-short-relator-cylinders`, OPEN).
For every `k >= 2`, `eta in (0,1)` and every nontrivial freely reduced word `w`
in `F_k`, there are `M_w < infinity` and `delta_w > 0` with
`Z_{k,eta,w} subseteq U_{M_w,delta_w}`.

**Proposition 4.1.** The cylinder pieces together with Theorem 3.1 imply the
uniform conjecture. More precisely, for fixed `(k,eta)`,

    X_{k,eta} subseteq U_{M,delta} for some (M,delta)
    iff  for each of the finitely many w with 1 <= |w| < L(eta), Z_{k,eta,w} subseteq U_{M_w,delta_w} for some (M_w,delta_w).

*Proof.* "Only if" is restriction. For "if", `X_{k,eta} = P_{k,eta} union
union_{|w|<L(eta)} Z_{k,eta,w}`, a finite union. Take `M` the maximum of
`M(eta)` and the `M_w`, and `delta` the minimum of `delta(k,eta)` and the
`delta_w`, and use Lemma 1.2. QED.

**Proposition 4.2.** The uniform conjecture implies
`fpbs-benjamini-schramm-universal`.

*Proof.* Let `Gamma` be nonamenable with finite symmetric generating set `S`,
`e not in S`. List `S` as `s_1,...,s_k` (`k = |S| >= 2`, since otherwise
`Gamma` is cyclic). The simple Cayley graph of the marked group is
`Cay(Gamma,S)`. By Kesten `rho < 1`, so the marked group is in `X_{k,eta}` for
some `eta`, hence in some `U_{M,delta}`. Corollary 3.2 of the local-limits note,
with the constant sequence, gives `p_c < p_c + delta <= p_{2->2} <= p_u`. QED.

**Why the split is useful.**

* Each cylinder is a clopen family defined by one relation, and can be attacked
  or refuted on its own. Examples of the relations involved:
  - `w = s_1^2`: one generator is an involution (free products with `Z/2`
    factors, Coxeter-type markings);
  - `w = [s_1,s_2]`: two generators commute (products `Gamma x Z` with a mixed
    marking, where the amenable direction of Theorem 6 of `exploration.md`
    lives);
  - `w = s_1^n`, `n < L(eta)`: a torsion generator (Burnside-type markings).
* A counterexample to one cylinder refutes the uniform conjecture for that
  `(k,eta)`. By Theorem 2.2(iv) it gives a comeager failure set only inside the
  kernel; it does not by itself refute the pointwise conjecture.
* The known classes of `fpbs-free-product-cayley-graphs-have-critical-l2-gap`
  and `fpbs-acylindrically-hyperbolic-critical-l2-gap` are pointwise
  (qualitative) and do not certify a cylinder.
* Theorem 3.1 is an explicit certificate of a fixed `(M,delta)` on a clopen
  subset of `X_{k,eta}`. For `eta <= 1 - sqrt(2k-1)/k` it contains the free
  marking of `F_k`, and it contains every marked group whose Cayley graph has
  girth at least `L(eta)` and spectral radius at most `1-eta`.

## 5. Where this stops

* Theorems 2.1–2.2 are equivalences: they do not decide whether `K_{k,eta}` is
  empty.
* Theorem 3.1 is a transplant of Nachmias–Peres. Girth is the whole mechanism;
  a single relation of length below `L(eta)` in the marking takes a group out
  of the patch. So the patch does not reach `Gamma x Z`, surface groups with
  standard markings, or any one-ended group with a short relation.
* The uniform conjecture may be false while the pointwise conjecture is true.
  Theorem 2.2(vi) separates them: the pointwise conjecture needs only
  `K_{k,eta}` empty, which allows transfinite derived stages with degenerating
  constants.
