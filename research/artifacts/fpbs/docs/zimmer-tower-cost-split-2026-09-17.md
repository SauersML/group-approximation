# Furstenberg--Zimmer tower split of cost descent

September 17, 2026, worker b-t-block, from the hole
`fpbs-relative-cycle-block-localization`. These are written deductions.
Fixed price is not resolved, and no priority is claimed. The one
imported theorem is quoted verbatim in Section 2.

**Coordination note.** Worker b-t-reuse reached the same tower split in
parallel. It records the split as
`fpbs-compact-weakly-mixing-tower-decomposes-cost-preservation`, with the
dichotomy import `relative-furstenberg-zimmer-dichotomy` and the two open premises
`fpbs-compact-extensions-preserve-cost` (P_c here, N2) and
`fpbs-relatively-weakly-mixing-extensions-preserve-cost` (P_w here, N3).
Those are the graph nodes. This note does not duplicate them.

Step N1 is already Section 10 of `fixed-price-conditional-traffic.md`
(`fpbs-traffic-variational-cost-identities`). Section 1 below is an
independent finitely generated write-up of the same fact.

The one new graph node from this note is Theorem 4.1,
`fpbs-profinite-skew-products-reduce-to-finite-fibers`.

**Referee corrections (2026-09-17).** That node is OPEN: two of three
referee lenses refuted it, and its proof route is kept as an attempt
artifact. The referees agreed with (a), (b) and the conditional first
sentence of (c). Three statements in this note are wrong.
* **Per-Gamma equivalence.** "Finite-fibre preservation is equivalent to
  finite-index multiplicativity" holds only over a class of groups, not
  for one fixed Gamma. The direction (I)=>(F) in
  `fpbs-finite-fiber-cost-bound` passes through Gamma x Sym(q).
* **Consequence paragraph.** The imported isometric-extension theorem says
  that ergodic relatively compact extensions are homogeneous skew
  products, not the reverse. The residue is K/L not totally disconnected,
  not K^0 nontrivial, since the L K_n intersect to L K^0.
* **Section 5.** Its closing claim is false; see the correction there.

## 0. Summary

Let Gamma be an infinite finitely generated group. The parent
`fpbs-free-action-cost-at-least-bernoulli-cost` asks for C(a) >= C(b),
where a is any free p.m.p. action and b is Bernoulli. Since
C(a x b) = C(a) (`fpbs-bernoulli-noise-does-not-change-cost`), the parent
is cost descent along the projection a x b -> b. The open premise
`fpbs-relative-cycle-block-localization` is one more way of stating that
descent.

The split has three steps and one import:

* **[N1] Increasing unions (proved).** C(Y) >= inf_n C(Z_n) along an
  increasing generating chain of factors.
* **[N2] Relatively compact extensions of free actions preserve cost
  (OPEN).**
* **[N3] Relatively weakly mixing extensions of free actions preserve cost
  (OPEN).**
* **[FZ] Jamneshan's relative dichotomy (imported).** It holds for any
  group, with no ergodicity hypothesis.

Section 3 derives the parent over the base b. For finitely generated
Gamma the split is an equivalence, parent <=> N2 and N3.

Section 4 contains the new material:
* **N2 inside the rank-gradient question.** N2 contains discrete-spectrum
  actions, and so implies rank gradient = C(b) - 1.
* **Theorem 4.1.** Profinite-fibre skew products reduce to uniform finite
  fibres. So beyond finite-index multiplicativity, the content of N2 lies
  in fibre groups with nontrivial identity component.
* **N3 obstruction.** N3 contains every free weakly mixing action, and
  cannot follow from weak-containment monotonicity.

## 1. [N1] Cost along increasing factors

**Setting.** Gamma is finitely generated, with finite generating set S.
Y = (Y, nu) is a free p.m.p. Gamma-action. Z_0 <= Z_1 <= ... is an
increasing sequence of Gamma-invariant complete sub-sigma-algebras of Y
whose union generates Y mod null sets. Each Z_n is realized pointwise
as a standard factor pi_n : Y -> Z_n.

**Theorem 1.1.** C(Y) >= inf_n C(Z_n). If every Z_n is free, then
C(Z_n) is nonincreasing and converges to C(Y).

*Proof.* If C(Y) is infinite there is nothing to prove, so assume it is
finite. Fix eps > 0 and a graphing Phi of the orbit relation R_Y with
c(Phi) <= C(Y) + eps.

**Step 1: group pieces.** Enumerate Gamma. Every partial Borel
isomorphism with graph inside R_Y splits into countably many
restrictions s|A, s in Gamma, with disjoint domains: send each point of
the domain to the first s in the enumeration that agrees with the map
there. Splitting does not change cost. So write
Phi = (s_i|A_i)_{i in N}, with sum_i nu(A_i) = c(Phi).

**Step 2: truncate.** Take N and r in N and g in S. A word is a
sequence (i_1, e_1), ..., (i_l, e_l) with l <= r, i_j <= N and
e_j = +-1. Its product is s_{i_l}^{e_l} ... s_{i_1}^{e_1}. The word is
*admissible at y* if every step is an edge of Phi. Put
y_0 = y and y_j = s_{i_j}^{e_j} y_{j-1}. A step with e_j = +1 needs
y_{j-1} in A_{i_j}. A step with e_j = -1 needs y_j in A_{i_j}.
Let E_g(N,r) be the set of y at which some word with product g is
admissible. This set is a finite union, over words, of finite
intersections of translates h A_i with i <= N.

Phi generates R_Y and Y is free. So for a.e. y there is a finite
Phi-path from y to g y, and its label product h satisfies h y = g y,
hence h = g. The sets E_g(N,r) increase in N and r with conull union.
Fix N and r with nu(Y \ E_g(N,r)) < eps/|S| for every g in S. Let W be
the number of words, at most (2N+1)^r.

**Step 3: approximate.** The union of the Z_n is an algebra of sets
generating Y, so it is dense in the measure algebra of Y. Choose
delta > 0 with N delta + |S| W r delta < eps. Choose one n and sets
B_i in Z_n (i <= N) with nu(A_i sym B_i) < delta. Define E'_g by the
same Boolean formula with each A_i replaced by B_i. Every intersection
in the formula has at most r terms, and translation preserves nu. So
nu(E_g sym E'_g) <= W r delta. Because Z_n is Gamma-invariant, E'_g is
Z_n-measurable.

**Step 4: repair and descend.** On Z_n, let Theta consist of the pieces
s_i|B_i for i <= N, together with g|(Z_n \ E'_g) for g in S. Here the
B_i and E'_g are read as subsets of Z_n.

Theta generates R_{Z_n}. Take z in Z_n and g in S. If z is in E'_g,
then some word with product g is admissible at z for the pieces B_i,
and it gives a Theta-path from z to g z. This uses only the group
product, not freeness of Z_n. Otherwise the repair piece g|(Z_n \ E'_g)
is an edge from z to g z. So Theta connects every z to s z for all
s in S, and hence to its whole orbit.

Its cost is
c(Theta) <= sum_{i<=N} nu(B_i) + sum_{g in S} nu(Y \ E'_g)
<= c(Phi) + N delta + eps + |S| W r delta <= C(Y) + 3 eps.
So C(Z_n) <= C(Y) + 3 eps, which proves the first assertion.

If the Z_n are free, `fpbs-factor-lift-cost-monotone` gives
C(Y) <= C(Z_{n+1}) <= C(Z_n), since Z_n is a factor of Z_{n+1} and of Y.
Together with the first assertion, C(Z_n) decreases to C(Y). QED.

**Remark 1.2.** Every intermediate factor between a free action and one
of its extensions is free. So the second assertion applies to any
increasing chain of intermediate factors of an extension of a free
action.

**Corollary 1.3 (limit ordinals).** Let alpha be a countable limit
ordinal. Let (Z_eta)_{eta < alpha} be an increasing chain of invariant
factors of a free Y, and let Z_alpha be the factor generated by their
union. Then C(Z_alpha) >= inf_{eta<alpha} C(Z_eta). *Proof:* apply
Theorem 1.1 to Z_alpha and a cofinal sequence eta_n -> alpha.

## 2. [FZ] The imported relative dichotomy

Source: A. Jamneshan, *An uncountable Furstenberg--Zimmer structure
theory*, Ergodic Theory Dynam. Systems 43 (2023) 2404--2436,
arXiv:2103.17167. The following is quoted verbatim from the arXiv TeX
source, `\label{thm-dichotomy1}`, Section 1.1:

> \begin{theorem}[Uncountable relative dichotomy]\label{thm-dichotomy1}
> Let $\mathcal{X}=(X,\mu,T)$ and $\mathcal{Y}=(Y,\nu,S)$ be  probability algebra $\Gamma$-dynamical systems and $\pi: \mathcal{X}\to \mathcal{Y}$ an extension.
> Exactly one of the following statements is true.
> \begin{itemize}
> \item[(i)] $\pi: \mathcal{X}\to \mathcal{Y}$ is a relatively weakly mixing extension.
> \item[(ii)] There exist an  probability algebra $\Gamma$-dynamical system $\mathcal{Z}=(Z,\lambda,R)$ and extensions $\phi:\mathcal{X}\to \mathcal{Z}$ and $\psi:\mathcal{Z}\to \mathcal{Y}$ such that $\psi$ is a non-trivial relatively compact extension.
> \end{itemize}
> \end{theorem}

The main-results subsection opens with "Let $\Gamma$ be a group and $X$
be a $\sigma$-complete Boolean algebra equipped with a countably additive
measure $\mu$ of total mass $1$". So neither countability nor ergodicity
is assumed. The proof of the restated
structure theorem at the end of the paper sets $\mathcal{Y}_1\coloneqq\mathtt{AP_{X|Y_0}}$
and repeats "in a transfinite recursion, while passing to inverse limits
at limit ordinals". For countable-complexity systems the paper points to
the classical theory: "This relative dichotomy is well understood for
systems of countable measure-theoretic complexity, e.g., see
\cite[\S 2.14]{tao2009poincare}".

**Translation to standard systems.** Take a countable Gamma acting on
standard probability spaces. Probability algebra systems are then
measure algebras of standard systems. An algebra extension corresponds
to a Gamma-invariant complete sub-sigma-algebra, and it has a pointwise
standard factor realization (Mackey point realization). In Jamneshan's
convention an "extension pi : X -> Y" has Y as the factor. So a pair
phi : Y -> Z, psi : Z -> W, applied to pi : Y -> W, realizes Z as an
intermediate invariant factor between W and Y. This is the only
translation used. It is standard measure theory, not part of the quote.

## 3. Derivation of the parent

**Theorem 3.1.** Assume N2 and N3 for Gamma. Let pi : Y -> X be an
extension of p.m.p. Gamma-actions on standard spaces, with X free. Then
C(Y) = C(X).

*Proof.* By lifting (`fpbs-factor-lift-cost-monotone`), C(Y) <= C(X). For
the reverse inequality, build intermediate invariant factors Z_alpha of
Y by transfinite recursion. They satisfy X <= Z_alpha <= Y, and each is
a sub-sigma-algebra.

* Z_0 = X.
* At a successor step, if Y -> Z_alpha is relatively weakly mixing, stop
  and set beta = alpha. Otherwise FZ(ii) gives an intermediate Z with
  Z -> Z_alpha a non-trivial relatively compact extension. Set
  Z_{alpha+1} = Z.
* At a limit alpha, Z_alpha is generated by the union of the Z_eta,
  eta < alpha.

**Termination.** The chain is strictly increasing at successor steps.
For each alpha < beta pick a unit vector in
L^2(Z_{alpha+1}) minus L^2(Z_alpha). These vectors are orthonormal in
the separable space L^2(Y). So the recursion stops at a countable
ordinal beta, and every limit ordinal <= beta has countable cofinality.

**Freeness.** Every Z_alpha is an extension of the free X, so it is free.

**Induction: C(Z_alpha) >= C(X).** At alpha = 0 this is equality. At a
successor, N2 for Z_{alpha+1} -> Z_alpha gives
C(Z_{alpha+1}) = C(Z_alpha). At a limit, Corollary 1.3 gives
C(Z_alpha) >= inf_{eta<alpha} C(Z_eta) >= C(X).

**Top.** Y -> Z_beta is relatively weakly mixing, so N3 gives
C(Y) = C(Z_beta) >= C(X). QED.

**Corollary 3.2 (the parent).** Let a be a free action and b Bernoulli.
Apply Theorem 3.1 to the projection a x b -> b, which needs no
ergodicity. It gives C(a x b) >= C(b). Then
`fpbs-bernoulli-noise-does-not-change-cost` gives C(a) = C(a x b) >= C(b).

**Converse.** The parent, together with Abert--Weiss maximality, gives
fixed price for Gamma. By `fpbs-factor-invariance-equals-fixed-price`,
all free factor maps then preserve cost, which includes N2 and N3. So,
over finitely generated Gamma, parent <=> N2 and N3. The split is a
decomposition, not a weakening of the target.

## 4. What each premise contains

**N2 contains compact actions, hence the rank-gradient question.** Let
a be a free action with discrete spectrum. An example is the boundary
action of Gamma on lim Gamma/Gamma_n for a normal chain with trivial
intersection. Then a x b -> b is relatively compact: L^2(a x b | b) is
spanned by the L^infty(b)-modules E tensor L^infty(b), where E runs over
the finite-dimensional invariant subspaces of L^2(a). So N2 gives
C(a) = C(b). With `fpbs-abert-nikolov-rank-gradient-equals-profinite-cost`,
N2 implies RG(Gamma, (Gamma_n)) = C(b) - 1 for every such normal chain.
That is an open question of Abert--Nikolov type.

N2 also contains every uniform finite-fibre extension. There
`fpbs-finite-fiber-cost-bound` shows that preservation is equivalent to
finite-index multiplicativity of cost minus one.

**Theorem 4.1 (profinite fibres reduce to finite fibres).** Let Gamma be
countably infinite and W a free p.m.p. Gamma-action with C(W) finite
(automatic for finitely generated Gamma). Let K be a compact metrizable
totally disconnected group, L <= K a closed subgroup and
rho : Gamma x W -> K a measurable cocycle. Let Z = W x_rho K/L be the
homogeneous skew product,

    g(w, kL) = (g w, rho(g, w) k L),

with measure mu x m_{K/L}. Pick a decreasing basis K_1 >= K_2 >= ... of
open normal subgroups, and let Z_n = W x_rho K/(L K_n). Then:

(a) Each Z_n -> W is a uniform q_n-point factor, q_n = [K : L K_n], and
Z -> Z_n -> W.

(b) C(Z_n) decreases to C(Z).

(c) If every uniform finite-fibre factor map of free Gamma-actions
preserves cost, then C(Z) = C(W). By `fpbs-finite-fiber-cost-bound`, that
hypothesis is equivalent to finite-index multiplicativity of cost minus
one for Gamma.

*Proof.*

(a) L K_n is an open subgroup, hence of finite index. The map
kL -> k L K_n is K-equivariant, so it intertwines the two skew-product
actions. The pushforward of m_{K/L} is the uniform measure on
K/(L K_n). So the conditional measures of Z_n over W are uniform on
q_n points.

(b) The factors Z_n increase, since L K_{n+1} <= L K_n. They generate Z
modulo null sets. The closed sets L K_n decrease with intersection L, by
compactness. So the countably many Borel maps K/L -> K/(L K_n) separate
the points of the standard Borel space K/L, and hence generate its Borel
sigma-algebra. Together with the base coordinate, they generate the Borel
sigma-algebra of W x K/L.

All the spaces are free, being extensions of W. The base W has finite
cost. Section 10 of `fpbs-traffic-variational-cost-identities` (for
finitely generated Gamma, equally Theorem 1.1 here) gives
C(Z_n) -> C(Z) decreasingly.

(c) Under the hypothesis, C(Z_n) = C(W) for every n, and (b) gives
C(Z) = C(W). QED.

**Consequence.** For ergodic systems, a relatively compact extension is a
homogeneous skew product. This is Jamneshan's isometric-extension theorem
for probability algebra systems, and Zimmer's theorem in the standard
case; it is imported, not quoted here. With that input, N2 splits in
three:
* finite-index multiplicativity, which covers finite and profinite fibre
  groups by Theorem 4.1;
* skew products whose fibre group K has a nontrivial identity component
  K^0, for example circle or torus rotation cocycles;
* non-ergodic compact extensions.

Theorem 4.1 is unconditional. The consequence is a remark over the
imported structure theorem. For a fibre group with nontrivial identity
component, the quotients K/(L K_n) no longer separate points, so the
chain argument fails.

**N3 contains weakly mixing actions.** Let a be weakly mixing. The
relative product (a x b) x_b (a x b) is a x a x b. Here a x a is weakly
mixing and b is ergodic, so the product is ergodic. Its invariant
functions are therefore constant, and in particular b-measurable. So
a x b -> b is relatively weakly mixing, and N3 gives C(a) = C(b) for
every free weakly mixing a. Compact and weakly mixing actions are
disjoint classes. Neither premise is known to imply the other.

**N3 is not a weak-containment statement.** By Abert--Weiss, b is weakly
contained in every free action, so b ≺ a x b. Monotonicity of cost
(`cost-is-constant-on-weak-equivalence-classes`) then gives
C(a x b) <= C(b), which is the easy direction.

For the reverse inequality, monotonicity would need a x b ≺ b. Since
a x b is weakly equivalent to a (`fpbs-bernoulli-noise-does-not-change-cost`),
that amounts to a being weakly equivalent to b. So for a weakly mixing a
that is not weakly equivalent to b, N3 cannot follow from monotonicity
alone. Such a proof must use the relative weak mixing structure itself,
for example ergodicity of the relative self-joining, and not only the
weak-containment class.

## 5. Relation to the block-localization hole

Theorem 6.1 of `relative-cycle-exchange.md` rounds one generating
graphing uniformly over the whole extension. The FZ split replaces that
uniform rounding with three regimes that behave differently:

* Compact fibres, where invariant finite-rank modules exist, so
  fibrewise averaging is available.
* Inverse limits, which cost nothing extra, by N1.
* A relatively weakly mixing top, where no invariant finite-rank module
  exists.

The recorded dead ends for block rounding (determinantal deletion on
T_2r x C_M, fixed certificates on F_r x C_M, the retained-boundary floor)
are all tested on finite-fibre extensions. So they are evidence about the
compact regime N2. Their bearing on N3 is untested: no localization
countermodel over a relatively weakly mixing extension is recorded.

**Correction (referee lens 1, 2026-09-17).** The last paragraph is false.
* `fpbs-retained-boundary-rounding-isoperimetric-floor` holds for every
  free factor Y -> X. Its worked case is a x b -> b on F_2 x Z for any a,
  including weakly mixing a, where F_0 >= 5/3.
* `fpbs-oblivious-certificates-never-localize` covers lifts on a x b -> b
  for any a, already on Z^2.

So the recorded obstructions reach the relatively weakly mixing top for
those rounding and certificate classes.
