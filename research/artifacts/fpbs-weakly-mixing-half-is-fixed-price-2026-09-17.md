# The weakly mixing half P_w of the Furstenberg-Zimmer split is all of fixed price for groups without (T)

Belief-breaker lane, swarm-0917 wave 7 (agent swarm-0917-w7-w7-fp-break), 2026-09-17/18.

## 0. Summary

`fpbs-compact-weakly-mixing-tower-decomposes-cost-preservation` splits fixed price for a
group G into two prerequisites that were meant to be independently failable:

* P_c(G): relatively compact extensions V -> W of free p.m.p. G-actions preserve cost;
* P_w(G): relatively weakly mixing extensions V -> W of free p.m.p. G-actions preserve cost
  (`fpbs-relatively-weakly-mixing-extensions-preserve-cost`).

The recorded need b9eea368 says that P_w "contains C(a)=C(b) for all free weakly mixing a".
This note shows it contains much more.

**Theorem A.** Let G be an infinite finitely generated group without property (T). Then the
following are equivalent.

1. G has fixed price.
2. P_w(G).
3. The single product extension `a_inf x b -> b` preserves cost, where `a_inf` is a weakly
   mixing realization of the maximum action and b is a Bernoulli shift.

In particular P_w(G) implies P_c(G) for every such G, so on the non-(T) class the split
P_c + P_w is not a decomposition into independent prerequisites: P_c is redundant and P_w
carries the whole problem.

**Theorem B (obstruction for Kazhdan groups).** Let G be a countable group with property (T).
If a p.m.p. action a of G is weakly contained in a weakly mixing p.m.p. action c, then a is
weakly mixing. Hence the argument of Theorem A (and every argument that proves the Bernoulli
lower bound on weakly mixing free actions and transfers it by monotonicity of cost under weak
containment) gives exactly the free weakly mixing actions of a Kazhdan group and dies at every
free action with a nonzero finite-dimensional Koopman subrepresentation (a nontrivial Kronecker
factor), for example every free profinite action of a residually finite Kazhdan group.

So for Kazhdan groups, P_w(G) yields C(w) = C(b) for every free weakly mixing w (Corollary C)
and the whole remaining content of fixed price sits in free actions with a nontrivial
Kronecker factor, which is P_c territory. The Furstenberg-Zimmer split is genuine only there.

Everything below is a deduction over imported statements, which are quoted in the claim nodes
`burton-kechris-maximum-action-weakly-mixing-without-t`,
`burton-kechris-cost-usc-and-maximum-action`, `burton-kechris-koopman-weak-containment`,
`cost-is-constant-on-weak-equivalence-classes`, `fpbs-bernoulli-maximal-cost` and
`fpbs-bernoulli-noise-does-not-change-cost`.

## 1. Conventions and three Hilbert-space lemmas

G is a countable group. For a p.m.p. action a of G on (X, mu), kappa^a is the Koopman
representation on L^2(X, mu), kappa^a(g)f(x) = f(g^{-1} x), and kappa^a_0 is its restriction to
L^2_0(X, mu), the orthogonal complement of the constants (Burton-Kechris, Section 4). A unitary
representation is *weak mixing* if it has no nonzero finite-dimensional subrepresentation
(Burton-Kechris, Section 1: "Recall that a weak mixing representation is one that has no non-0
finite-dimensional subrepresentations."). The action a is *weakly mixing* if kappa^a_0 is weak
mixing. This is the standard notion, and it is the one used in Burton-Kechris Theorem 3.20.

G has *property (T)* if every unitary representation pi with almost invariant vectors (for every
finite F in G and eps > 0 a unit vector v with ||pi(g)v - v|| < eps for g in F) has a nonzero
invariant vector. This is the definition, not an import.

Throughout, HS(H, K) is the space of Hilbert-Schmidt operators H -> K with the trace inner
product. It is canonically isometric to K (x) conj(H), with v (x) conj(u) corresponding to the
rank-one operator x -> <x, u> v. Under this identification the representation pi (x) conj(sigma)
becomes S -> pi(g) S sigma(g)^{-1}, so its invariant vectors are exactly the Hilbert-Schmidt
intertwiners from sigma to pi.

**Lemma 1 (no finite-dimensional subrepresentation gives small correlations).** Let pi be a
unitary representation on H with no nonzero finite-dimensional subrepresentation. Then for every
xi in H and eps > 0 there is g in G with |<pi(g) xi, xi>| < eps.

*Proof.* Let xi != 0 and suppose |<pi(g) xi, xi>| >= delta > 0 for all g. Let P be the rank-one
operator x -> <x, xi> xi, an element of HS(H) = HS(H, H), and let the orbit be
P_g = pi(g) P pi(g)^{-1}. Then <P_g, P>_HS = tr(P_g P) = |<pi(g) xi, xi>|^2 >= delta^2. Let S_0 be
the element of least norm in the closed convex hull K of {P_g}. The set K is invariant under the
isometric action S -> pi(g) S pi(g)^{-1} and S_0 is unique, so S_0 is invariant. Every element of
the convex hull has inner product at least delta^2 with P, and so does S_0 by continuity. So
S_0 != 0. Each P_g is positive, so S_0 is positive, Hilbert-Schmidt and hence compact, and it
commutes with every pi(g). A nonzero eigenvalue of S_0 has a finite-dimensional eigenspace, and
that eigenspace is pi-invariant, a contradiction. []

**Lemma 2 (tensoring preserves weak mixing).** If sigma on H has no nonzero finite-dimensional
subrepresentation and rho on K is any unitary representation, then sigma (x) rho has none.

*Proof.* Let W in H (x) K be invariant, finite-dimensional and nonzero, with orthogonal projection
P_W, a positive trace-class operator of trace dim W that commutes with (sigma (x) rho)(g). Let Q
be its partial trace over K, the operator on H with <Q x, y> = sum_k <P_W (x (x) e_k), y (x) e_k>
for an orthonormal basis (e_k) of K. Q is positive and trace class with tr Q = dim W > 0, and
sigma(g) Q sigma(g)^{-1} is the partial trace of (sigma(g) (x) rho(g)) P_W (sigma(g) (x) rho(g))^{-1},
because the partial trace is invariant under conjugation by 1 (x) rho(g). That operator is P_W,
so Q commutes with sigma. A nonzero eigenspace of the compact positive operator Q is then a
finite-dimensional sigma-invariant subspace, a contradiction. []

This is the fact that Brannan-Kerr attribute to the Kerr-Pichot argument ("weak mixing is
preserved under tensor products with arbitrary representations").

**Lemma 3.** If A is a weakly mixing p.m.p. action, then so is the diagonal action A x A.

*Proof.* L^2_0(A x A) = (L^2_0(A) (x) 1) + (1 (x) L^2_0(A)) + (L^2_0(A) (x) L^2_0(A)), an
orthogonal sum of invariant subspaces. So kappa_0^{A x A} is kappa_0^A + kappa_0^A +
kappa_0^A (x) kappa_0^A. Each summand has no nonzero finite-dimensional subrepresentation, by the
hypothesis and Lemma 2. A finite-dimensional invariant subspace of an orthogonal sum projects onto
a finite-dimensional invariant subspace of each summand, and at least one projection is nonzero.
So the sum has none either. []

## 2. Product extensions over a weakly mixing fibre are relatively weakly mixing

For an extension X -> Y, write <f, h>_{L^2(X|Y)} = E(f conj(h) | Y), which is the module inner
product in Definition 6.1 of Jamneshan (quoted in `relative-furstenberg-zimmer-dichotomy-citation`).
For a function f in L^2(X), write phi_f = E(|f|^2 | Y).

**Reading of Definition 6.1.** The quantity ||<(T^g)* f, f>_{L^2(X|Y)}||_{L^2(Y)} in Definition 6.1
is finite whenever phi_f is in L^2(Y), by the conditional Cauchy-Schwarz inequality below. It
need not be finite for an arbitrary f in L^2(X). We prove the condition of Definition 6.1 for
every f with E(f|Y) = 0 and phi_f in L^2(Y). This class contains every bounded f and every f in
the Kaplansky-Hilbert module L^2(X|Y) (phi_f in L^infinity(Y)), which is where the module inner
product lives. So Lemma 4 covers the module reading of "relatively weakly mixing" and the
reading over all f with phi_f in L^2(Y) (see the verification boundary in Section 5). The choice between (T^g)* = Koopman operator of g or of g^{-1} does not
matter, because the condition is "there exists g" and the norm is unchanged under g -> g^{-1}
(apply the Koopman operator U_g, which is an isometry of L^2(Y), to E(U_{g^{-1}} f conj f | Y) and
get the complex conjugate of E(U_g f conj f | Y)).

**Lemma 4.** Let A be a weakly mixing p.m.p. action of G on (Z, zeta), and let C be any p.m.p.
action of G on (Y, nu). Then the coordinate projection A x C -> C is relatively weakly mixing:
for every f in L^2(Z x Y) with E(f|Y) = 0 and phi_f in L^2(Y), and every eps > 0, there is g in
G with ||E(U_g f conj(f) | Y)||_{L^2(Y)} < eps.

No freeness or ergodicity of C is used.

*Proof.* By Fubini, for nu-a.e. y the section f_y = f(., y) is in L^2(Z), with
phi_f(y) = ||f_y||^2, E(f|Y)(y) = int f_y d zeta = 0, and
E(U_g f conj f | Y)(y) = <kappa^A(g) f_{g^{-1} y}, f_y>. The conditional Cauchy-Schwarz inequality
|E(U_g f conj f|Y)|^2 <= E(|U_g f|^2 | Y) E(|f|^2 | Y) = (U_g phi_f) phi_f then shows that
E(U_g f conj f | Y) is in L^2(Y), with norm at most ||phi_f||_{L^2(Y)}.

Define F on Z x Z x Y by F(z, z', y) = f(z, y) conj f(z', y). Then

* ||F||^2 = int (int |f(z,y)|^2 dz)(int |f(z',y)|^2 dz') dy = ||phi_f||^2_{L^2(Y)} < infinity;
* for every y, int int F(z, z', y) dz dz' = |E(f|Y)(y)|^2 = 0, so F is orthogonal to L^2(Y), that
  is, F is in L^2_0(Z x Z) (x) L^2(Y);
* the Koopman operator of the diagonal action (A x A) x C satisfies
  (U_g F)(z, z', y) = (U_g f)(z, y) conj (U_g f)(z', y), hence
  <U_g F, F> = int |int (U_g f)(z, y) conj f(z, y) dz|^2 dy = ||E(U_g f conj f | Y)||^2_{L^2(Y)}.

The representation of G on L^2_0(Z x Z) (x) L^2(Y) is kappa_0^{A x A} (x) kappa^C. By Lemma 3,
kappa_0^{A x A} has no nonzero finite-dimensional subrepresentation, and by Lemma 2 neither does
its tensor product with kappa^C. Lemma 1 applied to F and eps^2 gives g with
<U_g F, F> < eps^2, that is, ||E(U_g f conj f | Y)||_{L^2(Y)} < eps. []

This is the fact recorded without proof in the body of
`fpbs-relatively-weakly-mixing-extensions-preserve-cost` ("for a free weakly mixing action a and a
Bernoulli shift b, the projection a x b -> b is relatively weakly mixing"). Here it is proved for
an arbitrary base C.

**Remark (necessity of weak mixing of the fibre, partial).** If A is not ergodic, then A x C -> C
is not relatively weakly mixing: take f = (1_B - zeta(B)) (x) 1 for a nontrivial A-invariant set B.
Then E(U_g f conj f | Y) is the constant zeta(B)(1 - zeta(B)) for every g. If A is ergodic and
kappa^A_0 has a one-dimensional subrepresentation spanned by h, then |h| is invariant, hence
constant, so h is bounded. With f = h (x) 1, |E(U_g f conj f|Y)| = ||h||^2 for every g, and again
A x C -> C is not relatively weakly mixing. Only this partial converse is used below, and only in
a remark.

## 3. Proof of Theorem A

Let G be infinite, finitely generated and without property (T). Fix a standard non-atomic
probability space (X, mu). Every free p.m.p. action of the infinite group G lives on a non-atomic
standard space, so it is isomorphic to an element of A(G, X, mu); cost is an isomorphism
invariant, and we work in A(G, X, mu) throughout. "Fixed price" means that all free p.m.p. actions
of G have the same cost.

**Step 1: a weakly mixing maximum action.** By `burton-kechris-cost-usc-and-maximum-action`
(item 2) there is a maximum a_inf for weak containment in A(G, X, mu), unique up to weak
equivalence. By `burton-kechris-maximum-action-weakly-mixing-without-t` (Burton-Kechris,
proof of Theorem 3.20, using Kerr-Pichot), since G does not have (T), a_inf can be realized as a
weakly mixing action. So fix a weakly mixing a_w in A(G, X, mu) (transport the product of Burton-
Kechris to (X, mu) by an isomorphism of standard non-atomic spaces) that is weakly equivalent to
a_inf. Then c ≼ a_inf ≼ a_w for every c in A(G, X, mu), so a_w is also a maximum.

**Step 2: a_w is free.** Let b in A(G, X, mu) be a Bernoulli shift (any nontrivial standard base;
the shift is free because G is infinite, and non-atomic). b ≼ a_w by maximality, and the free
actions are upward closed under ≼ (`burton-kechris-cost-usc-and-maximum-action`, item 3). So a_w
is free. The product a_w x b is free because it has the free factor b.

**Step 3: the one extension.** By Lemma 4 with A = a_w and C = b, the projection a_w x b -> b is
a relatively weakly mixing extension of free actions. If it preserves cost (hypothesis (3), which
is an instance of (2)), then C(a_w x b) = C(b).

**Step 4: Bernoulli noise.** By `fpbs-bernoulli-noise-does-not-change-cost`, applied to the free
action a_w, C(a_w x b) = C(a_w). So C(a_w) = C(b), and this holds for every Bernoulli shift b.

**Step 5: squeeze.** Let a be any free action. Since a ≼ a_w, monotonicity of cost under weak
containment for free actions of finitely generated groups (`cost-is-constant-on-weak-equivalence-classes`:
"If b ≺ a, then C(a) ≤ C(b)") gives C(a_w) ≤ C(a). By `fpbs-bernoulli-maximal-cost` the
supremum of costs of free actions is attained by some nontrivial Bernoulli action b_0, so
C(a) ≤ C(b_0) = C(a_w) by Step 4. Hence C(a) = C(a_w) for every free a: G has fixed price.

This proves (3) => (1). (1) => (2) is immediate: under fixed price every extension of free actions
preserves cost. (2) => (3) is Lemma 4 together with Steps 1-2, which show that a_w x b -> b is a
relatively weakly mixing extension of free actions. []

**Remarks.**

1. By Burton-Kechris Theorem 7.1 (quoted in `burton-kechris-cost-usc-and-maximum-action`),
   C(a_inf) = C(G), the infimum cost. The top a_w x b of the extension has cost C(a_w) = C(G)
   by Step 4, and the base has cost C(b). So (3) says exactly C(G) = C(b), and fixed price for a
   non-(T) group is equivalent to this single instance of P_w.
2. P_c is not used. So P_w(G) => fixed price(G) => P_c(G) for every infinite finitely generated
   G without (T).
3. (T) passes to quotients, so every finitely generated group with an infinite amenable quotient,
   or with a quotient without (T), lacks (T). This note does not claim that fixed price is known
   or unknown for any particular group of the class. What it shows is structural: P_w for all
   finitely generated groups implies fixed price for every finitely generated group without (T),
   so P_w is not a proper sub-problem on that class.

## 4. Theorem B: for Kazhdan groups, weak containment in a weakly mixing action forces weak mixing

**Theorem B.** Let G be a countable group with property (T), and let a, c be p.m.p. actions of G
with a ≼ c. If c is weakly mixing, then a is weakly mixing.

*Proof.* Suppose a is not weakly mixing. Let sigma be a nonzero finite-dimensional
subrepresentation of kappa^a_0, on H_sigma in L^2_0(X_a) with orthonormal basis u_1, ..., u_n. Put
m_ij(g) = <sigma(g) u_i, u_j> = <kappa^a_0(g) u_i, u_j>. Since sigma(g) is unitary,
sum_{i,j} |m_ij(g)|^2 = n for every g.

By `burton-kechris-koopman-weak-containment` (Burton-Kechris Proposition 4.1), a ≼ c implies
kappa^a_0 ≼_Z kappa^c_0. Fix a finite F in G containing the identity and eps in (0, 1/2). By the
definition of ≼_Z (Burton-Kechris Definition 1.3, quoted there) there are w_1, ..., w_n in
L^2_0(X_c) with |m_ij(g) - <kappa^c_0(g) w_i, w_j>| < eps for all g in F and all i, j.

Consider the representation pi = kappa^c_0 (x) conj(sigma) on L^2_0(X_c) (x) conj(H_sigma) and the
vector eta = sum_i w_i (x) conj(u_i). Then

* ||eta||^2 = sum_i ||w_i||^2, which lies in (n(1 - eps), n(1 + eps)) (take g = e, i = j);
* <pi(g) eta, eta> = sum_{i,j} <kappa^c_0(g) w_i, w_j> conj(m_ij(g)), so
  |<pi(g) eta, eta> - n| = |sum_{i,j} (<kappa^c_0(g) w_i, w_j> - m_ij(g)) conj(m_ij(g))| < n^2 eps
  for g in F (using |m_ij| <= 1);
* hence ||pi(g) eta - eta||^2 = 2||eta||^2 - 2 Re <pi(g) eta, eta> < 2n eps + 2n^2 eps, and
  ||pi(g) eta - eta||^2 / ||eta||^2 < (2n + 2n^2) eps / (n(1 - eps)) <= 4(1 + n) eps for g in F.

Since F and eps are arbitrary, pi has almost invariant unit vectors. By property (T) it has a
nonzero invariant vector. Under L^2_0(X_c) (x) conj(H_sigma) = HS(H_sigma, L^2_0(X_c)) (Section 1),
that is a nonzero operator S: H_sigma -> L^2_0(X_c) with kappa^c_0(g) S = S sigma(g) for all g. Its
range S(H_sigma) is nonzero, finite-dimensional, and kappa^c_0-invariant. So c is not weakly
mixing. []

**Corollary C.** Let G be finitely generated with property (T), and assume P_w(G). Then
C(w) = C(b) for every free weakly mixing action w and every Bernoulli shift b.

*Proof.* Lemma 4 makes w x b -> b a relatively weakly mixing extension of free actions, so
C(w x b) = C(b), and `fpbs-bernoulli-noise-does-not-change-cost` gives C(w x b) = C(w). []

(Corollary C holds for every finitely generated G, with the same proof. For G without (T) it is
superseded by Theorem A.)

**The obstruction.** Call a *weak-containment transfer* any argument of the form: find a free
action c with a ≼ c and C(c) = C(b), and conclude C(a) >= C(c) = C(b) by monotonicity. Together
with Bernoulli maximality this gives C(a) = C(b). By Theorem B, for a Kazhdan group G, if c is
weakly mixing then so is a. So a weak-containment transfer from the weakly mixing actions
reached by Corollary C (or by any other method that controls only weakly mixing actions) reaches
exactly the free weakly mixing actions and nothing else. It never reaches a free action whose
Koopman representation kappa_0 has a nonzero finite-dimensional subrepresentation: a nonergodic
free action, or an ergodic free action with a nontrivial Kronecker factor, for example a free
profinite action of a residually finite Kazhdan group such as SL(3, Z), whose kappa_0 is a sum of
finite-dimensional representations.

For G without (T) the same transfer runs through the weakly mixing maximum a_w, which weakly
contains everything. For G with (T), a_inf is not ergodic (Burton-Kechris Theorem 3.20), and by
Theorem B no weakly mixing action is maximal. The difference between the two cases is exactly
the dichotomy of Theorem 3.20.

## 5. Consequences for the Furstenberg-Zimmer lane, and the verification boundary

**What changes.**

1. `fpbs-relatively-weakly-mixing-extensions-preserve-cost` (P_w) is not a sub-problem on the
   non-(T) class. For every infinite finitely generated G without (T), P_w(G) is equivalent to
   fixed price for G (Theorem A). A proof of P_w by a method that does not see (T) would prove
   fixed price for every such group in one step. The bounty of P_w is essentially the goal.
2. The node `fpbs-compact-weakly-mixing-tower-decomposes-cost-preservation` gives
   fixed price <= P_c + P_w. For non-(T) groups, P_w alone suffices. So the split does not
   decompose the difficulty there. Any lane that proves P_c first and hopes P_w is easier is
   misdirected on that class.
3. The split has content only for Kazhdan groups. There P_w gives the weakly mixing free actions
   (Corollary C), and Theorem B shows that no monotonicity transfer from weakly mixing actions
   reaches the rest. The residual problem for a Kazhdan group is: free actions a with a
   nonzero finite-dimensional subrepresentation of kappa^a_0. These are the nonergodic ones and
   the ergodic ones with a nontrivial Kronecker (distal-level-one) factor. This is the territory
   of P_c and of the relatively compact floors of the tower.
4. A useful reformulation for the non-(T) class: fixed price for G is equivalent to the
   single equality C(G) = C(b), where C(G) = C(a_inf) (Burton-Kechris Theorem 7.1). Theorem A
   gives no new handle on that equality. It shows that P_w is that equality in disguise.

**What does not change.** Nothing here proves or refutes any cost equality. Theorems A and B
are structural. No claim is made about the cost of any specific action.

**Verification boundary.**

* Lemmas 1-4, Theorem B and the deductions in Section 3 are complete proofs written here. They
  use only Hilbert-space facts (least-norm points of closed convex sets, the spectral theorem for
  compact self-adjoint operators, partial traces, and HS(H, K) = K (x) conj(H)) and the imports.
  They have not been through a referee pass.
* The import `burton-kechris-maximum-action-weakly-mixing-without-t` is the sentence of
  Burton-Kechris quoted there, which relies on Kerr-Pichot. The Kerr-Pichot paper itself was not
  read. The secondary description in Brannan-Kerr (arXiv:1706.00554) is quoted as corroboration.
* The definition of relatively weakly mixing is read on the class phi_f in L^2(Y) (Section 2).
  If a later reader insists on literally all f in L^2(X), with a norm that may be +infinity, then
  the hypothesis of P_w becomes stricter. Whether a_w x b -> b satisfies that stricter reading is
  not decided here. Theorem A is stated and proved for P_w with relative weak mixing read on the
  class phi_f in L^2(Y), which contains the module L^2(X|Y). This is the reading under which the
  defining quantity is a real number.
* Freeness of a_w uses only b ≼ a_w and the upward closure of freeness under ≼. It does not use
  any freeness claim of Kerr-Pichot.

## 6. An open bridge for Kazhdan groups (spark, not established)

By `fpbs-kazhdan-groups-have-cost-one` (Hutchcroft-Pete), every infinite Kazhdan group G has
cost C(G) = 1, the infimum over free actions. Suppose some free *weakly mixing* action w of G has
cost 1. Then P_w(G) gives C(b) = C(w) = 1 by Corollary C. Every free action has cost at least 1
and at most C(b), so G has fixed price 1.

So for a Kazhdan group G:

    P_w(G) and (some free weakly mixing action of G has cost 1)  =>  G has fixed price 1.

Theorem B does not block this, because it constrains what is weakly contained in a weakly mixing
action, not which costs weakly mixing actions have. Whether the Hutchcroft-Pete low-cost actions,
or ergodic components of a_inf (which have cost 1 almost surely, since cost integrates over the
ergodic decomposition), can be chosen weakly mixing is not decided here. The Hutchcroft-Pete
construction was not read. If the answer is yes for all Kazhdan groups, then P_w carries the whole
fixed price problem for every infinite finitely generated group, and P_c is redundant everywhere.
