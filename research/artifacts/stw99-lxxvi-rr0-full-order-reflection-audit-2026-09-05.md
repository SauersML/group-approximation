# Full first-factor Cu order reflection for real-rank-zero simple pure fields

Status: complete proof; internal mathematical review completed on 5 September 2026.
This proves order reflection for every positive source class. Surjectivity
for arbitrary mixed target classes remains a separate assertion.

## Theorem

Let D be separable, simple, stably finite, pure, and real rank zero.
For every second-countable locally compact Hausdorff space X, the actual
first-factor homomorphism

```text
phi_X:C_0(X,D) -> C_0(X,D tensor Z),   f |-> f tensor 1_Z,
```

induces an order embedding on Cu. There is no dimension bound on X.
Equivalently, for arbitrary positive a,b in C_0(X,D tensor K),

```text
phi_X(a) <=_Cu phi_X(b)  implies  a <=_Cu b.
```

The input results are the previously proved all-base compact-left
reflection theorem and the exact relative strict positive-source
extension theorem. The latter is used only on finite-dimensional
compact bases. The limit argument below removes the dimension bound.

## 1. Inputs and their precise scope

Put B=D tensor K and write H_d=closure(dB) for d in B_+.

1. The coefficient first-factor map induces an isomorphism
   Cu(D) -> Cu(D tensor Z). This is the simple stably finite case of
   the concrete theorem, Proposition 23 of
   [Schafhauser--Tikuisis--White](https://arxiv.org/pdf/2506.10902v2).
2. For every compact metrizable T, every projection p in C(T,B),
   and every positive d in C(T,B), phi_T(p)<=_Cu phi_T(d) implies
   p<=_Cu d. This is the preceding
   [compact-left audit](stw99-lxxvi-rr0-relative-projection-selection-audit-2026-09-05.md).
3. If T is finite-dimensional compact metrizable, Y is closed in T,
   and positive contractions c,d satisfy [c(t)]<=[d(t)] everywhere
   and strict inequality off Y whenever c(t) is nonzero, every
   continuous z_Y with z_Y*z_Y=c|Y and z_Y(y) in H_d(y) extends to
   z in C(T,B) with z*z=c and zz* in Her(d). This is Section 6 of
   the [strict positive-source extension audit](stw99-lxxvi-rr0-cutoff-relative-selection-audit-2026-09-05.md).

We also use the following exact form of Brown--Ciuperca, Theorem 3.5:
in a stable finite C*-algebra B, compactness of [h] in Cu(B) implies
that the actual positive element h has spectrum contained in
{0} union [delta,infinity) for some delta>0. Thus its support projection
belongs to B. Here B=D tensor K is stable and finite because D is
stably finite. We do not apply this assertion to an arbitrary algebra,
nor assume stable rank one for C(T,D). The primary paper is
[Isomorphism of Hilbert modules over stably finite C*-algebras](https://arxiv.org/abs/0811.0958).

## 2. The closed compact core for a spectral cutoff

First suppose X is finite-dimensional compact metrizable. Let a,b
be positive contractions in C(X,B), and assume phi_X(a)<=_Cu phi_X(b).
Coefficient order reflection after evaluation gives

```text
[a(x)] <= [b(x)]   for every x in X.
```

Fix eta>0, set c=(a-eta)_+, and define

```text
E_eta = {x in X : [c(x)]=[b(x)] is nonzero},
K = closure(E_eta).
```

We do not assert that E_eta itself is closed. We show that the chosen
element a|K has a uniform spectral gap, and that equality of its
fiberwise Cu class with that of b persists on K.

For x in E_eta, the inequalities

```text
[c(x)] <= [a(x)] <= [b(x)] = [c(x)]
```

are equalities. Since [(a(x)-eta)_+] << [a(x)], their common class
is compact. Brown--Ciuperca applies in B to a(x) and c(x). Their
support projections r_x=s(a(x)) and q_x=s(c(x)) therefore belong
to B, satisfy q_x<=r_x, and have equal Cu classes. Projection Cuntz
equivalence is Murray--von Neumann equivalence. The projection r_x
is finite, so its subprojection q_x cannot be properly equivalent
to r_x. Consequently q_x=r_x, and

```text
spec(a(x)) is contained in {0} union (eta,infinity).
```

Moreover, ||a(x)||>eta because c(x) is nonzero. Norm continuity and
spectral continuity for self-adjoint elements show that, for every
y in K,

```text
spec(a(y)) is contained in {0} union [eta,infinity),
||a(y)|| >= eta.
```

Choose a continuous function f on [0,1] which is zero on [0,eta/2]
and one on [eta,1], whenever K is nonempty. Functional calculus gives
an actual continuous projection r=f(a|K) in C(K,B), and

```text
r=s(a|K),   [r]=[a|K] in Cu(C(K,B)).
```

If eta>=1, the cutoff is zero and comparison is automatic, so the
construction is needed only for 0<eta<1. An empty K requires no
boundary data.

For completeness, equality of the fiber classes also persists on K.
Fix y in K and delta>0. Choose x in E_eta sufficiently close to y
that ||b(x)-b(y)||<delta and ||r(x)-r(y)||<1. The perturbation
comparison for positive elements and equivalence of close projections
give

```text
[(b(y)-delta)_+] <= [b(x)] = [r(x)] = [r(y)].
```

Taking the supremum over delta decreasing to zero gives
[b(y)]<=[r(y)]=[a(y)]. The reverse inequality was already known.
Thus [a(y)]=[b(y)] for every y in K. This argument is about fiberwise
Cu equality; it does not identify any chosen Hilbert modules or
assert a global projection equivalence for b|K.

## 3. An actual prescribed embedding on the core

Restrict the original global comparison to K. Since a|K is Cuntz
equivalent to r, it gives

```text
phi_K(r) <=_Cu phi_K(b|K).
```

Compact-left reflection, applied to the compact metrizable space K,
therefore yields r<=_Cu b|K. Projection comparison supplies an actual
partial isometry t in C(K,B) satisfying

```text
t*t=r,   tt* in Her(b|K).
```

This is the usual projection-into-hereditary-algebra realization of
Cuntz comparison. No conversion of arbitrary equal Cu classes into
a chosen module isomorphism is being used.

Set

```text
z_K=t(c|K)^(1/2).
```

Since r(c|K)=c|K, we have z_K*z_K=c|K. Since tt* belongs to
Her(b|K), the element z_K belongs to closure((b|K)C(K,B)); in
particular z_K(y) belongs to H_b(y) for every y in K. The map z_K
is norm continuous.

Off K, whenever c(x) is nonzero, the comparison [c(x)]<=[b(x)]
is strict: equality would put x in E_eta and hence in K. We may
therefore apply the exact relative strict extension theorem with
source c, target b, and closed boundary K. It supplies z in C(X,B)
such that

```text
z*z=c,   zz* in Her(b),   z|K=z_K.
```

Thus (a-eta)_+<=_Cu b. The case K empty uses the same theorem with
empty boundary. This holds for every eta>0, so a<=_Cu b. We have
proved full Cu order reflection on every finite-dimensional compact
metrizable base, with no assumption that either global class is
compact or soft.

## 4. Order embeddings pass to sequential Cu limits

We record the needed limit fact explicitly. Suppose there are
commuting sequential systems of Cu-semigroups S_i,T_i and Cu
morphisms f_i:S_i -> T_i, each of which is an order embedding.
Write alpha and beta for the connecting maps and f:S -> T for
the induced map on limits. Then f is an order embedding.

We use two standard properties of the sequential Cu limit:
every element is the supremum of an increasing sequence of images
of stage elements; and if beta_i,infinity(v)<=beta_j,infinity(w),
then for each v'<<v the inequality beta_i,k(v')<=beta_j,k(w)
holds at some common later stage k. These are the approximation
and comparison clauses in the construction of Cu limits.

Suppose f(x)<=f(y). Write y as the supremum of an increasing
sequence alpha_j,infinity(t_j) of stage images. Fix a stage element
v in S_i with alpha_i,infinity(v)<=x, and elements u<<w<<v.
Then

```text
beta_i,infinity(f_i(w))
  << beta_i,infinity(f_i(v))
  <= f(x) <= f(y)
  = sup_j beta_j,infinity(f_j(t_j)).
```

For some stage j, the leftmost element is at most
beta_j,infinity(f_j(t_j)). As f_i(u)<<f_i(w), the comparison clause
gives a common later stage k with

```text
beta_i,k(f_i(u)) <= beta_j,k(f_j(t_j)).
```

Commutation and order reflection by f_k imply
alpha_i,k(u)<=alpha_j,k(t_j). Passing to the limit gives
alpha_i,infinity(u)<=y. Interpolating between each u<<v and v,
then taking suprema, proves alpha_i,infinity(v)<=y. Finally express
x as a supremum of increasing stage images to conclude x<=y.

Only the stage maps f_i must be order embeddings. No such assumption
on the connecting maps is needed. Sequential continuity for Cu of
C*-algebras is Coward--Elliott--Ivanescu, Theorem 2; a general
form is Antoine--Perera--Thiel, Corollary 3.2.9 in
[Tensor products and regularity properties of Cuntz semigroups](https://arxiv.org/pdf/1410.0483).

## 5. Arbitrary compact metrizable bases

There is a direct finite-dimensional approximation which avoids a
polyhedral approximation premise. Embed the compact metrizable X
in the Hilbert cube [0,1]^N, and let X_n be its image under the first
n coordinate projections. Each X_n is compact metrizable of covering
dimension at most n. The coordinate maps X_(n+1) -> X_n are
surjective, and X is their inverse limit: compatible finite
coordinates determine a point of X by compactness.

The pullbacks of C(X_n) form an increasing unital self-adjoint
algebra separating points of X, hence are uniformly dense in C(X)
by Stone--Weierstrass. Taking elementary tensors with D, respectively
D tensor Z, gives inductive limit identifications

```text
C(X,D) = lim_n C(X_n,D),
C(X,D tensor Z) = lim_n C(X_n,D tensor Z).
```

The first-factor maps commute with these coordinate pullbacks.
Section 3 proves Cu order reflection at every stage. Cu continuity
and Section 4 therefore prove order reflection over X. The
dimensions of the X_n need not be uniformly bounded.

## 6. Locally compact bases and the exact remaining issue

For second-countable locally compact Hausdorff X, its one-point
compactification X^+ is compact metrizable. The ideal inclusions
C_0(X,D) subset C(X^+,D) and their target analogues induce order
embeddings on Cu. The compact-base theorem applied to X^+ therefore
reflects comparison of source ideal elements, and the source ideal
inclusion reflects it back to C_0(X,D). The target ideal is exactly
C_0(X,D tensor Z); thus this argument concerns the actual prescribed
first-factor map throughout.

The result combines with the preceding compact-class and full-soft
theorems to control all order relations between arbitrary source
classes, not just relations internal to those two subclasses.
Surjectivity for arbitrary target classes has not been proved here.
A sufficient remaining realization statement is the sandwich
condition: whenever y'<<y in the target Cu-semigroup, there is a
source class x with y'<=Cu(phi_X)(x)<=y. Order reflection would make
the source classes obtained between consecutive terms of a rapidly
increasing target approximation increasing, proving surjectivity.

The compact-level-set method has prior art: Tikuisis,
[The Cuntz semigroup of continuous functions into certain simple C*-algebras](https://arxiv.org/pdf/1007.2927),
Theorem 1.1 and Section 4, treats simple unital Z-stable ASH
coefficients using compact restriction data, and Lemma 4.2 gives
relative positive embeddings with numerical rank gaps in recursive
subhomogeneous settings. We claim no novelty for that method. The
new assertion proved here is order rigidity of the actual
first-factor map for the stated simple pure real-rank-zero
coefficient class over all second-countable locally compact bases.
It is not a proof of STW LXXVI for arbitrary pure C*-algebras.

The root review checked the use of the closure of the equality set,
the uniform spectral gap at its limit points, the actual projection
comparison supplying boundary data, and the exact strict extension.
It also checked the Cu-limit comparison argument, the Hilbert-cube
approximation and the ideal passage for noncompact bases. Proposition
23 of STW was checked in the primary text with precisely the simple,
separable, stably finite and pure coefficient hypotheses. No unresolved
gap was found. This is not external peer review or formal verification.
