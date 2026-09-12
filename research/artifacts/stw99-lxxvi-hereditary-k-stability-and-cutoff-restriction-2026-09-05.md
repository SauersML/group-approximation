# Hereditary K-stability gives strict projection embeddings, but not exact cutoff lifting

Date: 5 September 2026. Internally reviewed theorem and counterexample.
This artifact proves a conditional projection-source extension theorem
without real rank zero, and an explicit failure of exact positive-cutoff
restriction surjectivity. It does not prove the full positive-source
extension theorem under hereditary K-stability.

Review record: the independent root review checked the orbit and
stabilizer description, local polar sections, Michael selection
hypotheses, residual annihilator argument, and CAR conditional
expectation obstruction. No gap was found. The positive result remains
conditional on the stated hereditary K-stability hypothesis.

## 1. Precise hereditary hypothesis and unitary convention

Let D be separable, simple, stably finite, and of stable rank one,
and put B=D tensor K. Assume:

```text
(HK) Every nonzero hereditary C*-subalgebra C of B is K-stable.
```

For any possibly nonunital C, use its forced unitization C^dagger
and write U_1(C) for the kernel of U(C^dagger)->U(mathbb C). Thus U_1(C)
consists of the unitaries with scalar quotient 1. If C is unital,
this group is canonically U(C) in the usual unital convention.

In (HK), K-stability means the actual stabilization maps identify
pi_k U_1(C) with K_(k+1)(C), for every k>=0; the same holds after
matrix amplification. This agrees with the quasi-unitary convention
in Hua, [*K-stability of Z-stable C*-algebras*](https://arxiv.org/pdf/2406.11084),
Definition 4.1 and Theorem 4.2.

No purity assumption is needed in the proof below once stable rank
one and (HK) are assumed. Simple finite pure coefficients supply
stable rank one by the already used coefficient theorem.

## 2. Strict projection-source Stiefel spaces

Let p be a projection in B and d in B_+ with [p]<[d]. Define

```text
E(p,d)={v in closure(dB): v*v=p}.
```

**Theorem.** Under (HK), E(p,d) is nonempty and weakly contractible.
Real rank zero is not required.

For p=0 the space is the singleton {0}. Otherwise projection
comparison gives an actual frame v_0 in E(p,d). Put

```text
C=Her(d),       r=v_0 v_0*,       C_r=(1-r)C(1-r).
```

C_r is a nonzero hereditary subalgebra of C. If it were zero, then
(1-r)d(1-r)=0 and positivity would give d=rdr. Since r belongs to
Her(d), the support of d would be r, and d would be strictly positive
in the unital corner rCr, hence invertible there. This would give
[d]=[r]=[p], contrary to strictness.

The group G=U_1(C) acts on E(p,d) by left multiplication. This action
is transitive. Indeed, for v,w in E(p,d), the partial isometry wv*
belongs to C and has initial and final projections vv* and ww*.
Stable rank one approximates this partial isometry by polar unitaries
u_n such that u_n vv* tends to wv*. The scalar quotient can be
normalized without changing that approximation: if it is lambda_n,
replace u_n by

```text
lambda_n^(-1) u_n (lambda_n vv*+1-vv*).
```

These unitaries lie in U_1(C), and u_n v tends to w. For a sufficiently
close pair of frames, the local polar correction below gives an exact
unitary carrying one frame to the other. This proves transitivity.

The stabilizer of v_0 is exactly U_1(C_r): a unitary fixes v_0 if
and only if its difference from 1 vanishes on both sides of r.
The orbit map has continuous local sections. To give the formula,
let v,w be close frames, with r_v=vv* and r_w=ww*. The polar unitary
of

```text
r_w r_v+(1-r_w)(1-r_v)
```

carries r_v to r_w; denote it by h. Then

```text
k=w(hv)*+(1-r_w),       u=kh
```

is a unitary in U_1(C), depends continuously on w near v, equals 1
at w=v, and satisfies uv=w. Thus

```text
U_1(C_r) -> U_1(C) -> E(p,d)                            (2.1)
```

is a locally trivial principal bundle.

Since C is simple, C_r is full in C. Its inclusion induces an
isomorphism on K-theory. Naturality and (HK) make the left map in
(2.1) a weak homotopy equivalence, including on components. The
long exact sequence of this bundle therefore makes E(p,d) path
connected with all homotopy groups zero. This proves the theorem.

The argument replaces the old projection approximate unit in Her(d)
by an actual homogeneous-space description. The relevant stabilizer
is the nonzero hereditary complement, not a presumed finite-rank
matrix corner.

## 3. Exact relative projection-source selection without real rank zero

Let X be finite-dimensional compact metrizable and Y closed in X.
Suppose p in C(X,B) is a projection and d in C(X,B)_+ is positive,
with [p(x)]<=[d(x)] everywhere and strict inequality outside Y
whenever p(x) is nonzero. Suppose a continuous frame v_Y on Y satisfies

```text
v_Y*v_Y=p|Y,       v_Y(y) in closure(d(y)B).
```

**Corollary.** Under (HK), v_Y extends to a continuous frame v on X
with v*v=p and v(x) in closure(d(x)B). In particular p<=_Cu d.

Here are the selection hypotheses, none of which uses real rank
zero. For close v,w in a fixed E(p,d), normalize the straight line:

```text
z_t=(1-t)v+tw,       H_t=z_t(z_t*z_t)^(-1/2).
```

The inverse is in pBp. For ||v-w|| small this contracts a sufficiently
small sphere of frames in a uniformly controlled larger ball. The
estimate follows from ||z_t*z_t-p||<=2||v-w||+||v-w||^2 and is
independent of p,d and the hereditary algebra. Hence all these frame
spaces, together with singleton fibers, form an equi-LC^n family for
every finite n.

The multifunction x->E(p(x),d(x)) is lower semicontinuous. Given a
frame v_0 at x_0, approximate it by d(x_0)e p(x_0) for a fixed e in B.
Near x_0, normalize d(x)e p(x) in its initial projection corner. This
is a local continuous frame as close to v_0 as desired. The inverse
can equivalently be computed after adding 1-p(x) in the unitization.
If p(x_0)=0, p vanishes near x_0 and the zero frame suffices.

Replace the fibers over Y by the prescribed singletons {v_Y(y)}.
The resulting multifunction remains lower semicontinuous: near Y
combine the preceding local frame construction with continuity of
v_Y, and off Y use closedness of Y. Its fibers are nonempty and
closed. Off Y they are weakly contractible by Section 2, or singleton
when p=0; on Y they are singleton. Michael's finite-dimensional
selection theorem now applies. The precise theorem and a primary
proof are Gutev, [*Constructing selections stepwise over skeletons
of nerves of covers*](https://www.math.bas.bg/serdica/2018/2018-137-154.pdf),
Theorem 1.1.

Finally, the selected frame belongs to closure(d C(X,B)) globally.
An increasing functional-calculus approximate unit e_n(d) converges
pointwise on v. The squared errors v*(1-e_n(d))^2v decrease, so
Dini's theorem on compact X makes convergence uniform. Thus vv*
belongs to Her(d) in the section algebra.

This extends the projection-source input to a strictly broader
coefficient hypothesis. For example Z is not real rank zero, but
all hereditary subalgebras of Z tensor K are Z-stable, hence K-stable.
Hereditary permanence is Toms--Winter,
[*Strongly self-absorbing C*-algebras*](https://arxiv.org/pdf/math/0502211),
Corollary 3.1, and K-stability is Hua's Theorem 4.2 cited above.
This observation does not establish arbitrary positive-source selection.

## 4. Nonzero residual algebras for arbitrary source cutoffs

There is one further non-RR0 fact. Suppose c,d in B_+ satisfy
[c]<[d], and v*v=c with v in closure(dB). For every eta>0, the
hereditary algebra

```text
Ann_Her(d)((vv*-eta)_+)
={x in Her(d): x(vv*-eta)_+=(vv*-eta)_+x=0}
```

is nonzero. If vv* has a nonzero spectral value below eta, a nonzero
positive continuous function of vv* supported in (0,eta) lies in
this annihilator. If it has no such spectral value, its support is
a projection r in Her(d), and [r]=[c]<[d]; the nonzero complement
(1-r)Her(d)(1-r) lies in the annihilator. The case c=0 is immediate.

Under (HK), these residual algebras have the same stabilized unitary
homotopy as Her(d), through their full inclusions. This supplies a
possible way to absorb homotopy obstructions after a source cutoff.
It does not supply an exact extension from one cutoff module to a
larger one. The next example proves that such extension can fail.

## 5. An explicit exact cutoff restriction that is not onto

Take the CAR algebra

```text
A=tensor_(n>=1) M_2,
Delta=tensor_(n>=1) C^2 = C(K),       K={0,1}^N.
```

The tensor diagonal maps on finite tensor products extend to a
conditional expectation E:A->Delta. More explicitly, diagonalize
the first m tensor factors and leave the tail fixed; on each local
tensor element these maps eventually become constant. Contractivity
and density give their point-norm limit E. It fixes Delta and is
Delta-bimodular.

Let e_n be the projection with value 1 in the second diagonal entry
of the nth tensor factor, and put

```text
c=sum_(n>=1) 2^(-n)e_n,
delta=1/4,       epsilon=1/2,
a=(c-delta)_+,       b=(c-epsilon)_+.
```

The series converges in norm. Under Delta=C(K),
c(omega)=sum 2^(-n)omega_n, with range [0,1]. The nonzero projection
e=(1-e_1)(1-e_2) is orthogonal to a, since c<=1/4 on its cylinder.
Therefore

```text
[b] <= [a] <= [1-e] < [1].                              (5.1)
```

Both a and b have spectrum accumulating at zero. We consider actual
right Hilbert A-modules H_a=closure(aA) and H_b=closure(bA), with
H_b contained in H_a. Set

```text
F_a={w in A:w*w=a},       F_b={v in A:v*v=b},
h(t)=sqrt((t-epsilon)_+/(t-delta)_+) for t>delta,
h(t)=0 for t<=delta.
```

Then h is continuous and b^(1/2)=a^(1/2)h(c). A vector w in F_a
encodes the module embedding T_w:H_a->A by

```text
T_w(a^(1/2)x)=wx.
```

Consequently the actual module restriction map is exactly

```text
rho:F_a->F_b,       rho(w)=w h(c).                      (5.2)
```

Define the continuous function

```text
f(t)=sqrt(t-epsilon) exp(i/(t-epsilon))   if t>epsilon,
f(t)=0                                 if t<=epsilon,
```

and let v=f(c). The oscillation is multiplied by a vanishing amplitude,
so f is continuous. We have v*v=b, hence v belongs to F_b.

**Claim.** v is not in the image of rho. In fact no element w of A,
even without the condition w*w=a, can satisfy w h(c)=v.

If such w existed, bimodularity of E would give E(w)h(c)=v. For
omega with c(omega)>epsilon this forces

```text
E(w)(omega)=sqrt(c(omega)-delta) exp(i/(c(omega)-epsilon)). (5.3)
```

Let omega_0=(1,0,0,...), so c(omega_0)=epsilon. Choose binary points
omega_n and omega'_n with

```text
c(omega_n)=epsilon+1/(2 pi n),
c(omega'_n)=epsilon+1/(2 pi n+pi).
```

They can be chosen with first coordinate 1. Their remaining binary
tails have numerical value tending to zero, so both sequences converge
to omega_0 in the product topology: any fixed initial tail coordinate
must eventually be zero. Equation (5.3) has limits respectively

```text
sqrt(epsilon-delta)=1/2,
-sqrt(epsilon-delta)=-1/2.
```

This contradicts continuity of E(w) in C(K). The claim follows.

The same counterexample applies in the stabilization with target
projection 1_A in its fixed corner. If w belongs to 1_A(A tensor K)
and w*w=a in that corner, then w=w1_A, so w actually lies in A.
Additional matrix coordinates cannot remove the expectation obstruction
while keeping this source and target.

## 6. What the counterexample does and does not show

The CAR algebra satisfies (HK): it is Z-stable, and every hereditary
subalgebra of its stabilization is Z-stable by hereditary permanence;
Hua's theorem gives K-stability of all of them. Thus (5.2) fails to be
onto even with stable rank one, real rank zero, strict comparison
against the target projection as in (5.1), and hereditary K-stability.

This does not contradict the established RR0 positive-source theorem.
That proof uses a chosen increasing tower of projection submodules,
whose restrictions have orthogonal hereditary complements. It does not
claim that arbitrary functional-cutoff module restrictions are onto.

Nor does the example refute density of the image of rho, approximate
lifting, or weak contractibility of an individual positive embedding
space. It refutes exactly the proposed use of unrestricted exact
cutoff-restriction lifting to replace the projection tower. A proof
from (HK) for arbitrary positive sources would still need a controlled
approximate lifting or another parameterized construction. No such
full theorem is asserted in this artifact.
