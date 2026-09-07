---
rg: 2
id: local-secant-shear-dilation-and-sector-proof
kind: route
title: Telescope local rules and retain the inverse residual in one auxiliary track
target: injective-automata-have-local-stable-secant-dilations
requires:
  - boolean-secants-do-not-supply-operator-left-inverses
---

## Local secants for arbitrary finite-field rules

Choose a finite memory F for tau, enumerate the scalar coordinates of
(k^n)^F, and write its origin rule as f:k^m->k^n. For two local inputs
a,b let p_i use the first i coordinates of b and the remaining coordinates
of a. Define the i-th column of D_f(a,b) by

    (f(p_i)-f(p_(i-1)))/(b_i-a_i),       if b_i!=a_i,
    f(p_i+e_i)-f(p_i),                  if b_i=a_i,

where e_i is the i-th standard basis vector.

In the second case p_i=p_(i-1), so both cases give

    f(p_i)-f(p_(i-1))=column_i(D_f(a,b)) (b_i-a_i).

The finite sum yields D_f(a,b)(b-a)=f(b)-f(a). The unit-increment
convention at equal coordinates agrees with the earlier Boolean
convention when k=F_2. It also ensures that if f is affine-linear,
D_f(a,b) is its actual linear coefficient matrix for every pair a,b.
No derivative or chain rule for nonlinear maps is being asserted.

Use this rule at every g in G with local inputs (x(gs))_(s in F) and
(y(gs))_(s in F). Grouping scalar columns into n-by-n matrices gives

    (P_c z)(g)=sum_(s in F) a_s(g^(-1).c) z(gs),

where every a_s is locally constant on the certificate full shift C.
It follows that P_c(y-x)=tau(y)-tau(x).

Apply the same construction to sigma at the local patterns of tau(x)
and tau(y). These patterns themselves depend on finite patterns of c,
so the resulting Q_c has both finite data memory and finite certificate
memory. The identity sigma tau=id gives

    Q_c(tau(y)-tau(x))=y-x.

Thus P and Q are matrices over the algebraic crossed product
C_lc(C,k) semidirect G, represented by certificate-controlled local
linear operators. Products of such operators remain local: data memory
sets multiply, and only finitely many translates of the coefficient
memory sets are used. This is a uniform finite-memory construction,
not a compactness argument with a certificate-dependent unbounded radius.

## Retaining the residual gives a reversible map

Suppress c in the notation. Starting with (z,w), perform the three local
operations

    (z,w) -> (z,w+Pz)
          -> (z-Q(w+Pz),w+Pz)
          -> (w+Pz,z-Q(w+Pz)).

The first two operations are additive shears, and the third swaps tracks.
Each has an explicit local inverse for arbitrary P and Q. Their product
is U in the claim. Solving

    a=Pz+w,                  b=z-Qa

gives z=Qa+b and w=(I-PQ)a-Pb, exactly V. Hence UV=VU=I without using
QP=I or PQ=I. The calculation is valid over a noncommutative operator
ring; the displayed order of every product matters.

For the certified pair, P h=ell and Q ell=h, so U(h,0)=(ell,0).
Nevertheless the same U is invertible on every possible pair of data
tracks, whether or not those tracks encode an actual execution difference.
Keeping certificates unchanged therefore gives a reversible automaton on
the full product shift.

## The exact condition for clearing all auxiliary data

For an arbitrary z one has

    U(z,0)=(Pz,(I-QP)z).                                (SSD2)

Therefore U(H) is contained in H exactly when QP=I as an operator.
Assume this identity. The restriction of U to H is then P, which is
injective. If PQ=I it is also surjective. Conversely, if P is surjective,
write an arbitrary a as Pz; then PQa=PQPz=Pz=a. Thus U(H)=H if and
only if PQ=I, and strict containment is equivalent to PQ!=I.

For the entire certificate family the forward-containment condition must
hold for every c; a strict range defect needs at least one c with PQ!=I.
The coefficient ring's representation on all certificate-data fibers is
faithful: for a nonzero coefficient at a chosen group element, evaluate
at a certificate where it is nonzero and choose data supported at that
input site to isolate it at the origin. Thus these operator conditions
are also the corresponding exact crossed-product matrix identities.

The earlier reversible three-bit gate demonstrates that genuine inverse
computations do not imply this condition. At c=(000,111), all input
coordinates differ, so the convention above gives the same rank-two P
as in `boolean-secants-do-not-supply-operator-left-inverses`. No Q can
make QP=I. Its certified vector still satisfies QP h=h. Adding the
auxiliary track consequently supplies reversibility without proving
invariance of H.

For linear tau and sigma, in contrast, the unit-increment convention
gives P=tau and Q=sigma independently of c. The original identity
sigma tau=id therefore does imply QP=I, and its reverse defect is
exactly I-PQ. The construction agrees with the known linear reduction;
the unresolved extension is from nonlinear inversion to an operator
identity on all data.

## The nonlinear zero-auxiliary sector

For completeness, define R as in the claim. Put a=tau(x)+z and
b=x-sigma(a). These equations solve uniquely as x=b+sigma(a) and
z=a-tau(b+sigma(a)), proving the stated local inverse. This requires
only the additive group structure of the alphabet and local rules;
neither inverse identity between tau and sigma is needed for R itself.

If sigma tau=id, then R(x,0)=(tau(x),0). In the reverse direction,

    R^(-1)(y,0)=(sigma(y),y-tau(sigma(y))).               (SSD3)

The second component vanishes exactly when y belongs to the image of
tau: one implication writes y=tau(sigma(y)); the other substitutes
y=tau(x) and sigma tau=id. Thus failure of surjectivity appears precisely
as a nonzero inverse auxiliary component on some y.

This proves an exact reversible extension of any already given one-sided
inverse pair. It does not turn a strict embedding of a proper sector into
a strict embedding of the ambient full shift, and it does not manufacture
the source one-sided inverse pair. The linear computation (SSD2) identifies
the stronger operator identity needed to use the group-algebra compiler.
