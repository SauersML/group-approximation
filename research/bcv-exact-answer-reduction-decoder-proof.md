---
rg: 2
id: bcv-exact-answer-reduction-decoder-proof
kind: route
title: Joint-refine the BCV point PVMs and decode every perfect PCP atom
target: bcv-perfect-answer-reduction-decodes-double-cover
requires: []
---

Use the notation of Bowen--Chapman--Vidick,
arXiv:2501.00173, Definition 5.79 and Proposition 5.80. The low-degree
parameters are `d=9`, `m` variables, and a field
`F_q` of characteristic two. The field choice in equation `(210)`
satisfies `72m/q<=1/2`, hence `q>=144m`; the argument below only
needs `q>63m`.

## 1. A zero-loss functional-relation lemma

All measurements used below live in one faithful finite tracial von Neumann
algebra `(M,tau)`. This is the ambient algebra of the strategy, not a
separate algebra chosen for each line. In matrices use normalized trace. If
a tracial presentation is not faithful, first quotient its trace kernel and
restrict to the trace support.

Let `P=(P^a)` and `R=(R^c)` be PVMs in `M`, and let
`e:c |-> a` be a function. If

```text
tau(P^a R^c)=0 whenever a != e(c),                       (EAD1)
```

then

```text
P^a = sum_(c:e(c)=a) R^c.                               (EAD2)
```

Indeed `tau(P^aR^c)=tau(R^cP^aR^c)=||P^aR^c||_2^2`.
Faithfulness kills every forbidden product. Thus
`R^c<=P^(e(c))`, and summing the mutually orthogonal `R^c`'s proves
`(EAD2)`. Perfect line--point consistency is exactly `(EAD1)`, with
`e` evaluation at the incident point. No a priori commutation assertion
is used.

## 2. The actual BCV samplers see all required lines

Fix a complete first-coordinate data packet v=(Player,w), where Player
is A, B, or Oracle. Write `P_(v,p)` for its Point PVM,
`A_(v,L)` for an ALine PVM, and `R_(v,L)` for a DLine PVM.
The fixed-packet support assertion follows from the sampler itself.
Definition 5.79 says that the type graph is the tensor product of
A--Oracle--B and ALine--Point--DLine, both including every self-loop
(page 173, lines 18751--18754), and defines

```text
s_(Player,Space)(z,(u,s,r))
    =(s_Player(z),s_Space(u,s,r)).                       (EAD3a)
```

It then states that the two component edges are sampled independently
(lines 18792--18800). On a Player self-loop, Definition 4.38 feeds the same
seed z to the same map at both ends, so both outputs are the same packet w.
Every packet that is a game vertex has a nonempty finite seed fibre and
therefore positive loop mass. Independently pairing that loop with any
supported low-degree incidence holds v fixed while sampling that incidence.

The Point sampler is BCV equation `(178)`,

```text
s_Point(u,s,r)=(u,0,0).                                  (EAD3)
```

Consequently every `p in F_q^m` is sampled with positive weight.

The axis-line sampler is equation `(179)`,

```text
s_ALine(u,s,r)=(null_(e_(chi(s)))(u),s,0),               (EAD4)
chi(s)=1+(s mod m),                                      (180)
```

so every affine line parallel to every coordinate vector occurs: for
direction `e_i` take `s=i-1` and choose `u` on the desired line.
The inequality `q>63m` in particular ensures that these seed values are
available.

Most importantly, the diagonal-line sampler is BCV equation `(181)`,

```text
s_DLine(u,s,r)
 =(null_(pi_(chi(s)-1)(r))(u),s,pi_(chi(s)-1)(r)).       (EAD5)
```

Equations `(178)--(181)` quantify over every `s in F_q`, so
`s=0` is in the sampler domain. At that value `chi(s)=1`. The paper
defines `pi_i` by zeroing the first i coordinates (lines 18468--18473),
hence `pi_0(r)=r`. Given distinct points `p,p'`, choose
`r=p'-p` and `u=p`. Equation `(EAD5)` then samples a copy of the
affine line through both points and both incidences. Uniform finite seeds
give it positive mass. This is the BCV DLine support statement; it is not
imported from the analogous JNVWY test.

Apply `(EAD2)` to each sampled incidence. For `p in L`,

```text
P_(v,p)^a = sum_(h:h(p)=a) R_(v,L)^h,                   (EAD6)
```

and analogously with `A_(v,L)`. Any two Point PVMs are therefore
coarse-grainings of one DLine PVM and commute. All Point PVMs being finite
and pairwise commuting, they have the joint PVM

```text
E_v(F)=product_(p in F_q^m) P_(v,p)^(F(p)),
       F:F_q^m -> F_q^(k_v).                            (EAD7)
```

Orthogonality and completeness follow by expanding the finite commuting
product. This proves that the products in `(EAD7)` are legitimate inside
one faithful algebra.

## 3. Every supported table is an individual-degree-nine polynomial

Let `L=a+F_q e_i` be an axis line. If `E_v(F) != 0`, then its coarser
line-point product is nonzero. Expanding that product by the ALine version
of `(EAD6)` gives

```text
product_(p in L) P_(v,p)^(F(p))
 = sum_(h: deg h<=9 and h|_L=F|_L) A_(v,L)^h.           (EAD8)
```

Thus `F|_L` is the evaluation table of a degree-at-most-nine univariate
polynomial. Equation `(EAD4)` supplied every axis line, not merely the
sampler's diagonal lines. Since `q>9`, reduced interpolation is unique.
BCV Fact 5.21 now says that each coordinate of `F` is represented by a
unique polynomial of individual degree at most nine. Define

```text
H_v^g=E_v(ev(g))                                        (EAD9)
```

for these polynomial tuples, assigning zero to every unsupported tuple.
Then `H_v` is a global polynomial-table PVM and every Point PVM is its
evaluation marginal.

This also recovers the line PVMs exactly. An ALine label has degree at most
`9`, and a DLine label has degree at most `9m`. The restriction of an
individual-degree-nine polynomial to an arbitrary affine line has degree at
most `9m`. Because `q>63m>9m`, evaluations at all `q` line points
separate the allowed line labels. Combining this injectivity with
`(EAD6)` gives

```text
A_(v,L)=H_v[restriction to L],
R_(v,L)=H_v[restriction to L].                           (EAD10)
```

In particular, the finite-field term in the robust comparison near
Proposition 5.80 equation `(196)` becomes exact equality at zero loss.

## 4. Indifference and the PCP checks hold atom by atom

Answer Reduction check (3) reads the coefficients of an ALine outcome in
every variable declared irrelevant for that polynomial component and
rejects unless all nonconstant coefficients vanish. By `(EAD10)`, a
nonzero atom `H_v^g` is constant on every sampled axis line in each such
coordinate. Equation `(EAD4)` samples all of them, so `g` is independent
of every forbidden coordinate. This is the exact zero-loss version of the
bad-coordinate elimination surrounding equation `(197)`.

For an Oracle packet, the Point proof check is the pointwise form
`(188)--(191)` of PCP equations `(170)--(173)`. Equation `(EAD3)`
samples every verifier point `p` with positive probability, and the
Oracle--Point self-loop is in the product type graph. If a nonzero global
atom `H_(Oracle,z)^Pi` failed one of those equations at some `p`, then
it would lie below the rejected Point-outcome projection at that
positive-weight check. Perfectness gives that projection trace zero and
faithfulness makes it zero, contradicting nonzero `H^Pi`. Hence every
supported `Pi` is a literal degree-nine PCP bundle of the prescribed
variable form and passes every verifier point.

Its PCP acceptance probability is one. Since `q>63m`,

```text
1 > 63m/q.                                               (EAD11)
```

BCV Corollary 5.72 applies separately to every supported atom and says that

```text
Res(g_1^R,g_1^L,g_2^R,g_2^L)                            (EAD12)
```

is an accepted answer quadruple for the source verifier. This is an
atomwise use of the PCP soundness theorem, not a substitution of
`epsilon=0` into the robust bound.

## 5. Exact consistency and inverse wrappers

Suppose an Oracle datum `z` has isolated-player data
`s_A(z)=x` and `s_B(z)=y`. Answer Reduction check (2), at every Point
`p`, tests the A/Oracle or B/Oracle coordinates in the same polynomial
space. Equations `(EAD1)--(EAD2)` give exact Point-PVM identities

```text
P_(A,x,p)=P_(Oracle,z,p)[Restrict_A],
P_(B,y,p)=P_(Oracle,z,p)[Restrict_B].                    (EAD13)
```

Every point identity in `(EAD13)` has positive support: pair the
A--Oracle or B--Oracle first-coordinate edge with the Point self-loop and
use `(178)` for the desired p. Evaluation on all points separates
individual-degree-nine polynomials. More explicitly, uniqueness of the
joint refinement gives, for every player polynomial tuple h,

```text
H_(A,x)^h
 = product_p P_(A,x,p)^(h(p))
 = sum_(Pi: Restrict_A(Pi)(p)=h(p) for every p)
       H_(Oracle,z)^Pi
 = sum_(Pi: Restrict_A(Pi)=h) H_(Oracle,z)^Pi,           (EAD14)
```

and analogously for B. The last equality uses q>9, so two allowed reduced
polynomials agreeing at every point are equal. Thus, as PVM identities,

```text
H_(A,x)=H_(Oracle,z)[Restrict_A],
H_(B,y)=H_(Oracle,z)[Restrict_B].                        (EAD15)
```

Coarse-grain the three PVMs by `Res`. Equation `(EAD12)` says every
nonzero Oracle atom is source-accepted, and `(EAD15)` says its A and B
marginals are exactly the isolated PVMs. These are precisely the
measurements of a perfect strategy for
`Oracle(DoubleCover(V_n))`. Restricting to isolated vertices, as in
Claim 5.46 at error zero, gives a perfect strategy for
`DoubleCover(V_n)`, with no algebra or dimension enlargement.

A general source is recovered from its double cover only with an additional
exact identification:

- Claim 3.54 supplies it when every question has a positive-relative-weight
  synchronization loop; at error zero the plus and minus PVMs agree.
- Remark 3.55 supplies it for a bipartite source by choosing opposite sheets
  on the two sides.

The bipartite alternative applies to the real Answer Reduction input.
Theorem 4.36 produces `H=DeType(Q)` with `Q=QueRed(...)`. In
Definition 4.40 the genuine A and B questions of H occupy disjoint copies;
the only overlapping zero anchor has answer length zero and its incident
tests autoaccept. After inverse purification and padding, select the plus
sheet on the A copy and the minus sheet on the B copy, assigning the trivial
measurement on anchors and ignored dummies. This recovers a perfect H while
retaining every non-anchor generator. Corollary 4.42 at error zero then
restricts H to `DoubleCover(Q)`; because the typed graph of Q has all
self-loops (Figure 14), Corollary 4.43/Claim 3.54 synchronizes the two
copies and returns Q. Fact 5.41 and Fact 4.48 are the exact
value-preserving inverse purification and unpadding operations.

Without either hypothesis, the loopless odd-cycle inequality game shows
that recovery of `V_n` is false: binary edge perfection around an odd
cycle alternately identifies each PVM with the complement of the preceding
one and ends with a projection equal to its complement, while the double
cover is an even cycle and is classically perfect.

## 6. ZPC typing and readable closure

Assume now that the target model is ZPC. Let `q=2^t`, and choose an
`F_2`-linear functional `lambda:F_q->F_2` with `lambda(1)=1`.
Definition 5.17 defines `Res(g)` as literal restriction to the
Boolean subcube. Corollary 5.72 and the assignment condition of Definition
5.25 ensure that the supported g-polynomials take values in
`F_2={0,1}` there. Hence, for a decoded source coordinate `xi` and
its Boolean-subcube point `p_xi`,

```text
Res(g)_xi=g(p_xi) in {0,1} subset F_q.                  (EAD17)
```

The signed observable for `lambda(g(p_xi))` is a product of the target
Point observables for the field-basis bits selected by `lambda`. Products
of signed permutation matrices remain signed permutations. All such Point
observables at a fixed packet commute by `(EAD6)--(EAD7)`, so their joint
spectral PVM is exactly the decoded answer PVM.

The typing is literal. Table 3 places every field bit of an R-labelled
Point value in the readable answer and every field bit of an L-labelled
Point value in the linear answer. If the source coordinate is readable,
`(EAD16)`
uses only the field bits of its `R`-labelled polynomial component; Table 3
marks those target Point bits readable, hence diagonal. If the source
coordinate is structural unreadable, it uses only the corresponding
`L`-labelled target generators. Finally, for a source edge `xy`, choose
its Oracle packet `z`. Equation `(EAD15)` makes the A and B decoded
PVMs coarse-grainings of the single Oracle PVM, so all source answer
variables commute across that edge. Thus the decoded strategy is ZPC.

Inside the common algebra, every decoded readable spectral projection lies
in the target initial readable algebra `D_0(S)`, while every decoded
unreadable generator is a finite word in target unreadable generators. If
a source unreadable word `w` and a decoded readable element `d` have
already been represented, then

```text
w d w^*                                                    (EAD17)
```

is the same conjugation by the corresponding target unreadable word.
Induction on word length and closure under Boolean operations gives the
literal inclusion

```text
D_infinity(Dec(S)) subseteq D_infinity(S).               (EAD18)
```

Sheet selection, isolated-vertex restriction, inverse purification, and
unpadding only discard measurements, so they preserve `(EAD18)`.

This proof is for an attained perfect faithful-tracial model. A sequence of
finite-dimensional strategies with errors tending to zero may first be
placed in a tracial ultraproduct; the same algebraic proof decodes that
perfect limit, but it does not force a finite-dimensional attained source
model.
