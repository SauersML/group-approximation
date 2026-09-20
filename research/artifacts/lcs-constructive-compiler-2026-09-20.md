# A weighted linear-plus-conjugacy compiler with an explicit uniform gap

Date checked: 2026-09-20. This completes a restricted constructive lowering,
not perfect-completeness RE hardness. The missing machine-indexed source
family is identified in Section 7. No computation, build, or MSI job ran.

## 1. Source and target interfaces

Fix k>=1. A weighted linear-plus-conjugacy instance has self-adjoint
involution variables X_1,...,X_n and a probability distribution w with
positive rational weights on two sorts of requirements:

- A linear row r=(i_1,...,i_l;b), with distinct indices, 1<=l<=k,
  requiring its variables to commute and their product to equal (-1)^b I.
- A conjugacy requirement t=(i,j,h), requiring X_i X_j X_i=X_h.

For a tuple of self-adjoint involutions in M_d(C), use normalized
Hilbert--Schmidt norm and define

```
E_r(X) = (1/4)||X_(i_1)...X_(i_l)-(-1)^b I||_2^2
         +(1/4) sum_(a<b) ||[X_(i_a),X_(i_b)]||_2^2,
E_t(X) = (1/4)||X_i X_j X_i-X_h||_2^2,
E(X)   = sum_r w_r E_r(X) + sum_t w_t E_t(X).
```

In E_r, [A,B]=AB-BA is the additive commutator. There is no upper-bound-one
convention for E_r; its pair terms are deliberately summed. Let
e_*=inf_(d,X) E(X). The same infimum is obtained using arbitrary
finite-dimensional tracial algebras: a tracial state is a convex combination
of normalized traces on its simple matrix blocks.

The construction below outputs a finite binary LCS L, of maximum row
width K=max(k,3), with rational row weights. Its constraint-variable game
samples a row by those weights and one variable uniformly in that row.
It has the following properties, with

```
C_k = max(9k^2,14652),
gamma_k(Delta) = (Delta/(148 C_k))^4 / K.
```

1. If e_*=0, then omega_q(L)=omega_qa(L)=1.
2. An exact d-dimensional source solution gives an exact 4d-dimensional
   solution of L (an unused amplification can be omitted).
3. If e_*>=Delta>0, then omega_q(L)<=1-gamma_k(Delta).
4. The explicit finite transformation has polynomial size and running time
   in the explicit weighted source encoding. It uses 22 rows for each
   conjugacy requirement and retains each original linear row.

All constants are independent of n, the number of requirements, minimum
source weight, and matrix dimension. No fixed nonhyperlinear seed enters.

## 2. Primary inputs and attribution

The group gadgets are **William Slofstra**'s restricted embedding machinery,
[arXiv:1703.08618v2](https://arxiv.org/html/1703.08618v2),
Lemma 4.4 and Proposition 4.2. They preserve finite-dimensional and
approximate representations. The weighted bundles and numerical estimates
below are a direct audit of those gadgets, not a claim of new gadget authorship.
The final passage to arbitrary quantum strategies uses **Eric Culf**,
[arXiv:2603.14746v1](https://arxiv.org/html/2603.14746v1),
Corollary 7.3: constraint-variable loss epsilon can be replaced by
finite-dimensional tracial loss at most 148(K epsilon)^(1/4), where K
is maximum context size. Both proofs/theorem interfaces were checked in
the primary HTML on the date above.

This is deliberately a restricted compiler. **Culf--Mastel**'s perfect-gap
BCS source does not already have these word requirements. **Paddock--Slofstra**'s
BCS/solution-group dictionary and **Taller--Vidick**'s imperfect-completeness
hardness retain their original scope. **Liu**'s negative seed and **Thom**'s
conditional normalization machinery are not needed for this lowering.

Repository searches covered `wagon-wheel-stops-before-bcs-groupification`,
`marked-approximate-radical-survives-solution-group-embedding`,
`finite-linear-commutation-system-to-lcs`, the Culf--Mastel source nodes,
the dimension-reported Pauli compilers, nested-conjugacy audits, and the
focused Slofstra audit. Those distinguish the upstream nonlinear-predicate
problem; this argument additionally checks weighted, input-size-independent
soundness for a fully specified word-language lowering.

## 3. The six-row conjugacy block and its exact decoder

For a conjugacy a b a=c where b,c are already required to commute, add
seven private involutions u_1,...,u_7 and the six homogeneous linear rows
on the following triples:

```
(a,u_1,u_2),  (b,u_2,u_3),  (u_3,u_5,u_4),
(a,u_5,u_6),  (c,u_7,u_6),  (u_1,u_4,u_7).
```

Every triple has product I and consists of commuting variables in an exact
LCS solution. The orderings displayed are useful for approximate decoding.
Let e_1,...,e_6 be the norms of these six ordered products minus I in an
arbitrary tuple of self-adjoint involutions. No commutator hypotheses are
needed for the following estimate:

```
||a b a-c||_2 <= e_1+e_2+e_3+e_4+e_5+e_6.                (A)
```

Indeed substitute a~u_1u_2, b~u_2u_3, a~u_5u_6 to obtain
aba~u_1u_3u_5u_6. Then use u_3u_5~u_4, u_1u_4~u_7, and
u_7u_6~c. Unitary invariance and telescoping charge each row once.
This verifies the relevant restriction bound directly.

For completeness, the following two-by-two blocks extend any exact
involution solution a,b,c with aba=c and bc=cb. Original variables become
diag(x,x), and

```
u_1=[0 a; a 0],        u_2=[0 I; I 0],
u_3=[0 b; b 0],        u_4=[0 ba; ab 0],
u_5=diag(bab,a),       u_6=diag(bc,I),
u_7=diag(b,c).
```

Each is an involution. Direct multiplication verifies all six rows; a
product of three involutions equal to I also forces pairwise commutation.
When aba=c holds only approximately but a,b,c are involutions and b,c
commute exactly, all these blocks are still involutions and their row and
commutation defects tend to zero with ||aba-c||_2. The block formulas are
Slofstra's; inequality (A) exposes their weighted decoder in the direction
needed here.

## 4. A 22-row bundle for an arbitrary conjugacy

For each original variable, use auxiliary names y_l,z_l,w_l when required,
and one common new involution f. For a source conjugacy X_i X_j X_i=X_h,
the bundle consists of four linear rows

```
(X_i,f,w_i), (X_j,y_j,z_j), (X_h,y_h,z_h), (g_t,y_j,z_h),
```

all with product I, where g_t is private to this source requirement,
together with six-row blocks for the three nice conjugacies

```
f y_j f=z_j,     f y_h f=z_h,     w_i y_j w_i=z_h.
```

Niceness is supplied respectively by the second, third, and fourth
linear row. Thus there are 4+3*6=22 rows. Rows are labelled occurrences;
identical constraints in different bundles may be kept with separate row
labels, or merged by adding weights. This avoids assumptions on bounded
variable occurrence. Distinct auxiliaries in each six-row block make all
its rows legitimate three-variable LCS rows, including when i,j,h repeat.

The initial normalization extends any source tuple by

```
X_l -> diag(X_l,X_l),     f=[0 I; I 0],
y_l=diag(X_l,I),         z_l=diag(I,X_l),
w_l=[0 X_l; X_l 0],      g_t=y_j z_h.
```

The four linear rows are exact for every tuple of source involutions;
the three nice conjugacies are exact whenever the source conjugacy is.
The two inputs of every nice conjugacy commute exactly even for an
approximate source tuple. Apply Section 3 on one further common doubling.
Consequently all exact source solutions lift in dimension 4d. The same
formulas send vanishing source defects to vanishing output defects,
without choosing a separate dimension factor for each requirement.

Here is the uniform decoder. Let e_i,e_j,e_h be the product defects of
the first three linear rows and let c_t,c_j,c_h be the defects of the
third, first, and second nice conjugacies, respectively. Then

```
||X_i X_j X_i-X_h||_2
  <= 6e_i+e_j+e_h+2c_t+c_j+c_h.                            (B)
```

To check the coefficient 6, the first row gives both
X_i~f w_i and X_i~w_i f, each with error e_i, and hence
||f w_i-w_i f||_2<=2e_i. Substitute the first two and third occurrences
in X_i X_j X_i to get f w_i y_j z_j w_i f, with error 2e_i+e_j.
Split that product as

```
(f w_i y_j w_i f)(f w_i z_j w_i f).
```

The first factor is within c_t+c_h of y_h. Replace z_j by f y_j f in
the second factor, and commute each of its two surrounding f,w_i pairs;
it is within c_j+4e_i+c_t of z_h. Finally y_h z_h is within e_h of X_h.
This proves (B).

Use (A) for each c. The resulting coefficients on the row product defects
are 6,1,1 on three normalization rows, 2 on six rows, and 1 on twelve
rows. Their squared sum is

```
36+1+1+6*4+12=74.
```

The fourth normalization row is needed for completeness but does not have
to be charged by this decoder. Cauchy--Schwarz gives

```
||X_i X_j X_i-X_h||_2^2 <= 74 sum_(r in bundle) e_r^2.       (C)
```

## 5. Weights and finite-tracial loss

Sample each retained source linear row with its original weight w_r.
For a source conjugacy of weight w_t, sample each of its 22 rows with
weight w_t/22. The total row weight is one. After choosing a row, sample
one of its variables uniformly.

Consider a finite-dimensional tracial strategy for this target game.
Write B_v for Bob's involution for variable v, and A_(r,v) for the
commuting involutions derived from Alice's row PVM. Alice's answers are
satisfying assignments, so their product has the exact row parity.
If delta_(r,v) is their mismatch probability, then

```
||B_v-A_(r,v)||_2^2=4 delta_(r,v).
```

Write delta_r for their average over variables of row r. For an ordered
row product of length l,

```
||prod_(v in r) B_v-(-1)^b I||_2^2 <= 4 l^2 delta_r.        (D)
```

For a pair u,v in the row, using the exact commutation of Alice's
observables gives

```
(1/4)||[B_u,B_v]||_2^2 <= 8(delta_(r,u)+delta_(r,v)).        (E)
```

Summing (E) over pairs and adding (D)/4 yields

```
E_r(B) <= (9l^2-8l)delta_r <= 9k^2 delta_r.                 (F)
```

For a conjugacy bundle, all rows have length three, so (C) and (D) give

```
E_t(B) <= (74/4)*36 sum_(r in bundle) delta_r
        =666 sum_(r in bundle) delta_r
        =14652 average_(r in bundle) delta_r.              (G)
```

After summing with the prescribed source weights, (F)--(G) prove

```
E(B_original) <= C_k * loss_tracial(L).                    (H)
```

This is why minimum source weight and total instance size never enter
the bound. The global operator for a source variable is Bob's single B_v;
there is no illicit choice of a different source tuple for each context.

## 6. Arbitrary quantum strategies and perfect completeness

Apply Culf's Corollary 7.3 to any finite-dimensional quantum strategy for
L with loss epsilon. The target has maximum width K, hence a
finite-dimensional tracial strategy exists with loss at most
148(K epsilon)^(1/4). Equation (H) supplies a source tuple (or a convex
combination of matrix tuples) with energy at most

```
148 C_k (K epsilon)^(1/4).
```

If every source matrix tuple has energy at least Delta, the same is true
of that convex combination. Rearranging proves the claimed quantum gap
gamma_k(Delta), uniformly across the entire source family.

For perfect completeness, if e_*=0 choose finite-dimensional involution
tuples with source energy tending to zero. The instance is fixed and all
weights are positive, so every one of its finitely many row, commutation,
and conjugacy defects tends to zero. Section 4 gives target approximate
operator solutions with the same property. Each target context is a fixed
finite abelian involution system; its approximate commuting observables
can be rounded locally, and its parity repaired with error tending to zero.
The local PVMs used by Alice and the original global Bob observables
therefore win with probability tending to one. This is also precisely the
approximate-solution direction proved by Slofstra's Lemmas 3.6--3.8 and
Proposition 3.4. The target thus has value one in qa. No finite-dimensional
attainment is inferred from the mere assumption e_*=0.

When the source tuple is exact, the explicit block extensions are exact,
and Alice's joint spectral measurements together with Bob's variables on
a maximally entangled state give a perfect quantum strategy. There is no
completeness loss in either assertion.

## 7. What is still missing for the RE endpoint

This proves a concrete last-stage theorem: it suffices to produce
machine-indexed bounded-width weighted linear-plus-conjugacy instances
with energy infimum zero on HALT and a single positive energy lower bound
on NONHALT. The theorem above then supplies an explicit constant quantum
gap and binary LCS syntax. For explicit polynomial-time source encodings,
the lowering itself is polynomial time; no claim is made that such source
encodings have been constructed. Succinct verifier access and any exact
three-answer convention also require their own checked interface.

I attempted to fill the input from the three existing candidates:

1. Culf--Mastel's source has genuine forbidden spectral projections.
   Replacing these by involutory conjugacy requirements is not a published
   part of their reduction. The local scalar/odd-tensor obstruction in
   `wagon-wheel-stops-before-bcs-groupification` applies to the naive
   contextwise replacement. No such replacement is assumed here.
2. The Slofstra/Kharlampovich machine construction encodes membership by
   a word c(n)=1 and then uses the tag relation t c(n) t=J c(n).
   That relation kills J when c(n)=1. Thus the proof's word construction
   has perfect approximate completeness on the complementary branch;
   it is not the required HALT-positive family. The accessible HTML of
   Proposition 6.3(c) prints the opposite membership sign, inconsistent
   with the displayed construction and its proof. This audit follows the
   equations, not that sign. It makes no unsupported correction claim
   about the final journal typesetting. Independently, a computable
   family with J!=1 exactly on HALT is impossible because J=1 is r.e.
3. The dimension-reported Pauli compilers activate a dimension obstruction
   on HALT and retain an algebraic model on NONHALT. Their runtime-uniform
   word activation is still an open premise, and even its stated
   orientation is not the desired one. The present lowering does remove
   a final conjugacy-to-LCS syntax concern from a future correctly
   oriented construction; it does not solve activation or same-basis
   consistency.

The terminal theorem is therefore available with explicit constants,
while the substantive machine-to-word source is not. This is progress on
the constructive route without identifying the missing source theorem
with an already solved generic BCS compiler or with the weak constant
qc/qa separator.

## 8. Exact succinct sampling without rational rejection loops

The explicit rational-weight theorem above does not by itself promise a
worst-case polynomial-time exact sampler for arbitrary rational weights.
For the strong root, assume instead a polynomial-time source sampler over
polynomial-length constraint identifiers, together with a polynomial-time
decoder returning the bounded-width requirement and its variable names.
All requirements of positive probability form the finite source instance.

Retain a sampled linear row. For a sampled conjugacy, toss five fair bits:
values 0,...,21 choose the corresponding bundle row; values 22,...,31
repeat rows 0,...,9. Every bundle row has conditional probability at
least 1/32. Equation (G)'s pre-averaging estimate therefore gives

    E_t <= 666 sum_(r in bundle) delta_r
        <= 21312 E_(sampled bundle row)[delta_r].

Let L_0 be the intermediate game with this exactly samplable row
distribution and a uniformly selected variable in each row. Equations
(F)--(G) and Culf's Corollary 7.3 give, with K=max(k,3),

    C'_k=max(9k^2,21312),
    gamma_0=(Delta/(148 C'_k))^4/K.

Thus e_*>=Delta implies omega_q(L_0)<=1-gamma_0, and e_*=0 still
implies omega_q(L_0)=1. At this stage L_0 is only an intermediate game:
exact uniform selection among three positions cannot be implemented with
a worst-case bounded number of fair bits. Biasing the variable selection
would alter the strict LCS-game convention used in
[Taller--Vidick, Section 3.2](https://arxiv.org/html/2507.22444v2).
The following padding preserves that convention instead.

Set P=2^ceil(log2 K), a constant. For each intermediate row r with
1<=l<=K variables, put p=2^ceil(log2 l) and m=p-l. Add m private
variables z_(r,0),...,z_(r,m-1) to its equation, with the same parity.
Also introduce a distinguished identity variable z_*. The final sampler
first samples r as above, then tosses one fair bit:

- With probability 1/2, query the padded equation and a uniformly chosen
  one of its p variables, using log2 p fair bits.
- With probability 1/2, choose j uniformly from 0,...,P-1 using log2 P
  fair bits. If j<m, query the singleton equation z_(r,j)=+1; otherwise
  query the singleton equation z_*=+1. Bob receives its sole variable.

These are ordinary binary LCS rows of power-of-two width at most P,
with Bob uniform within each row. Repeated copies of the identity
singleton may be kept as separate row labels or identified. Both versions
have the displayed sampler and the same argument below.

Here is a direct loss comparison valid for arbitrary finite-dimensional
quantum strategies, without a tracial or synchronous assumption. Fix r
and a strategy for the padded game. Alice's answer to a padded row can
be taken to satisfy its parity: invalid answers always lose and can be
replaced by any valid answer. Let delta_pad be the uniform consistency
loss on that padded row, and delta_z the loss on the singleton z=+1.
To answer r in L_0, Alice simulates her padded-row measurement, discards
the dummy answers, and flips one designated original answer if needed
to satisfy the original parity. Bob keeps his original-variable strategy.

Before that correction the average mismatch on the l original positions
is at most (p/l)delta_pad. A correction is needed only if the product of
the dummy answers is -1. For each dummy z, no-signalling gives

    Pr[A_z=-1] <= Pr[A_z != B_z] + Pr[B_z=-1]
               <= p delta_pad + delta_z.

The last term is the singleton loss because its only valid Alice answer
is +1; Bob's marginal is the same under either Alice question. The union
bound therefore gives the old-row loss estimate

    delta_r <= p(m+1/l)delta_pad + sum_z delta_z
            <= P^2 delta_pad + sum_z delta_z.

The new loss conditional on the initial choice of r is

    epsilon_r=(1/2)delta_pad+(1/(2P))sum_z delta_z
              +((P-m)/(2P))delta_*,

where delta_*>=0 is the identity-singleton loss. Consequently
delta_r<=2P^2 epsilon_r. Averaging with the intermediate row weights
produces one valid strategy for L_0 and proves

    loss(L_0, extracted strategy) <= 2P^2 loss(L_padded, strategy).

Hence the final, exactly samplable strict LCS game has the uniform gap

    gamma=gamma_0/(2P^2)
         =(Delta/(148 C'_k))^4/(2K P^2).

Conversely every L_0 strategy extends by giving all dummy and identity
variables the constant answer +1. Its padded loss is no greater than
its old loss, so value-one completeness is preserved, as is attainment
when an exact strategy was available. No new representation-theoretic
input or rejection sampling is needed for this padding.

Auxiliaries are named using the source variable identifier, or the source
requirement identifier plus a constant-size block/row label; the common f
has one distinguished name. Padding variables add a row identifier and
an index smaller than P, with z_* separately tagged. Questions and all
computation remain polynomial in the machine-code length, and Alice's
answer has at most P bits. A row may occur with several sampling labels;
this does not change its operator identities or positive-probability
support. The decoder and sampler never enumerate the entire source.

Consequently the precise source family in
`lcs-weighted-conjugacy-halting-gap-source` suffices for the strong root.
This family is not constructed here. This section only checks that the
completed lowering preserves the exact efficient-verifier interface.

## 9. Review record

Independent coordinator review on 2026-09-20: PASS for the ordered six-row
telescoping estimate, exact block matrices and approximate niceness,
the normalization bound (B), coefficient-square sum 74, pair coefficient
8 in (E), and 666*22=14652. The reviewer also checked Culf's Corollary 7.3
against the primary source. This is a written proof review, not execution,
formal certification, or a proof of the missing HALT-positive source.

The coordinator also checked the final Section 8 padding argument:
Bob's no-signalling marginals identify the singleton error, the union
bound controls the parity correction, and averaging gives the stated
factor 2P^2 without changing the strict uniform-variable LCS convention.
