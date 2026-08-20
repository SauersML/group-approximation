# Schur--Clifford predicate rank compiler and multiplicity-pressure attack

**Date:** 2026-08-19  
**Status:** Two exact algebraic theorems proved below; one quantitative obstruction criterion proved; the global return/holonomy transducer remains open. **This is not yet a proof of the existence of a non-hyperlinear group.**

**2026-08-20 Cairn integration update.**  Fixed finite packets flexibly
exactify by normal-form telescoping plus Gowers--Hatami
(`finite-schur-clifford-packet-flexible-hs-exactification`).  A direct
ultraproduct argument strengthens the forbidden-mass lemma to the original
shared approximate selector tuple
(`non-ce-bcs-has-robust-approximate-energy-gap`), so no simultaneous choice of
the context-dependent exactifications is needed.  The global hole is now only
`fixed-scale-contextual-multiplicity-holonomy`, combined by
`multiplicity-return-via-contextual-holonomy`.

The earlier centrality warning was also too strong.  Central selectors in
overlapping context factors impose exactly the context commutations, not
global commutation: the two-edge example is `C_2 x (C_2*C_2)`.  Ordinary
Bass--Serre gluing still fails, but because it is virtually free and admits
stationary representation-type flows, not because it classicalizes every
selector.

There is also a fixed-scale reformulation of the surplus.  For an exact
packet representation, let `R_A` and `R_B` average the adjoint action of the
nested finite groups.  Forbidden Hilbert mass `q` forces

```text
rank(R_A-R_B)/d^2 >= 3 q^2/(4 D^2 K),
```

where `D=2^N` is the baseline spin dimension and `K` is the number of
forbidden assignments.  This is
`predicate-rank-jump-forces-adjoint-reynolds-gap`.  It replaces a fragile
integer-copy selection by an explicit positive-density projection which is
ready for scaled Kazhdan transport.

There is a necessary covariance warning.  Merely placing `A_f` in the
commutant of a Kazhdan group and `B_f` in the commutant of its compressed copy
does nothing: the compressor representation and a forbidden packet can live
on separate tensor factors, with perfect transport and the full Reynolds gap.
This is `packet-kazhdan-commutant-placement-decouples`.
The narrowed open interface is
`compressor-covariant-packet-reynolds-return`: a named relation must make the
Reynolds-difference range an actual coefficient of the compressor orbit.

The Schur complement in fact supplies a canonical coefficient frame.  On
every selector sector there are explicit products `P_x,Q_x` of packet
generators which commute with the leading packet and whose mutual commutator
is `(-1)^{f(x)}`.  Central Fourier control produces three fixed coefficients
`P_f,Q_f,P_fQ_f`; on every forbidden simple block their right module over the
packet commutant is exactly `(M_2 minus C I_2) tensor M_m`, of dimension
`3m^2`.  Thus the extensive Reynolds defect does not require selecting an
adjoint basis vector.  A finite overgroup cannot make the nonlinear
controlled commutator universally sound: induction from the enlarged center
forces wrong-phase irreducibles unless `f` is affine.  The remaining
covariance mechanism must therefore be genuinely infinite or tracial, not a
larger finite selector packet.

For a family of commuting return letters, all remaining gauge freedom can be
computed exactly.  If the packet implementers have binary projective
commutator matrix of rank `2r`, Schur's lemma moves the opposite cocycle to
the external multiplicity space, which must then be a module over
`M_(2^r)(C)`.  Hence `2^r` divides the multiplicity.  This identifies the
precise supercritical target: the infinite compressor/self-simulation must
activate cocycle rank `2r` with `r` larger than the logarithm of the
multiplicity in the same candidate model.  Any fixed rank remains dilutable.

Nor can the spurious finite-overgroup sectors be hidden at small Plancherel
weight.  The regular representation of any finite overgroup restricts to the
selector--phase subgroup as a uniform multiple of its regular
representation.  Unless the phase is an affine selector word, each selector
character has equal positive- and negative-phase mass, so the nonlinear law
is wrong on exactly one half of the regular packet.  This removes finite
regular normalization as a possible shortcut around the infinite return
mechanism.

There is nevertheless a group-native replacement for the additive
controlled coefficients.  Between `A_f` and `B_f` sit the two actual finite
subgroups obtained by adjoining only the final `p` generator or only the
final `q` generator.  Each is a binary refinement of the baseline packet.  On
allowed sectors the refinements commute; on forbidden sectors they are the
`Z`- and `X`-MASAs of the relative Pauli qubit.  Their centered commutant
modules are orthogonal copies of `M_m`, and simultaneous return to one
carrier obeys the sharp conditional-expectation inequality `(SPS4)`.  This
replaces nonlinear finite groupification by a concrete two-dimensional
inclusion square; the remaining open cell is to make a one-sided compressor
return the two child modules with uniform HS cost.

The required local two-cell is explicit.  Multiplying the final `p` generator
by `J` and, independently, the final `q` generator by `J` defines two
commuting involutive automorphisms of the finite packet.  On a forbidden
simple their implementers are the opposite corrected Pauli operators
`Q_x,P_x`, hence anticommute; on an allowed sector they simply permute the
four compatible child characters.  Adjoining commuting stable letters for
these automorphisms forces even external multiplicity on every forbidden
simple.  The global hole has consequently narrowed again: a finite
self-similar compressor must replicate this explicit flip square into
independent returned directions until their cocycle rank exceeds the current
multiplicity, with loss independent of recursion depth.

The exact recurrence can be made depth one.  Put the finite flip-square group
at every site of the Kun--Thom coset action.  A strict positive compressor
gains infinitely many `Gamma`-fixed sites in one step; in the Bernoulli tensor
model each gained site contributes an independent forbidden packet cocycle,
so any `n` selected sites have binary rank `2n`.  This gives exact tracial
completeness with arbitrary rank and no long compressor words.  The remaining
soundness theorem is now coordinate recovery: a matrix microstate must expose
more than `log_2 m` of those new site factors, chosen at its own multiplicity
scale, with total HS loss independent of the number selected.

There is a sharp limitation to this plan.  The exact truncation containing
`n` independent flip squares uses `n` Pauli cancellation qubits, so its
external multiplicity is `m=2^nL` after arbitrary spectator amplification.
It satisfies every relation in that finite window while `n<=log_2 m`.
Therefore infinite compressor index, ultraproduct recovery of every fixed
number of sites, and scaled Kazhdan transport cannot by themselves cross the
capacity threshold.  A final compiler must react to the residual spectator
multiplicity and activate more cells inside that same model—the literal
dimension-diagonal/self-detecting step.

The residual spectator is not merely bookkeeping.  The old `n` Pauli
cancellation pairs generate `M_(2^n)(C)` on the multiplicity space, so their
commutant is exactly `M_L(C)`.  Additional independent cells must act in this
residual factor and force `2^r|L`.  Hence the sharp diagonal task is to inspect
that commutant and request `r>log_2L` new cells; the already paid rank cancels
from both sides of the capacity inequality.

There is a genuinely different escape from dimension detection.  If a finite
bi-index action can be rounded uniformly, one base lamp and finitely many
pair-orbit relators produce a coherent *infinite* family of anticommuting
matrices inside the same candidate model.  Such a family cannot exist in any
finite `M_d`: compactness gives two members converging to the same unitary,
whose anticommutator tends to norm two.  This route pays no logarithmic rank
threshold at all.  Its entire missing input is uniform HS site coherence for
an explicit infinite finite-bi-index subgroup pair; finite pair-orbit type by
itself does not control approximate coset representatives.

A concrete exact holonomy primitive is now available.  If two commuting
automorphisms of a finite packet have projective implementer commutator
`zeta` of order `r` on an irreducible packet, adjoining commuting stable
letters forces `r` to divide its external multiplicity.  This is
`commuting-automorphism-cocycle-forces-multiplicity`.  It is the literal
two-cell version of multiplicity pressure, but a fixed `r` still dilutes by
repairing `O(r)` copies inside multiplicity `m`; self-similarity or a
same-model dimension trigger must make the pressure extensive.

## 0. Executive statement

There is a loophole in the repo's affine-selector no-go results.

A finite group gadget cannot remove an arbitrary nonlinear joint character of a commuting Boolean selector subgroup.  But it can make the **matrix size of the irreducible packet above that character depend nonlinearly on the character**.

More precisely, for every Boolean predicate

\[
f:\{0,1\}^k\to\{0,1\},
\]

one can effectively build a finite class-two 2-group packet with Boolean selectors \(z_1,\dots,z_k\), a central sign \(J\), and two nested finite packet groups

\[
A_f\le B_f,
\]

such that on the sector

\[
J=-1,\qquad z_i=(-1)^{x_i},
\]

the algebra of \(A_f\) is always one full matrix algebra \(M_{2^N}(\mathbf C)\), while every irreducible \(B_f\)-module has dimension

\[
2^{N+f(x)}.
\]

Equivalently, every irreducible \(B_f\)-module restricts to \(A_f\) as

\[
2^{f(x)}
\]

copies of the unique \(A_f\)-spin module.  A violating assignment can therefore be made to create **one extra Clifford multiplicity bit**.

For AND this is already the 2-by-2 affine matrix

\[
M_\wedge(x,y)=
\begin{pmatrix}
1&x\\
y&0
\end{pmatrix},
\qquad
\operatorname{rank}_{\mathbf F_2}M_\wedge(x,y)=1+xy.
\]

So, literally: **AND = one extra Pauli qubit.**

The remaining global task is no longer “compile a nonlinear predicate into group relations.”  It is:

> **Return-transducer problem.** Build a finite group-theoretic transport/holonomy mechanism which compares the packet multiplicity before and after these rank gates on a positive-density marked carrier, with any mismatch charged in normalized Hilbert--Schmidt energy.

That target is closely aligned with the repo's semisimple-packet multiplicity route and with its supercritical branching/holonomy routes.

---

## 1. Why this does not contradict the selector no-go

The repo proves in `research/finite-selector-gadget-induction-barrier.md` that if a finite group \(H\) contains an abelian selector subgroup \(D\), every character of \(D\) compatible with the marked central phase occurs in some finite-dimensional representation of \(H\).  Hence a finite gadget cannot keep, say, one-hot selector characters while deleting three-hot characters.

The construction below **does not delete any selector character**.  Every assignment survives.  What changes is the dimension/multiplicity of the nonabelian packet over that assignment.

This is also compatible with `notes/TRUE_AUGMENTATION_ZERO_HECKE_GATE.md`: a scalar central phase is too coarse for nonlinear *spectral selection*.  The present construction uses the scalar phase only to select a Clifford spin sector; the nonlinear datum is the rank of the commutation form.

Thus the mechanism leaves the induction theorem untouched and moves the nonlinearity into representation multiplicity.

---

## 2. The affine-rank theorem

### Theorem 2.1 (Boolean predicate as a one-rank jump)

For every Boolean predicate \(f:\{0,1\}^k\to\{0,1\}\), there is an effectively constructible square matrix

\[
M_f(x)\in M_{N+1}(\mathbf F_2)
\]

whose entries are affine-linear forms in \(x_1,\dots,x_k\), and such that for every Boolean assignment \(x\),

\[
\operatorname{rank}_{\mathbf F_2} M_f(x)=N+f(x).
\tag{2.1}
\]

Moreover, the upper-left \(N\times N\) block \(U_f(x)\) can be chosen invertible for every \(x\).

### Proof

Write the Boolean indicator of an assignment \(a\in\{0,1\}^k\) as

\[
\delta_a(x)=\prod_{i=1}^k \ell_{a_i}(x_i),
\qquad
\ell_1(x_i)=x_i,\quad \ell_0(x_i)=1+x_i,
\]

with arithmetic in \(\mathbf F_2\).  On the Boolean cube, \(\delta_a(x)=1\) exactly when \(x=a\).  Hence

\[
f(x)=\sum_{a:f(a)=1}\delta_a(x).
\tag{2.2}
\]

Build a directed acyclic algebraic branching program with source \(s\), sink \(t\), and one internally vertex-disjoint \(s\)-to-\(t\) path for each satisfying assignment \(a\).  Label the \(i\)-th edge of that path by \(\ell_{a_i}(x_i)\).  The path-sum of the branching program is exactly (2.2).

Order the vertices topologically and let \(N_f(x)\) be the weighted adjacency matrix.  It is strictly upper triangular.  Put

\[
U_f(x)=I+N_f(x).
\]

Over \(\mathbf F_2\), plus and minus coincide.  Since \(N_f\) is nilpotent,

\[
U_f(x)^{-1}=I+N_f(x)+N_f(x)^2+\cdots.
\]

The \((s,t)\)-entry of this inverse is the sum of the weights of all directed \(s\)-to-\(t\) paths, hence

\[
e_s^T U_f(x)^{-1}e_t=f(x).
\tag{2.3}
\]

Now define

\[
M_f(x)=
\begin{pmatrix}
U_f(x)&e_t\\
e_s^T&0
\end{pmatrix}.
\tag{2.4}
\]

The block \(U_f(x)\) is invertible for every \(x\), so the Schur-complement rank formula gives

\[
\operatorname{rank}M_f(x)
=N+\operatorname{rank}\bigl(e_s^TU_f(x)^{-1}e_t\bigr)
=N+f(x).
\]

This proves (2.1).  \(\square\)

### Remarks

1. The ABP-to-affine-determinant linearization is classical in algebraic complexity (Valiant-type determinant universality).  What matters here is the particular **rank-normalized** form (2.4): the leading block is invertible on every Boolean assignment, so the predicate is exactly one extra rank.
2. The construction can be extremely small for concrete predicates.  For AND, the displayed 2-by-2 matrix suffices.
3. `experiments/schur_clifford_rank_gate.py` verifies the construction exhaustively for every Boolean predicate of arity at most three.

---

## 3. Turn affine rank into a finite 2-group packet

Let \(M(x)=(m_{ij}(x))_{1\le i,j\le m}\) be an affine matrix over \(\mathbf F_2\), with

\[
m_{ij}(x)=c_{ij}+\sum_{\ell=1}^k a_{ij\ell}x_\ell.
\]

Define a finite class-two 2-group \(K(M)\) generated by

\[
J,z_1,\dots,z_k,p_1,\dots,p_m,q_1,\dots,q_m
\]

with the following relations:

- \(J,z_1,\dots,z_k\) are central involutions;
- all \(p_i\) are involutions and commute with one another;
- all \(q_j\) are involutions and commute with one another;
- \(p_i,q_j\) commute with every \(z_\ell\) and with \(J\);
- and

\[
[p_i,q_j]
=J^{c_{ij}}\prod_{\ell=1}^k z_\ell^{a_{ij\ell}}.
\tag{3.1}
\]

This presentation is consistent and finite: one can realize it explicitly as a central extension of \(\mathbf F_2^{2m}\) by \(\mathbf F_2^{k+1}\), with cocycle determined by the coefficient vectors of the entries of \(M\).

Fix a central character

\[
J\mapsto-1,
\qquad
z_\ell\mapsto(-1)^{x_\ell}.
\tag{3.2}
\]

Then (3.1) becomes

\[
P_iQ_j=(-1)^{m_{ij}(x)}Q_jP_i.
\tag{3.3}
\]

### Theorem 3.1 (Clifford rank = representation dimension)

Let \(r=\operatorname{rank}_{\mathbf F_2}M(x)\).  Every irreducible complex representation of the sector (3.2) has dimension

\[
2^r.
\tag{3.4}
\]

More precisely, the sector algebra is

\[
M_{2^r}(\mathbf C)\otimes
\mathbf C[(C_2)^{2(m-r)}],
\tag{3.5}
\]

and therefore is a direct sum of \(2^{2(m-r)}\) copies of \(M_{2^r}(\mathbf C)\).

### Proof

Choose \(R,C\in GL_m(\mathbf F_2)\) such that

\[
R M(x) C=\operatorname{diag}(I_r,0).
\]

Replacing the commuting \(p\)-generators by products according to \(R\), and the commuting \(q\)-generators by products according to \(C\), performs exactly these row and column operations without changing the sector algebra.

The first \(r\) pairs then satisfy the standard Pauli relations

\[
P_iQ_i=-Q_iP_i,
\]

and commute across distinct indices.  Each such pair generates \(M_2(\mathbf C)\).  The remaining \(2(m-r)\) generators commute with everything in the sector and generate the abelian algebra \(\mathbf C[(C_2)^{2(m-r)}]\).  Tensoring gives (3.5), hence every simple block has dimension \(2^r\).  \(\square\)

This is the standard extraspecial/finite-Heisenberg phenomenon, but now the rank of the commutation form is an affine-matrix computation in the selector bits.

---

## 4. The stronger object: a predicate-dependent restriction multiplicity

Apply Theorem 3.1 to the matrix (2.4).  Let \(B_f=K(M_f)\).  Let \(A_f\le B_f\) be the subgroup generated by the same central selectors and sign together with the \(p_i,q_j\) belonging to the upper-left block \(U_f\).

Since \(U_f(x)\) is invertible for every Boolean \(x\), the fixed central-character sector of \(A_f\) is always

\[
M_{2^N}(\mathbf C),
\tag{4.1}
\]

so it has a unique simple module \(S_x\), of dimension \(2^N\).

The full \(B_f\)-sector has rank \(N+f(x)\).

### Theorem 4.1 (predicate branching inclusion)

For every assignment \(x\) and every irreducible \(B_f\)-module \(T\) in the sector (3.2),

\[
T\!\downarrow_{A_f}
\cong S_x^{\oplus 2^{f(x)}}.
\tag{4.2}
\]

Thus:

- if \(f(x)=0\), one \(B_f\)-simple restricts to one copy of the baseline spin packet;
- if \(f(x)=1\), one \(B_f\)-simple restricts to **two** copies of the baseline spin packet.

### Proof

By Theorem 3.1,

\[
\dim S_x=2^N,
\qquad
\dim T=2^{N+f(x)}.
\]

The algebra in (4.1) is a full matrix algebra, so every finite-dimensional \(A_f\)-module in the fixed central-character sector is a direct sum of copies of its unique simple module \(S_x\).  Dimension therefore forces exactly \(2^{f(x)}\) copies.  \(\square\)

### Multiplicity form

If a finite-dimensional \(B_f\)-representation has, over assignment \(x\), total irreducible multiplicity \(m_B(x)\), then after restricting to \(A_f\) the multiplicity of \(S_x\) is

\[
m_A(x)=2^{f(x)}m_B(x).
\tag{4.3}
\]

Hence for a violation bit \(f\),

\[
\sum_x m_A(x)
=
\sum_x m_B(x)+\sum_{x:f(x)=1}m_B(x).
\tag{4.4}
\]

A positive density of violating packet copies therefore creates a positive **multiplicity surplus**.

Important: (4.4) is a multiplicity statement, not a Hilbert-dimension expansion.  Hilbert dimension is conserved because a violating \(B_f\)-simple is twice as large.  The global attack must therefore compare multiplicity on a common fixed packet scale, exactly as in the repo's `semisimple-packet-multiplicity-collapse.md`.

---

## 5. What this buys against the affine/AND barrier

The repo's dead-end was:

> arbitrary BCS predicates cannot be enforced by scalar group words on commuting Boolean selectors, because scalar support constraints are affine.

The rank compiler changes the target:

> do not ask the group to make the bad assignment impossible; ask the bad assignment to change the module type by a discrete factor of two.

This is strictly outside the affine-support argument.  The Boolean nonlinearity appears in

\[
x\longmapsto \operatorname{rank}_{\mathbf F_2}M_f(x),
\]

not in a set of allowed characters.

There is also no need for a universal nonlinear selector group: each fixed BCS context receives its own finite class-two packet, while the actual BCS variable involutions can be shared across contexts.  Only variables in a common context are required to commute.

---

## 6. The quantitative endpoint does not actually need integer index theory

The repo's marked spectral-density lemma says that if a marked unitary word \(W\) satisfies

\[
\|W-I\|_2\ge \alpha,
\]

then for \(0<\theta<1\), the spectral carrier

\[
Q_\theta=1_{\{|W-I|\ge\theta\alpha\}}
\]

has

\[
\tau(Q_\theta)
\ge
\frac{\alpha^2(1-\theta^2)}{4-\theta^2\alpha^2}.
\tag{6.1}
\]

Suppose a compiler produces nonnegative local violation masses \(q_j\) satisfying

\[
\sum_jq_j\ge \gamma\tau(Q_\theta),
\tag{6.2}
\]

and local payment inequalities

\[
q_j\le L\sum_{r\in N(j)}\|r(U)-I\|_2^2,
\tag{6.3}
\]

with each relator appearing in at most \(D\) neighborhoods.  Then bounded-overlap summation gives

\[
\sum_r\|r(U)-I\|_2^2
\ge
\frac{\gamma}{LD}
\frac{\alpha^2(1-\theta^2)}{4-\theta^2\alpha^2}.
\tag{6.4}
\]

So the logical endpoint needs only:

1. positive marked carrier mass;
2. positive local violation mass on that carrier;
3. local Hilbert--Schmidt payment;
4. bounded overlap.

Integrality/index language is one way to manufacture the local mass, but not a logical requirement of the final contradiction.  The Schur--Clifford packet gives a new candidate local mass: **multiplicity surplus caused by a nonlinear predicate**.

---

## 7. Sparse algebraic certificates pay normalized-HS energy

A convenient payment mechanism is a sparse decomposition in the relator ideal.  Suppose

\[
A_j(U)=\sum_{a=1}^M \lambda_a V_a(U)(r_a(U)-I)W_a(U),
\]

where \(V_a,W_a\) are contractions and \(|\lambda_a|\le 1\).  Then

\[
\|A_j(U)\|_2
\le \sum_a\|r_a(U)-I\|_2,
\]

and Cauchy--Schwarz yields

\[
\|A_j(U)\|_2^2
\le M\sum_a\|r_a(U)-I\|_2^2.
\tag{7.1}
\]

Thus any local multiplicity mismatch whose Hilbert mass is bounded by \(c\|A_j(U)\|_2^2\) automatically has the form (6.3).

This is structurally similar to the quantitative relation decompositions in Fanizza--Kroell--Mehta--Paddock--Rochette--Slofstra--Zhao (arXiv:2510.04943), where a distinguished projection \(D\) on one side of the Turing-machine construction satisfies a signal-collapse estimate \(\varphi(D)\le C_m\varepsilon\).

---

## 8. Contractive computation: “destroy faster than approximation helps”

The user's proposed Turing-machine principle can be stated abstractly without any group-specific machinery.

### Theorem 8.1 (contractive computation ladder)

Let \(a_n\ge0\) be uniformly bounded.  Suppose

\[
a_n\le \lambda a_{n+1}+C p(n)\sqrt E,
\qquad 0<\lambda<1,
\tag{8.1}
\]

where \(p\) is a fixed polynomial and \(E\) is a global normalized-HS relator energy.  Then

\[
a_0\le C\sqrt E\sum_{n\ge0}\lambda^np(n).
\tag{8.2}
\]

In particular, if \(a_0\ge a_*>0\) is forced by marked separation, then

\[
E\ge
\frac{a_*^2}
{C^2\bigl(\sum_{n\ge0}\lambda^np(n)\bigr)^2}>0.
\tag{8.3}
\]

### Proof

Iterate (8.1) to depth \(N\):

\[
a_0\le \lambda^Na_N+C\sqrt E\sum_{n=0}^{N-1}\lambda^np(n).
\]

The first term tends to zero because \(a_N\) is bounded, and the series converges because exponential decay beats every fixed polynomial.  This gives (8.2), hence (8.3).  \(\square\)

### Variable-density version

If a contraction factor \(\lambda<1\) occurs only on a set of levels of lower density \(\eta>0\), while the other levels have factor one, then the product of transfer factors is at most \(\lambda^{\eta n+o(n)}\).  Polynomially growing certificate costs are still summable.  Thus no single relation needs to carry large error: **a positive density of interdependent contraction events suffices.**

This is the precise “destroy faster than approximation helps” architecture.

---

## 9. A fixed non-CE BCS already has a dimension-free forbidden-mass gap

The rank compiler becomes more useful when paired with a compactness fact that does not require any PCP theorem.

### Theorem 9.1 (finite-dimensional forbidden-mass gap)

Let \(\mathcal B\) be a finite BCS with variables \(X\), contexts \(c\), and forbidden assignment sets \(F_c\).  Assume its BCS algebra has a tracial state, but **no Connes-embeddable tracial state**.  Then there is a constant \(\beta_{\mathcal B}>0\) such that for every finite-dimensional tuple of self-adjoint involutions \((Z_x)_{x\in X}\) for which the variables in each context commute exactly,

\[
\sum_c\sum_{a\in F_c}
\tau_d\!\left(
\prod_{x\in U_c}\frac{I+(-1)^{a_x}Z_x}{2}
\right)
\ge \beta_{\mathcal B}.
\tag{9.1}
\]

The terms in (9.1) are traces of genuine joint spectral projections, so the left side is exactly total forbidden-assignment mass.

### Proof

If no such \(\beta_{\mathcal B}\) existed, there would be dimensions \(d_n\) and exact contextwise commuting involution tuples \(Z^{(n)}\) for which the left side tends to zero.  Pass to the tracial matrix ultraproduct

\[
\prod_{\omega}(M_{d_n}(\mathbf C),\tau_{d_n}).
\]

The classes \(Z_x=[Z_x^{(n)}]_\omega\) remain self-adjoint involutions and commute in every context.  Each forbidden atom has nonnegative trace tending to zero, hence has ultraproduct trace zero.  Since it is a projection, its \(2\)-norm is zero and therefore the projection itself vanishes in the tracial ultraproduct.  The tuple thus gives a unital representation of the BCS algebra into a tracial matrix ultraproduct.  Composing with the ultraproduct trace gives a Connes-embeddable tracial state, contradicting the hypothesis.  \(\square\)

This theorem is the cleanest form of “failure cannot be diluted away” available from a fixed non-CE BCS: even if no single constraint is responsible, the **sum** of forbidden spectral mass is uniformly positive in every finite-dimensional model.

### Corollary 9.2 (forbidden mass becomes extensive multiplicity surplus)

Attach to context \(c\) the Schur--Clifford packet for the violation predicate

\[
f_c(a)=1_{\{a\in F_c\}}.
\]

Let its baseline rank be \(N_c\).  In an exact finite-dimensional realization of the packet, write \(q_c\) for the Hilbert-space mass of the forbidden selector sectors and \(s_c\) for the restriction-multiplicity surplus

\[
s_c=\sum_{a\in F_c}m_{B_c}(a).
\]

Every forbidden \(B_c\)-simple has dimension \(2^{N_c+1}\), so

\[
\frac{s_c}{d}=\frac{q_c}{2^{N_c+1}}.
\tag{9.2}
\]

Consequently, if the shared selector tuple realizes the same context spectral masses as in (9.1), then

\[
\frac1d\sum_c s_c
\ge
\frac{\beta_{\mathcal B}}{2^{1+N_{\max}}},
\qquad
N_{\max}=\max_cN_c.
\tag{9.3}
\]

Thus the non-CE BCS gap plus the rank compiler creates an **\(\Omega(d)\) integer multiplicity defect**.  The normalized-HS problem has been reduced to making a global return relation pay for that extensive defect.

---

## 10. The new synthesis: predicate rank gates + recurrence

The strongest route suggested by the compiler is the following.

Take one fixed finite BCS algebra with a tracial state but no Connes-embeddable tracial state.  Such a finite system has a uniform finite-dimensional soundness gap: otherwise a sequence of finite-dimensional strategies with total error tending to zero would yield a Connes-embeddable tracial state in a tracial ultraproduct.

For every context predicate \(f_c\):

1. attach the finite inclusion \(A_{f_c}\le B_{f_c}\);
2. exactify the finite packet inside a candidate HS microstate;
3. interpret a violating context assignment as the multiplicity doubling (4.2);
4. transport the resulting fixed-spin multiplicity through a finite recurrent packet network;
5. use the BCS soundness gap to force a positive density of doubling events on any positive marked carrier;
6. use a return/holonomy relation to compare the multiplicity after a cycle with the original multiplicity;
7. charge the unavoidable mismatch to normalized-HS relator energy.

In schematic form:

```text
marked separation
      |
      v
positive-density spectral carrier
      |
      v
finite packet exactification
      |
      v
BCS context assignment on packet copies
      |
      +---- satisfying ---- multiplicity x1 ----+
      |                                         |
      +---- violating ----- multiplicity x2 ----+--> recurrent return
                                                    |
                                                    v
                                           multiplicity curvature
                                                    |
                                                    v
                                            HS relator energy
```

This is a multiplicity analogue of the repo's Pauli Perron--Frobenius branching route.

---

## 11. Exact remaining theorem: the multiplicity-return transducer

The rank gate is not enough by itself.  Direct sums let a finite-dimensional approximator absorb any *absolute* divisibility requirement by increasing dimension.  Also, a finite graph of finite groups cannot be the final answer: it is virtually free/hyperlinear, and its regular finite-dimensional models provide stationary representation-ring flows.

The missing statement must therefore be genuinely global.

### Target 11.1 (multiplicity-return transducer)

Construct a finitely presented group \(\Gamma\), a marked word \(w\), finitely many Schur--Clifford context packets, and a finite recurrent transport network with the following property.

For every sufficiently accurate finite-dimensional normalized-HS microstate \(U\) of \(\Gamma\) in which \(w\) stays \(\alpha\)-separated from the identity:

1. a fixed positive fraction of the marked spectral carrier exactifies into the baseline spin packet types;
2. the packet multiplicity vectors can be transported around the finite network with total transport defect bounded by \(C E(U)\);
3. the fixed non-CE BCS soundness gap forces a positive fraction of transported packet copies to traverse rank-jump edges;
4. after one return cycle, those jumps create a multiplicity surplus of at least \(\eta d\) on a packet of fixed matrix size;
5. the return relation identifies source and target packet types, so at least \(c\eta d\) Hilbert dimension must lie in the transport defect.

Then

\[
E(U)\ge \varepsilon_0(\alpha)>0,
\]

and \(\Gamma\) is nonhyperlinear.

The key phrase in (4) is **fixed matrix size**.  Once the packet irreducible dimension is uniformly bounded, an extensive multiplicity mismatch is an extensive Hilbert-space mismatch and is visible to normalized HS norm.

---

## 12. Why ordinary graph-of-finite-groups gluing cannot be the return transducer

The local inclusions \(A_f\le B_f\) are finite, so one may be tempted to connect them by Bass--Serre edges.  This cannot finish the proof.

A finite graph of finite groups has virtually free fundamental group, hence is residually finite, sofic and hyperlinear.  Representation-theoretically, the dimension vector gives a positive stationary solution of the edge restriction equations; any apparent supercritical multiplicity component must leak into complementary types.

Therefore the return mechanism must use at least one of:

- a genuinely two-dimensional holonomy relation/complex of groups;
- a nonamenable coefficient/edge together with quantitative HS rigidity;
- a compressor/self-similar group in which multiplicity transport is not merely Bass--Serre restriction;
- a signed-Hecke/projection atlas followed by a groupification theorem.

This matches the repo's existing conclusion that one-dimensional finite-gadget gluing is too weak.

---

## 13. Relation to the repo's signed-Hecke route

The signed-Hecke compiler and the Schur--Clifford rank compiler solve complementary halves of the problem.

### Signed-Hecke route

- arbitrary predicate support is exact inside a higher-dimensional finite representation block;
- the remaining difficulty is a compatible global projection atlas.

### Schur--Clifford route

- no predicate support is deleted;
- every assignment remains, but violation changes a discrete packet multiplicity by a factor of two;
- the remaining difficulty is a global multiplicity-return/holonomy atlas.

The second route may fit the existing Kazhdan/semisimple infrastructure better because the repo already has scale-free transport theorems for multiplicity defects (`scaled-kazhdan-transport`, `kazhdan-tensor-type-transport`).

A concrete next attack is therefore to replace the generic semisimple packet in `semisimple-packet-multiplicity-collapse.md` by these explicit class-two 2-group packets, whose block structure and conditional expectations are completely computable.

---

## 14. A second attack: finite-bi-index Clifford tapes

There is another realization of the user's “tape” idea.

Let \(L\curvearrowright X=L/H\) be an infinite transitive action with finitely many orbits on ordered pairs.  Put a Pauli pair \((P_x,Q_x)\) at every site, identify all local commutators with one central sign \(J\), and make distinct sites commute.  Then any exact \(J=-1\) representation containing \(n\) distinct sites has dimension divisible by \(2^n\).

Finite pair-orbit type makes the infinite lamp relations finitely describable up to conjugacy.  What prevents this from immediately solving the problem is **site coherence in approximate representations**: two words representing the same coset need not give the same approximate lamp unless approximate centralization of the stabilizer \(H\) can be rounded uniformly.

Thus a sharp conditional criterion is:

> Find a finitely presented finite-bi-index pair \(H\le L\) for which the stabilizer representation is uniformly HS-roundable on the adjoint/multiplicity sector.  Then the finitely presented Clifford-tape extension is a serious nonhyperlinear candidate.

The Houghton highly-transitive examples fail this test: their amenable non-residually-finite stabilizers are not the required HS-stable objects.  The finite-bi-index route therefore remains a clean auxiliary search problem, not a finished construction.

---

## 15. Most aggressive program from here

The shortest route I currently see is:

1. **Fix one non-CE BCS** with bounded context arity.
2. **Compile every context predicate** by Theorems 2.1--4.1.
3. **Use an explicit finite packet exactifier** for the class-two 2-groups, retaining the shared selector words up to controlled HS error.
4. **Put the packet multiplicity wire under a Kazhdan/compressor action** already available in the repo.
5. **Prove a multiplicity-curvature lemma:** positive BCS violation density implies a self-normalized multiplicity defect which survives transport around one finite holonomy cycle.
6. **Apply the marked spectral carrier lemma and bounded-overlap payment** to get a fixed HS energy floor.

If Step 5 is achieved with a finite presentation, the open hyperlinear problem is solved.

The significant reduction is that Step 5 no longer needs to invent nonlinear group logic.  Nonlinear logic has been compiled into the rank of an affine commutation matrix.  What remains is a geometric/representation-theoretic transport theorem.

---

## 16. Computational verification

The script

```text
experiments/schur_clifford_rank_gate.py
```

constructs the ABP/Schur matrix and performs Gaussian elimination over \(\mathbf F_2\).

Current checks:

```text
AND gate M(x,y)=[[1,x],[y,0]]
(0, 0) rank=1 target=1
(0, 1) rank=1 target=1
(1, 0) rank=1 target=1
(1, 1) rank=2 target=2

exhaustive k=1: verified all 4 predicates
exhaustive k=2: verified all 16 predicates
exhaustive k=3: verified all 256 predicates
one-hot-3: compiler matrix size 9, baseline rank 8; verified
```

These checks do not prove the global hyperlinear claim; they verify the finite predicate-rank compiler exhaustively at small arity.

---

## 17. Audit: what is proved and what is not

### Proved here

- every Boolean predicate admits an affine-linear matrix with rank \(N+f(x)\) on the Boolean cube;
- that rank can be realized as the spin-block dimension of a finite class-two 2-group;
- the nested packet inclusion \(A_f\le B_f\) converts the predicate into exact restriction multiplicity \(2^{f(x)}\);
- the marked-carrier + bounded-overlap inequalities yield a dimension-free HS obstruction once a positive local violation mass with local payment exists;
- a contractive computation ladder with exponentially decaying transfer and polynomial error accumulation forces a uniform energy floor.

### Not proved here

- a finite group presentation which returns the Schur--Clifford multiplicity wire with the required positive-density curvature;
- a complete BCS-to-group compiler preserving the multiplicity mismatch in normalized HS microstates;
- an explicit nonhyperlinear group.

Those are exactly the remaining proof obligations.  Claiming the open problem solved before the return-transducer theorem is proved would be incorrect.

---

## References / nearby ingredients

- M. Fanizza, L. Kroell, A. Mehta, C. Paddock, D. Rochette, W. Slofstra, Y. Zhao, *The NPA hierarchy does not always attain the commuting operator value*, arXiv:2510.04943 (2025).  In particular their Definition 4.1 / Theorem 4.4 supply Turing-machine BCS families with a distinguished signal obeying a quantitative signal-versus-error inequality on one side of the reduction.
- C. Paddock, W. Slofstra, *Satisfiability problems and algebras of boolean constraint system games*, arXiv:2310.07901.
- Classical Valiant-style equivalence between algebraic branching programs and affine determinant representations; the proof in Section 2 above is self-contained for the only form needed here.
- Standard representation theory of extraspecial 2-groups / finite Heisenberg groups: a nondegenerate commutator form of rank \(2r\) gives spin dimension \(2^r\).


## 18. Repository audit, added on ingestion 2026-08-19

**Novelty sweep.** Every node the source cites by name exists and is cited
correctly: `finite-selector-gadget-induction-barrier`,
`semisimple-packet-multiplicity-collapse`, `scaled-kazhdan-transport`,
`kazhdan-tensor-type-transport`, `mipstar-bcs-tracial-nonru-exists`,
`marked-hs-separation-forces-spectral-density`,
`bounded-overlap-syndrome-energy-accounting`.  Section 6 is not new: it is the
composition of the last two, already in the graph.  Section 12 is not new
either: `finite-graph-of-groups-representation-types-are-integer-flows` and
`clifford-block-amalgam-residually-finite` already record it.  One correction:
the source's Section 13 speaks of a "signed-Hecke route" as though it were a
node; it is an unwired note, `notes/TRUE_PIECEWISE_SIGNED_HECKE_COMPILER.md`.

Genuinely absent before this ingestion, and therefore authored: the affine
rank compiler (nothing in the graph mentioned branching programs or `F_2`
rank), the Clifford rank/dimension dictionary, the `2^(f(x))` restriction
multiplicity, the forbidden-mass gap, and the contractive ladder.

**Independent verification.** `experiments/schur_clifford_rank_gate.py` was run
and reproduces the source's reported output exactly.  It was then extended
beyond what the source checked; see `experiments/` and the node
`boolean-predicate-is-one-rank-jump` for the range covered.

**One gate the source does not state, and it is load-bearing.**  Inequality
(9.1) is used only through the number `beta_B`.  Nothing downstream of it --
(9.2), (9.3), Target 11.1 -- refers to *why* the forbidden mass is bounded
below.  But a classically unsatisfiable CSP also has a positive forbidden-mass
lower bound, by an elementary counting argument with no MIP*, no ultraproduct
and no non-CE hypothesis; and the Schur--Clifford compilation of a classically
unsatisfiable CSP, glued as a graph of finite groups, is virtually free and
hence hyperlinear.  So the chain from a forbidden-mass bound to a positive HS
energy floor **must fail** on that instance.

Consequently the non-CE input is consumed nowhere except inside the return
transducer, and any proof of Target 11.1 that does not visibly use it is wrong.
This is recorded as `multiplicity-surplus-is-blind-to-the-non-ce-input` and is
the mandatory falsification test for every candidate transducer: run it on a
classically unsatisfiable CSP and check that it fails.

There is a second, sharper form of the same point.  The class-two packet makes
its own selectors `z_l` **central**.  If context packets are glued over their
shared selectors by an amalgam, a selector central in each factor is central in
the amalgam, so the BCS variables become *globally* commuting and the system
degenerates to exactly the classical CSP above.  Breaking that degeneracy is
not a detail of the transducer; it is the transducer.
