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

The residual algebra also carries an exact endogenous dimension stop.  Two
free-algebra letters enumerate standard polynomials `p_n`; `p_n` is nonzero
formally, but `p_L` vanishes under every substitution in `M_L(C)` by
Amitsur--Levitzki.  Adjoining inverses to all `p_n` gives a nonzero countable
algebra with no finite-dimensional representation.  This supplies a literal
program which reacts to the spectator size without receiving it as input.
What it does not supply is the decisive analytic compiler: the standard
polynomials are additive and grow with `L`, and their free-skew-field inverses
need not be bounded.  Recursive compression must still turn the failed
instruction into new Schur cells using finitely many unitary group relations
and a constant HS loss.

There is a bounded reformulation which is likely cleaner than the polynomial
tape.  The residual `M_L(C)` has atomic trace floor `1/L`; `r` independent
flip cells generate `M_(2^r)(C)` and ask for minimal projections of trace
`2^(-r)`.  Diffuse finite factors support the entire nested dyadic tower,
whereas a matrix fails as soon as `r>log_2L`.  The local payload is therefore
already group-native.  What remains is solely a finite recursive controller
which chooses that depth from the current microstate and transports all split
checks with constant HS loss.

Replicating the non-CE BCS now has an exact quantitative payoff.  Among `C`
contexts, each finite-dimensional replica has one context with forbidden mass
at least `beta_B/C`.  Across `N` commuting replicas these chosen forbidden
projections commute, so one joint sector violates at least
`ceil(beta_B N/C)` sites.  Their flip cocycles are independent and force
dimension at least `2^(ceil(beta_B N/C))`.  No common forbidden assignment or
common context across replicas is needed.  This establishes genuine
exponential amplification of copied bad regions; fixed `N` is still finite
profile pressure, so the adaptive same-model controller remains essential.

The finite-window result is robust once the controller supplies an all-pairs
approximate multiplication table.  Universal Gowers--Hatami stability
exactifies the entire finite replica group with error `42 epsilon` and
dimension enlargement at most `(1-4epsilon^2)^(-1)`, independent of the
number of replicas.  Hence a sign-retaining table already forces
`d >= (1-4epsilon^2)2^(ceil(beta_B N/C))`.  The analytic hole is no longer
packet rounding: it is the finite recursive compilation of local relators into
that all-pairs table with error independent of `N` and runtime.

Kleene self-reference removes even the in-model dimension sensor.  It is
enough for a machine-indexed compiler to have soundness only in the dimension
printed by a halting source machine.  The fixed-point machine searches for a
bad marked microstate and, if it finds one, outputs that witness's dimension
`D`; the compiled halting computation then requests the finite replica count
which contradicts `D`.  Halting would therefore destroy the exact witness
which caused it, so the machine cannot halt.  Hyperlinearity would make the
search halt, while nonhalting preserves the marked group word.  The sole
remaining theorem on this route is runtime-independent perfect-complete
groupification of the finite selected replica table; matrix-dimension
detection is no longer part of it.

There is a genuinely different escape from dimension detection.  If a finite
bi-index action can be rounded uniformly, one base lamp and finitely many
pair-orbit relators produce a coherent *infinite* family of anticommuting
matrices inside the same candidate model.  Such a family cannot exist in any
finite `M_d`: compactness gives two members converging to the same unitary,
whose anticommutator tends to norm two.  This route pays no logarithmic rank
threshold at all.  Its entire missing input is uniform HS site coherence for
an explicit infinite finite-bi-index subgroup pair; finite pair-orbit type by
itself does not control approximate coset representatives.

A sufficient coherence package is now explicit.  Same-dimension normalized-HS
stability of the acting group replaces the approximate action by an exact one;
property (T) of the point stabilizer Reynolds-projects the lamp into its exact
commutant.  Double-coset finiteness then propagates finitely many pair checks
to the whole infinite orbit without any long-word loss.  Thus this alternate
route has one sharply structural input: an explicit infinite finite-bi-index
pair with Kazhdan stabilizer and HS-stable ambient group.

That package cannot come from the easiest stability classes.  An amenable
ambient would make its Kazhdan subgroup finite, and finite subgroup plus
finitely many double cosets would make the whole ambient finite.  Conversely,
an infinite hyperlinear property-(T) ambient cannot be strictly HS-stable by
Becker--Lubotzky.  A noncircular candidate must therefore be nonamenable and
non-property-(T), yet HS-stable and large enough to contain a Kazhdan
finite-bi-index stabilizer.

The inclusion must also be genuinely nonsplit.  Strict normalized-HS
stability descends to retracts, whereas Becker--Lubotzky rule it out for every
infinite hyperlinear property-(T) group.  Hence a hyperlinear Kazhdan
stabilizer cannot be a retract of the stable ambient group; semidirect and
free-product constructions with the evident projection are dead on arrival.

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

### Sign-carrier correction for the robust replica theorem

The approximate exponential-dimension endpoint must use the signed forbidden
Fourier element

\[
Q_i^-={1-J\over 2}\,Q_i,
\]

not the bare forbidden selector projection.  Otherwise a representation with
\(J=+1\) can carry arbitrary forbidden selector mass without activating any
Clifford cocycle, contradicting the claimed dimension bound.  In an exact
representation \(Q_i^-\) is the joint projection onto the forbidden selector
sectors and the marked \(J=-1\) sector.  Its Fourier evaluation transfers
through Gowers--Hatami exactification with the same site-independent constant,
so the repaired hypothesis is exactly the common marked-carrier condition the
global compiler must supply.

### A simpler payload for the dimension-reported diagonal

After the fixed-point machine reports the dimension \(D\), the nonlinear BCS
payload is unnecessary.  Let \(E_N\) be the extraspecial Pauli group with \(N\)
independent pairs and common central sign \(J\).  An all-pairs
\(\varepsilon\)-homomorphism of its complete table for which
\(\|f(J)-I\|_2>42\varepsilon\) flexibly exactifies to a genuine
representation with a nonzero \(J=-1\) spin sector.  Consequently

\[
d\ge (1-4\varepsilon^2)2^N.
\]

Choosing \(N>\log_2(D/(1-4\varepsilon^2))\) contradicts the reported
dimension.  Thus the direct Kleene route no longer needs the non-CE BCS,
predicate rank gates, context selection, or forbidden-mass synchronization.
Its sole open step is the runtime-independent activation of the finite
Clifford multiplication table.  The Schur compiler remains relevant to the
original endogenous programme in which the group itself must discover and
propagate bad regions without an externally reported dimension.

There is a more economical verifier for the same payload.  The
Natarajan--Vidick Pauli braiding test has perfect completeness (using the Magic
Square anticommutation test) and robustness independent of the number of
qubits; its questions have length \(O(N)\) and its answers have constant
length.  Thus the complete \(E_N\) multiplication table is not analytically
essential.  What remains essential is the groupification: the test's
state-dependent multi-prover consistency relations must be lowered to
normalized-Hilbert--Schmidt group words, and the growing question space must
be activated after a halting computation with a runtime-independent gap.

The dimension implication can be made explicit without importing any further
rigidity machinery.  If the self-test places the physical state within
\(\delta\) of \(\Phi_{2^N}\otimes\mathrm{aux}\), every squared Schmidt
coefficient of the target is at most \(2^{-N}\).  A state of local dimension
\(d\) therefore has squared overlap at most \(d/2^N\), whereas norm distance
\(\delta\) gives overlap at least \((1-\delta^2/2)^2\).  Fixing a constant
test error for which \(\delta<1\) yields \(d\ge c_0 2^N\), with universal
\(c_0>0\).  This is recorded as
`pauli-braiding-test-exponential-dimension`; the new direct route leaves only
`dimension-reported-pauli-test-halting-compiler` open.

### Instance-modulated diagonal and a self-referential BCS signal

The Kleene microstate diagonal does not actually require one universal defect
threshold for every source machine.  A total compiler may output computable
rationals

\[
\delta_M>0,\qquad 0<\alpha_M<\sqrt2
\]

depending arbitrarily on the source code.  The fixed-point machine first
computes its own compiled presentation and thresholds, then searches below
\(\delta_M\) and above \(\alpha_M\).  Hyperlinearity eventually beats every
fixed positive \(\delta_M\), so the contradiction is unchanged.  What remains
forbidden is dependence on the unknown eventual halt time or on the reported
dimension.  This is recorded as
`instance-modulated-kleene-microstate-diagonal`.

This relaxation admits the computable constants in Fanizza--Kroell--Mehta--
Paddock--Rochette--Slofstra--Zhao's \(\mathcal L\)-families of BCS algebras.
It also yields a new exact fixed-point source object.  Let \(\mathcal L\) be
the halting set and let \((\mathscr B_m,C_m,D_m)\) be their computable family.
Construct a machine with its own index \(m_*\) which enumerates formal
algebraic proofs that

\[
D_{m_*}=0\quad\text{in }\mathcal A(\mathscr B_{m_*})
\]

and halts exactly when it finds one.  If it halted, membership in
\(\mathcal L\) would give a tracial state with \(\tau(D_{m_*})>0\),
contradicting the proved identity.  Hence it does not halt.  Completeness of
the recursively enumerable ideal-membership search gives
\(D_{m_*}\ne0\), while the nonmembership clause gives, with a computable
constant \(C_{m_*}\),

\[
\varphi_{\mathcal S}(D_{m_*})\le C_{m_*}\varepsilon
\]

for every \(\varepsilon\)-perfect strategy.  Thus one computably specified
finite BCS contains an algebraically nonzero projection erased by every
asymptotically perfect finite-dimensional strategy.

This is not yet a group obstruction.  The precise remaining bridge is
`hs-groupify-self-referential-bcs-signal`: preserve nonvanishing of this marked
projection while compiling the nonlinear BCS predicates to group words, and
make its strategy mass dominate the normalized-HS distance of a marked group
word.  The Schur--Clifford rank gates supply the local nonlinear compiler; a
marked fixed-scale multiplicity return remains open.  This route has one
advantage over the generic forbidden-mass construction: the distinguished
signal prevents a false argument that would also fire on an ordinary
classically unsatisfiable CSP.

There is a sharp constraint on that bridge.  It cannot be a trace-functorial
exact decoder.  Every discrete group has its regular trace, and for a
nonidentity word \(w\),

\[
\tau_{\mathrm{reg}}((w-1)^*(w-1))=2.
\]

If an algebraic decoder turned every tracial representation of the group into
a perfect strategy while lower-bounding \(\varphi(D)\) by the marked
\(L^2\)-mass, applying it to the regular trace would contradict the
\(\varepsilon=0\) signal-collapse inequality.  Therefore the groupification
must be intrinsically finite-dimensional: it has to use rank, determinant,
integral packet multiplicity, or a matrix-only rounding theorem which does not
extend functorially to the regular finite von Neumann algebra.  This explains
why the Schur--Clifford multiplicity machinery is not optional decoration but
the only currently visible way around the regular-trace obstruction.

The source construction also removes part of the apparent global-design
burden.  Its nonmembership proof already contains projections

\[
\widetilde P_n=QU^nPU^{-n}Q
\]

and involutions \(\widetilde X_n=U^n\widetilde XU^{-n}\) satisfying

\[
\widetilde P_n+widetilde X_n\widetilde P_n\widetilde X_n
=\widetilde P_{n+1}.
\]

The identity has a defining-relation decomposition of size polynomial in
\(n\) (Fanizza et al., Proposition 5.14).  In trace it doubles mass from one
tape cell to the next.  Their proof weights the recurrence by
\(2^{-n/2}\), so the exponential contraction dominates the polynomial
certificate loss and yields the signal-collapse estimate.  This is precisely
the proposed “copy bad regions faster than approximation can hide them”
architecture, already realized at the BCS level.

Accordingly, a sharper open target replaces the generic return-transducer:
attach the fixed Schur--Clifford predicate packets to this existing tape and
use matrix-only integral multiplicity to obtain

\[
a_n\le {1\over2}a_{n+1}+K(n+1)^k\sqrt E.
\]

The shift \(U\) already supplies every level, and all local predicates are
fixed.  The sole unresolved interface is coherence of the independently
exactified packet multiplicities along the actual conjugate tape words.  This
is recorded as `finite-dimensional-schur-lift-of-doubling-tape`; together with
the abstract contractive ladder it is now a one-hole route to a
nonhyperlinear group.

One part of that hole has a direct solution.  Suppose two independent flexible
exactifications \((\rho_i,V_i)\) of finite packets both approximate the same
map \(f:A\to U(d)\) on their common finite subgroup.  Average the rank-
\(d\) overlap \(T=V_2V_1^*\):

\[
\overline T={1\over |A|}\sum_{a\in A}\rho_2(a)T\rho_1(a)^*.
\]

Then \(\overline T\) is an exact intertwiner and
\(\|\overline T-T\|_F\le(\eta_1+\eta_2)\sqrt d\).  Since the first \(d\)
singular values of \(T\) equal one, singular-value perturbation shows that the
polar part of \(\overline T\), restricted above threshold \(1/2\), identifies
exact common submodules of dimension at least

\[
(1-4(\eta_1+\eta_2)^2)d.
\]

Thus separate Gowers--Hatami corrections can be aligned pairwise with only a
quadratic-density loss.  The remaining obstruction is genuinely cyclic:
choose these large polar intertwiners compatibly around a recurrence cell and
control the residual commutant holonomy by the original shared-word defect.
This lemma is recorded as `finite-group-shared-overlap-polar-alignment`.

There is also a packet-type mismatch which pairwise alignment cannot remove.
One rank gate is an inclusion \(A_f\le B_f\): restriction outputs an
\(A_f\)-module.  A second independent copy of the same gate expects a
\(B_f\)-module, so merely identifying their \(A_f\) restrictions creates
parallel divisibility conditions rather than multiplying the rank jumps.  A
composable design must either use a growing tower

\[
A_{n+1}=B_n,
\]

or construct a genuine fixed-scale Morita/holonomy return from the output
packet type to the input type.  The first option matches the existing
Fanizza--Slofstra self-similar Clifford sequence, but it replaces fixed-group
exactification by a relative stability problem: exactify the one new Pauli
cell with constants independent of the number of Clifford pairs already
present.  This uniform relative exactification is now the sharp analytic
subproblem inside `finite-dimensional-schur-lift-of-doubling-tape`.

That relative stability problem has a clean quantum-expander solution.  If
\(U_1,\ldots,U_D\) define a random-unitary channel with second
Hilbert--Schmidt singular value \(\lambda<1\) on the old spin factor, then for
the conditional expectation \(E\) to its commutant,

\[
\|X-E(X)\|_2\le {1\over1-\lambda}
\left({1\over D}\sum_j\|[X,U_j]\|_2^2\right)^{1/2}.
\]

The bound is unchanged after tensoring by an arbitrary residual multiplicity
factor.  Hence a proposed new Pauli pair which approximately commutes with the
constant-degree expander moves uniformly close to that residual factor.
Functional calculus followed by stability of the single fixed \(D_8\) table
then exactifies the new cell with constants independent of the number of old
qubits.  This is proved in
`quantum-expander-relative-commutant-rounding` and
`quantum-expander-rounds-relative-pauli-cell`.

Explicit constant-degree quantum expanders are known: Ben-Aroya--Schwartz--
Ta-Shma construct them by tensoring, squaring and quantum zig-zag.  Gross--
Eisert's quantum Margulis expander is even implemented by affine
Clifford/metaplectic transformations in odd phase-space dimension.  Neither
source, as currently imported, supplies the exact binary syntax needed here:
one finite presentation whose level conjugates give the expander unitaries on
every nested qubit prefix and remain compatible with the common sign and rank
gate.  Cairn records that precise algebraic task as
`self-similar-clifford-quantum-expander-tape`.  After it, a separate coherent
type-accounting step must still show that inactive selector sectors are
exactly the Fanizza BCS violation mass, with no complementary leakage.

There is now a more structural source of the expanders. If `(Gamma,N)` has a
finite relative Kazhdan set `S` and a family of projective representations in
which `N` acts irreducibly, then projective phases disappear in the adjoint
action and Schur's lemma says that the only `N`-fixed operators are scalars.
Applying the relative Kazhdan inequality to traceless matrices and lazifying
the `S`-average gives a quantum-expander gap

\[
1-\lambda\ge {\kappa^2\over4|S|},
\]

uniformly in the representation dimension. This is proved in
`relative-t-heisenberg-adjoint-quantum-expansion`. Relative property `(T)`
for elementary-linear semidirect products over finitely generated rings is a
known source of such a gap. Thus the remaining prefix-expander problem is no
longer to synthesize a dimension-uniform spectral gap. It is to build the
finitely presented **Jacobi congruence tower** which couples that fixed word
set to nested binary Schrodinger representations, a tape shift, and the same
central sign used by the rank gate. Cairn isolates this algebraic obligation
as `jacobi-congruence-clifford-tower`.

The first half of that algebraic obligation can be done exactly. For
(R_n=\mathbf F_2[u]/(u^n)), let \(\ell_n\) extract the top coefficient and
put

\[
\omega_n((a,b),(c,d))=\ell_n(ad+bc).
\]

This is nondegenerate, its Weyl representation has dimension (2^n), and
(mathrm{EL}_2(R_n)) acts projectively by Clifford unitaries. Moreover
((a,b)\mapsto(ua,b)) is a symplectic embedding into level (n+1), with a
single hyperbolic plane as orthogonal complement: abstractly it adds exactly
one qubit. The fixed relative-Kazhdan words over
(mathrm{EL}_2(\mathbf F_2[u])\ltimes R^2) give uniform adjoint expanders on
all these levels. This is `truncated-polynomial-binary-weyl-expander-tower`.

What fails is precisely the global syntax. The embedding is not a ring map,
the linear actions do not preserve the embedded prefixes, and the cocycle
uses the level-dependent functional \(\ell_n\). Thus one still has to turn
these exact finite-level objects into a single presentation with compatible
level transport and a common (or coherently conjugated) central sign.

The parenthetical relaxation is exact and useful. If the level signs are

\[
J_n=t^nJ_0t^{-n},
\]

then in every matrix tuple (J_n) is literally unitarily conjugate to the
marked word (J_0). Its distance from the identity and the trace of every
spectral carrier are therefore independent of (n), with no use of a
relator estimate. A ring-valued Heisenberg center with
(t z(c)t^{-1}=z(uc)) can consequently use (z(u^n)) as the local sign at
level (n). This is `conjugate-local-signs-preserve-marked-carrier` and
removes global centrality from the remaining Jacobi-tower obligations.

There is also a sharp structural explanation for the failure of the obvious
equivariant nesting. Any (R)-linear map
(R_n^2\to R_{n+1}^2) lands in (uR_{n+1}^2); the image of the socle then
lies in the radical of the restricted top-coefficient form. Hence no
module-linear symplectic inclusion exists.

The replacement is a two-chart atlas:

\[
P_n(a,b)=(ua,b),\qquad Q_n(a,b)=(a,ub).
\]

Both charts are symplectic. They share (n-1) qubits and have one distinct
transverse boundary qubit each; Fourier swap exchanges them. Upper elementary
maps preserve (Q_n), lower elementary maps preserve (P_n), and in either
case the induced parameter changes by the explicit rule (r\mapsto ur).
Thus the incompatibility is localized to one fixed-size holonomy cell rather
than spread across the growing prefix. Cairn records the exact geometry as
`truncated-weyl-two-chart-boundary` and the remaining compressor/payment
problem as `two-chart-jacobi-action-holonomy`.

The payment end of that holonomy can be closed abstractly. If two finite
Reynolds averages (P,Q) on (L^2(M_d)) are transported termwise by a word
(T), then

\[
{\lvert\operatorname{rank}P-\operatorname{rank}Q\rvert\over d^2}
\le 2\,{1\over D}\sum_j\|TU_jT^*-V_j\|_2^2.
\]

The proof combines the rank lower bound for the distance between two
orthogonal projections with
(|\operatorname{Ad}U-\operatorname{Ad}V|_{2,\mathrm{sup}}^2
\le2\|U-V\|_2^2). Together with the Schur-packet Reynolds gap `(ARG1)`, a
forbidden mass (q) forces holonomy energy at least
(3q^2/(8D^2K)). This is
`forbidden-packet-reynolds-holonomy-payment`. The remaining two-chart problem
is therefore purely the finite word transport of those averages, isolated as
`two-chart-reynolds-word-transport`.

There is an important consistency correction. A word which conjugates one
complete finite group table termwise onto another induces an isomorphism of
their represented image groups. Their Reynolds projections are then exactly
unitarily conjugate and have equal rank. Thus the raw (A_f,B_f) tables
cannot be the two endpoints of the holonomy—the very gap we want would
vanish.

The corrected endpoint is
`stabilized-two-chart-reynolds-word-transport`: attach an infinite packet
tail so the two **stabilized** subgroups are isomorphic, retain a faithful
infinite marked model by an Eilenberg swindle, and use the two-chart/Fanizza
orientation to cancel every finite-prefix boundary except one local
(R_A-R_B) term. A polynomial-time recursive presentation can then be moved
to a finitely presented host using the quantitative Higman theorem, with the
relative Dehn function giving the exact HS error modulus. The open calculation
is now the weighted cancellation of the stabilizing boundary, not raw packet
conjugacy.

A stronger spectral formulation removes even that raw return requirement.
Let (A) be the adjoint Laplacian of a property-((T)) base and let
(C_\alpha) be the Laplacian of its compressed word copy. Word telescoping
gives (C_\alpha\le LA) as quadratic forms, while the HNN relators make
(C_\alpha) Hilbert--Schmidt close to a unitary conjugate of (A). The
property-((T)) SOS certificate puts only (O(\delta^2)) normalized spectral
mass in any fixed interval inside the Kazhdan gap. Comparing spectral counts
at separated thresholds therefore yields

\[
\operatorname{tr}_{\rm ad}
\bigl(1_{[0,b]}(C_\alpha)(1-1_{[0,a]}(A))\bigr)=O(\delta).
\]

This is `property-t-hs-positive-density-commutant-no-growth`: a compressor may
still create a slow, zero-density wall, but not a positive-density one. Since
the Schur predicate packet creates adjoint wall density
(3q^2/(4D^2K)), placing that packet difference in the compressed low space
immediately forces (q^2=O(\delta)). The remaining construction is isolated
as `schur-packet-as-positive-density-compressor-wall`; it no longer needs a
termwise Reynolds-table conjugacy or a copywise multiplicity selector.

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
- A. Natarajan, T. Vidick, *Robust self-testing of many-qubit states*, arXiv:1610.03574.
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
