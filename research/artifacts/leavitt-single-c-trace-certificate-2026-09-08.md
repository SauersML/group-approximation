# Explicit finite certificates promoting the trace of c

2026-09-08. Written finite-group, module, and Hilbert-space calculations.
No code was run and no new Lean verification is claimed. Hyperlinearity
of the binary Leavitt unit group remains unresolved.

Let \(H=L_{\mathbb F_2}(1,2)^\times\), and use its native generators
\(c=(123),b_1,b_2,b_3\) from
[the relative-unitary criterion](leavitt-24k-relative-unitary-reduction-2026-09-08.md).
Put \(u=x_{12}(1)\); this has the native word called \(a\) in that
criterion. All traces and Hilbert--Schmidt norms below are normalized.

**Finite certificate theorem.** Given a finite set
\(F\subset H\setminus\{1\}\), chosen native words for its elements,
and integers \(N,M\geq2\), \(r\geq1\), one can construct a finite
list \(\mathcal R\) of true native kernel words such that every
unitary evaluation satisfying

\[
\max_{\rho\in\mathcal R}\|\rho-I\|_2\leq\epsilon
\]

obeys, for every chosen word \(g\in F\),

\[
\boxed{
|\operatorname{tr}G|
\leq
\left(\frac1N+
 \sqrt{\frac1M+3^{-r}+|\operatorname{tr}C|+18\epsilon}
\right)^{1/2}.}
\tag{1}
\]

Here \(C,G\) are evaluations of the prescribed words for \(c,g\).
The certificate uses exact algebraic conjugators and an explicit finite
group. It does not use a compactness argument or finite-simple-group
character-ratio estimates. Its word lengths depend on the inputs; no
uniform short-word bound is asserted.

## 1. A small finite group connecting c to a root

For \(r\geq1\), let

\[
A_r=(C_3)^r,\qquad D_r=A_r\rtimes\langle T\rangle,
\quad T^2=1,\quad TaT^{-1}=a^{-1}.
\]

Thus \(|D_r|=2\cdot3^r\). Embed it in a sufficiently large
degree-zero matrix block over \(\mathbb F_2\): each \(C_3\)
factor acts on a distinct two-coordinate block by

\[
J=\begin{pmatrix}0&1\\1&1\end{pmatrix},
\]

and \(T\) acts on every such block by
\(S=\begin{pmatrix}0&1\\1&0\end{pmatrix}\). Both generators
fix all other coordinates. Choose the total matrix size to be a
power of two strictly greater than \(2r\), so at least one fixed
coordinate remains. The identities \(J^3=S^2=1\) and
\(SJS=J^{-1}\) give the displayed group.

Every nonidentity \(a\in A_r\) is conjugate in \(H\) to the
native \(c\). Indeed, if \(a\) has \(k>0\) nontrivial blocks,
conjugate its \(J^{-1}\)-blocks to \(J\)-blocks using \(S\).
Its moving summand is then \(k\) copies of the same two-dimensional
companion action, and its fixed summand is a positive finite-rank
free \(R\)-module. The Leavitt isomorphism \(R^k\cong R\),
applied identically to both coordinates of the companion action,
identifies the moving summand with one copy of \(J\); it
intertwines the action because all companion entries are scalars.
The nonzero fixed summand is likewise isomorphic to \(R\).
The native permutation \(c\) has exactly these two summands:
one fixed \(R\) and one copy of the companion action on \(R^2\).
Their direct-sum identifications provide the required conjugator.

Similarly \(T\) is conjugate to \(u\). In characteristic two,
\((S-I)^2=0\); on each two-coordinate block its image and a
complement to its kernel are free of rank one, and its kernel equals
its image. On all blocks together these two summands are \(R^r\),
while the extra fixed coordinates supply a nonzero third summand.
Using \(R^r\cong R\) and compressing the nonzero fixed summand
to \(R\) gives the image, moving complement, and fixed homology
of \(u\). Choose the image isomorphism to intertwine the
square-zero map from its moving complement. This conjugates the
unipotents. The extra fixed coordinate is essential to this argument:
it avoids identifying a zero fixed homology module with a nonzero one.

All module maps here can be written using a finite complete binary
prefix code: a code with \(k\) leaves realizes \(R^k\cong R\).
Thus the conjugators are finite algebraic data.

For an exact unitary representation of \(D_r\), let
\(P=3^{-r}\sum_{a\in A_r}\pi(a)\). This is the fixed projection
of \(A_r\). Since \(aTa^{-1}=Ta\) in this exponent-three group,
trace invariance and averaging give

\[
\operatorname{tr}\pi(T)=\operatorname{tr}(\pi(T)P).
\]

Consequently the above conjugacies imply the exact finite inequality

\[
|\varphi(u)|\leq
3^{-r}+(1-3^{-r})\varphi(c)
\tag{2}
\]

whenever the indicated finite relations and conjugacies hold in a
tracial representation. The right side is the trace of a projection.

## 2. A quantitative version needing no exact finite-group representation

Let \(\sigma:D_r\to U(n)\), with \(\sigma(1)=I\), satisfy

\[
\|\sigma(x)\sigma(y)-\sigma(xy)\|_2\leq\epsilon
\qquad(x,y\in D_r).
\tag{3}
\]

Set \(P=3^{-r}\sum_{a\in A_r}\sigma(a)\), which is a
contraction. Approximate multiplication and inversion imply

\[
\|P^*-P\|_2\leq\epsilon,\qquad
\|P^2-P\|_2\leq\epsilon.
\]

For the self-adjoint contraction \(B=(P+P^*)/2\), it follows that

\[
\|B-P\|_2\leq\epsilon/2,\qquad
\|B^2-B\|_2\leq5\epsilon/2.
\]

Let \(Q=1_{[1/2,\infty)}(B)\). For a real scalar \(x\), the
distance to the selected value in \(\{0,1\}\) is at most
\(2|x^2-x|\). Spectral calculus therefore gives

\[
\|Q-P\|_2\leq11\epsilon/2.
\tag{4}
\]

Using (3) three times and approximate inversion once gives

\[
\|\sigma(a)\sigma(T)\sigma(a)^*
       -\sigma(T)\sigma(a)\|_2\leq4\epsilon.
\]

The underlying exact identity is \(aTa^{-1}=Ta\). Taking traces
and averaging over \(a\) yields

\[
|\operatorname{tr}\sigma(T)
 -\operatorname{tr}(\sigma(T)P)|\leq4\epsilon.
\]

Since \(Q\) is a projection and \(\sigma(T)\) is unitary,
\(|\operatorname{tr}(\sigma(T)Q)|\leq\operatorname{tr}Q\).
Twice using (4) proves

\[
|\operatorname{tr}\sigma(T)|
\leq\operatorname{Re}\operatorname{tr}P+15\epsilon.
\tag{5}
\]

Choose native words for the elements of \(D_r\) and their
conjugators from Section 1. Put all their multiplication identities
in the finite kernel list. Also put in the conjugacy identities
identifying every \(a\neq1\) with \(c\), and \(T\) with \(u\).
If each of these rows has defect at most \(\epsilon\), their
trace errors are at most \(\epsilon\). Equation (5) gives

\[
|\operatorname{tr}U|
\leq3^{-r}+(1-3^{-r})\operatorname{Re}\operatorname{tr}C
     +17\epsilon
\leq3^{-r}+|\operatorname{tr}C|+17\epsilon.
\tag{6}
\]

No dimension change or change to the original generator tuple has
occurred: the spectral projection \(Q\) is used only to prove
the inequality.

## 3. The finite Gram certificate on a proper diagonal corner

The algebraic construction in Section 2 of
[the full-character proof](leavitt-full-character-classification-2026-09-08.md)
has the following finite form. For a nonidentity element \(h\)
of a proper diagonal corner and any \(M\geq2\), it constructs
conjugators \(v_1,\ldots,v_M\) such that every quotient

\[
(v_i h v_i^{-1})^{-1}(v_j h v_j^{-1}),\qquad i\neq j,
\]

is conjugate to the fixed root \(u\). The construction uses distinct
ghost prefixes at one common length, a monomial sandwich \(bac=1\)
for a nonzero matrix entry of \(h-I\), and two spare coordinates.
The module splitting and the root-conjugacy maps are explicit there.
The final constant root may be identified with \(u\) by the same
nonzero-free-summand argument used for \(T\) in Section 1.

Add those conjugacy identities to the kernel list. Let \(H\) denote
the evaluation of the chosen word for \(h\), and write
\(H_i=V_i H V_i^*\). These are exact conjugates of the evaluated
matrix, irrespective of whether it represents the group. The rows give

\[
|\operatorname{tr}(H_i^*H_j)|
\leq |\operatorname{tr}U|+\epsilon\qquad(i\neq j).
\]

The diagonal inner products equal one. Cauchy--Schwarz applied to
the average of the \(H_i\) therefore gives

\[
|\operatorname{tr}H|
\leq\sqrt{M^{-1}+|\operatorname{tr}U|+\epsilon}.
\tag{7}
\]

## 4. The finite Gram certificate for any nonidentity element

Fix \(g\neq1\). Sections 3--5 of the full-character proof give
a sufficiently small cylinder \(e\), a proper diagonal projection
\(p\), and arbitrarily many distinct conjugates

\[
g_i=k_i g k_i^{-1},\qquad k_i\in H_e,
\]

such that every nonidentity quotient \(h_{ij}=g_i g_j^{-1}\)
lies in \(H_p\). Choose \(N\) of them. Apply the finite
proper-corner construction of Section 3 to each \(h_{ij}\),
with the same \(M\), and use the literal quotient word for
\(h_{ij}\). No relation error is required to identify its
evaluation with \(G_iG_j^*\).

Thus every off-diagonal inner product of the matrices
\(G_i=K_i G K_i^*\) has absolute trace at most the right side
of (7). A second averaging argument gives

\[
|\operatorname{tr}G|
\leq\left(N^{-1}+
 \sqrt{M^{-1}+|\operatorname{tr}U|+\epsilon}\right)^{1/2}.
\tag{8}
\]

Combining this with (6) proves (1). Taking the union of the
constructed rows works for every element of a finite set \(F\).

The conjugates can be selected by enumeration, rather than an
uncomputable choice. Their orbit is infinite by the proved simplicity
argument. Equality of finite Leavitt expressions is decidable using
the same normal-form argument as the sandwich proof: first put all
ghost lengths at one common depth, obtaining
\(\sum_{|\beta|=d}P_\beta(s_0,s_1)t_\beta\); this is zero
exactly when all collected formal polynomials vanish. The reverse
implication follows by right multiplication by \(s_\beta\) and
the pure-word independence proved by the nonperiodic-tail sandwich.
To select the cylinder itself effectively, enumerate words in the
finitely many cylinder groups at a sufficient fixed depth in parallel
until one fails to commute with \(g\); Section 4 of the full-character
proof guarantees that this happens.
Enumerate until \(N\) different conjugates have appeared. Constructed
units and their inverses can also be converted to native words by
enumeration and this equality test, because native generation is
proved. The argument asserts termination, not a useful search-time
or word-length bound.

## 5. A concrete accuracy choice and its scope

For \(0<\eta\leq1\), take

\[
N\geq2\eta^{-2},\qquad M\geq12\eta^{-4},\qquad
3^{-r}\leq\eta^4/12,\qquad
\epsilon\leq\eta^4/216.
\tag{9}
\]

If \(\operatorname{tr}C=0\), equations (1) and (9) give
\(|\operatorname{tr}G|\leq\eta\) for every chosen \(g\in F\).
The proof uses the bounds
\(N^{-1}\leq\eta^2/2\) and
\(M^{-1}+3^{-r}+18\epsilon\leq\eta^4/4\).

Consequently, any sequence of native generator tuples that satisfies
every kernel word asymptotically and has \(\operatorname{tr}C=0\)
already has canonical traces on every nonidentity word. No tensor
amplification is required for this trace promotion. Applied to the
existing frozen \(24k\) tuples, this proves that the feasible tuples
themselves become canonical microstates.

The certificate list depends on the desired finite set and accuracy.
The result does not replace the full kernel by one fixed packet, and
it does not establish feasibility. Its new content is the explicit
finite algebraic certificate and dimension-independent error bound
for passing from the one trace \(\operatorname{tr}C\) to any
prescribed finite set of traces.
