# Fixed-generator abelian registers lose polynomial spectral resolution

Let

\[
 U_i e_a=z_i(a)e_a,\qquad z_i(a)\in\mathbb T,
 \qquad 1\leq i\leq k,quad 1\leq a\leq N,
\]

and assume the vectors

\[
 z(a)=(z_1(a),\ldots,z_k(a))\in\mathbb T^k
\]

are distinct.  Their joint spectral algebra is then the full diagonal
position algebra (D_N\subset M_N(\mathbb C)).

Put

\[
 M=\left\lfloor (N/2)^{1/k}\right\rfloor .
\]

For (N\geq 2^{k+1}), we have

\[
 M\geq \frac12(N/2)^{1/k}.
\tag{1}
\]

Partition each circle into (M) half-open arcs of angular length (2\pi/M),
and hence partition (mathbb T^k) into (M^k\leq N/2) boxes.  Within each
box, pair as many of the labels (z(a)) as possible.  If the box occupancies
are (n_b), the number (P) of disjoint pairs satisfies

\[
 P=\sum_b\lfloor n_b/2\rfloor
 \geq \frac{N-\#\{b:n_b>0\}}2
 \geq \frac N4.
\tag{2}
\]

Let (S) swap the two basis vectors in each chosen pair and fix every
unpaired basis vector.  Then (S=S^*=S^{-1}).  Its diagonal conditional
expectation is the identity on the unpaired coordinates and zero on the
paired coordinates.  Therefore

\[
 \operatorname{dist}_2(S,D_N)^2
 =\|S-E_{D_N}(S)\|_2^2
 =\frac{2P}{N}\geq\frac12.
\tag{3}
\]

If ((a,b)) is one of the chosen pairs, then its two labels lie in the same
box, so for every (i)

\[
 |z_i(a)-z_i(b)|\leq 2\pi/M.
\tag{4}
\]

On the corresponding two-dimensional plane, the commutator
([S,U_i]) has precisely two nonzero entries, both of modulus
(|z_i(a)-z_i(b)|).  Summing over the disjoint pairs gives

\[
 \|[S,U_i]\|_2^2
 =\frac2N\sum_{(a,b)}|z_i(a)-z_i(b)|^2
 \leq (2\pi/M)^2.
\tag{5}
\]

Using (1) and summing (5) over (i) yields

\[
 \sum_{i=1}^k\|[S,U_i]\|_2^2
 \leq \frac{4\pi^2k}{M^2}
 \leq16\pi^2k(2/N)^{2/k}.
\tag{6}
\]

Equations (3) and (6) prove the claim.

If two joint labels coincide, the register-generated diagonal algebra does
not separate those two positions.  The full (M_2) block on their common
eigenspace commutes with every (U_i), so no estimate from these commutators
can recover the intended position algebra.  Hence distinct labels are the
best case, not an extra source of the obstruction.

This turns the informal register wall into a quantitative finite statement:
for fixed (k), a constant fraction of the register can be mixed at total
commutator energy (O_k(N^{-2/k})).  A nonabelian expander can avoid this
spectral packing only by abandoning the joint-eigenvalue position basis; its
controlled operators then require additive spectral projections rather than
ordinary group words.
