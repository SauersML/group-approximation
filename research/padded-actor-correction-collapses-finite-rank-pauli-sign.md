---
rg: 2
id: padded-actor-correction-collapses-finite-rank-pauli-sign
kind: route
title: Pay for the shared Pauli sign with correction on one finite actor packet
target: finite-rank-pauli-sign-forces-local-flexible-actor-instability
requires:
  - kazhdan-stabilizer-collapses-shared-pauli-sign
  - shared-center-pauli-tape-has-same-fp-gate
  - kt-local-actor-correction-pays-majorana-return
  - full-shared-pauli-wall-excludes-nearby-exact-actor
---

# Pay for the shared Pauli sign with correction on one finite actor packet

All Hilbert--Schmidt norms below are normalized in the displayed matrix
dimension.

## 1. The finite interface

Let \(G\curvearrowright X=G/\Gamma\) be transitive and infinite.  Fix a
finite Kazhdan set \(Q\subseteq\Gamma\), with Kazhdan constant
\(\kappa>0\), and representatives
\[
 \Gamma\backslash G/\Gamma
 =\{\Gamma,\Gamma r_1\Gamma,\ldots,\Gamma r_s\Gamma\}.       \tag{1}
\]
Put
\[
 T=Q\cup\{r_1,\ldots,r_s\},\qquad
 C_\kappa=2+\frac{16}{\kappa},\qquad
 K_\kappa=4+\frac{32}{\kappa}=2C_\kappa.                  \tag{2}
\]

Let \(A,B,J\in U(d)\), and let \(u_t\in U(d)\) for \(t\in T\).  No
multiplicativity assumption on the finite table \((u_t)_{t\in T}\) is needed
for the estimate below.  Define
\[
\begin{aligned}
 \delta_0&=\|ABA^*B^*-J\|_{2,d},\\
 \delta_1&=\max_{q\in Q}\max_{C\in\{A,B\}}\|[C,u_q]\|_{2,d},\\
 \delta_2&=\max_{\substack{1\le\ell\le s\\C,D\in\{A,B\}}}
 \|[C,u_{r_\ell}D u_{r_\ell}^*]\|_{2,d},\\
 \delta&=\max\{\delta_0,\delta_1,\delta_2\}.                 \tag{3}
\end{aligned}
\]
These are exactly the same-site, stabilizer, and double-coset prototype rows
of the finite shared-center Pauli presentation.

## 2. Arbitrary padding and local actor correction

Let \(p\ge0\), \(D=d+p\), and
\[
 \lambda=\sqrt{\frac dD}.                                  \tag{4}
\]
Choose arbitrary \(v_t\in U(p)\), and put
\[
 u_t^+=u_t\oplus v_t,\quad
 A^+=A\oplus I_p,\quad B^+=B\oplus I_p,\quad J^+=J\oplus I_p. \tag{5}
\]
The padding matrices \(v_t\) need not be multiplicative.

Suppose there is a genuine representation
\[
 \rho:G\longrightarrow U(D)                               \tag{6}
\]
such that
\[
 \epsilon=\max_{t\in T}\|\rho(t)-u_t^+\|_{2,D}.             \tag{7}
\]
Direct sums scale the three original row defects by \(\lambda\).  For
\(q\in Q\),
\[
 \|[A^+,\rho(q)]\|_{2,D}
 \le \lambda\delta+2\epsilon,                              \tag{8}
\]
and the same estimate holds with \(B^+\).  Indeed replacing one unitary in
a commutator changes its normalized Hilbert--Schmidt norm by at most twice
the replacement distance.

For a double-coset representative, write
\[
 F_C(U,D_0)=[C,UD_0U^*].
\]
The elementary estimates
\[
 \|\rho(r_\ell)D_0\rho(r_\ell)^*
       -u_{r_\ell}^+D_0(u_{r_\ell}^+)^*\|_{2,D}
 \le2\epsilon                                             \tag{9}
\]
and
\[
 \|[C,S]-[C,S']\|_{2,D}\le2\|S-S'\|_{2,D}                 \tag{10}
\]
give
\[
 \|F_{C^+}(\rho(r_\ell),D_0^+)\|_{2,D}
 \le\lambda\delta+4\epsilon.                               \tag{11}
\]
Keep the three row errors separate.  The proof of the exact-actor collapse
gives the asymmetric estimate
\[
 \|J-I\|_2\le d_J+d_X+\frac{16}{\kappa}d_H,                \tag{12}
\]
where \(d_J,d_H,d_X\) are respectively the same-site, stabilizer, and
cross-prototype defects.  This is also the zero-correction case of
\(\textit{full-shared-pauli-wall-excludes-nearby-exact-actor}\).
Applying (12) to the padded tuple and using (8), (11), and the
\(\lambda\)-scaled same-site defect gives
\[
 \|J^+-I_D\|_{2,D}
 \le \lambda\!\left(\delta_0+\delta_2+
                     \frac{16}{\kappa}\delta_1\right)
       +K_\kappa\epsilon
 \le \lambda C_\kappa\delta+K_\kappa\epsilon.              \tag{13}
\]
But
\[
 \|J^+-I_D\|_{2,D}=\lambda\|J-I_d\|_{2,d}.                 \tag{14}
\]
Combining (13)--(14) proves the sharp interface estimate
\[
 \boxed{\quad
 \lambda\|J-I_d\|_{2,d}
 \le \lambda C_\kappa\delta+K_\kappa\epsilon.
 \quad}                                                    \tag{15}
\]

Only the matrices indexed by the fixed set \(T\) were corrected.  The lamp
matrices were not corrected, and no growing actor window was used.

## 3. A padding-stable distance floor

Rearranging (15) gives
\[
 \epsilon\ge
 \frac{\lambda}{K_\kappa}
 \left(\|J-I_d\|_{2,d}-C_\kappa\delta\right).              \tag{16}
\]
Consequently, if a sequence has
\[
 \delta_n\to0,\qquad p_n/d_n\to0,\qquad
 \liminf_n\|J_n-I\|_{2,d_n}\ge c>0,                        \tag{17}
\]
then every padded genuine actor representation satisfies
\[
 \liminf_n\max_{t\in T}
 \|\rho_n(t)-(u_{n,t}\oplus v_{n,t})\|_{2,d_n+p_n}
 \ge \frac{c}{K_\kappa}.                                  \tag{18}
\]
For a tracial Pauli microstate with \(\operatorname{tr}(J_n)\to0\), one has
\(c=\sqrt2\), so the right side is
\[
 \frac{\sqrt2}{4+32/\kappa}.                               \tag{19}
\]
Thus the hidden spin sector is not merely uncorrectable in the same
dimension: it stays a definite distance from every genuine actor after
arbitrary sublinear padding.

## 4. Deleting a negligible reducing corner does not help

There is also a precise deletion version.  Let \(P\) be a projection of
rank \(\alpha d\), \(\alpha\ge1-\theta\), which reduces every \(u_t\),
\(t\in T\).  Suppose there is a genuine representation
\[
 \sigma:G\to U(P\mathbb C^d)
\]
such that
\[
 \epsilon_P=\max_{t\in T}
 \|\sigma(t)-Pu_tP\|_{2,P\mathbb C^d}.                     \tag{20}
\]
Extend \(\sigma\) by the trivial representation on
\((I-P)\mathbb C^d\).  Since the distance between two unitaries is at most
\(2\),
\[
 \max_{t\in T}\|\sigma(t)\oplus I-u_t\|_{2,d}
 \le \sqrt{\alpha\epsilon_P^2+4(1-\alpha)}
 \le \sqrt{\epsilon_P^2+4\theta}.                         \tag{21}
\]
Apply (15) with \(p=0\) and the right side of (21) in place of
\(\epsilon\).  If \(\theta_n\to0\), \(\delta_n\to0\), and the sign has the
separation (17), then
\[
 \liminf_n\epsilon_{P,n}\ge\frac{c}{K_\kappa}.             \tag{22}
\]
This statement requires a common reducing corner.  An arbitrary compression
which is not approximately reducing is not an actor representation and is
not covered.

## 5. Why Kazhdan spectral rounding stops one step short

For a genuine actor representation, the conjugation maps
\(\operatorname{Ad}\rho(q)\) form a genuine unitary representation of
\(\Gamma\) on \(L^2(M_D)\).  Its invariant subspace is the finite von
Neumann algebra \(\rho(\Gamma)'\), and orthogonal projection onto it is a
conditional expectation.  That multiplicative structure is what permits
polar rounding of \(A\) and \(B\) inside one exact commutant.

For approximate actor matrices \(u_q\), a robust spectral-gap theorem can
control a low-energy spectral subspace of the corresponding adjoint
Laplacian.  It does not make that subspace a unital algebra, identify its
orthogonal projection with a conditional expectation, or make polar
completion stay invariant.  The two named Pauli rows do not repair this:
on every fixed Pauli packet their exact normalizer still contains the full
unitary group of the multiplicity factor.  Spectral projections therefore
do not by themselves produce the finite set of atoms and coherent
permutations required by a sofic-action atlas.

Finite presentation only makes the input defect \(\delta\) a finite-row
quantity.  It supplies no modulus turning the actor table into (6).
Equations (15)--(22) isolate the missing statement exactly:

> every Pauli-compatible actor microstate can, after sublinear padding (or
> deletion of a negligible common reducing corner), be corrected on
> \(T=Q\cup\{r_1,\ldots,r_s\}\) to a genuine representation of \(G\).

This relative assertion is strictly weaker than flexible normalized-HS
stability of \(G\): it concerns only microstates which extend across the
Pauli host and asks for closeness only on one fixed finite packet.  It is
also stronger than robust spectral gap, because it constructs a genuine
group representation rather than a Hilbert-space low-energy subspace.

## 6. Literature and action boundary

The 2025 local Hilbert--Schmidt stability theorem of
Fournier-Facio--Gerasimova--Spaas obstructs strict local stability for
infinite hyperlinear Kazhdan groups.  It does not obstruct flexible
stability, and their finite-presentation local-to-global lemma merely says
that local and global versions coincide once the same stability hypothesis
is already known.  Becker--Lubotzky's property-\((T)\) obstruction is also
same-dimensional.  No audited theorem gives the Pauli-compatible relative
flexible correction above; in particular no infinite property-\((T)\) actor
in the current literature inventory is known to be flexibly
normalized-HS stable.

Gao--Kunnawalkam Elayavalli--Patchell provide the forward implication from
a sofic set action to Connes embeddability of generalized wreath products.
They neither extract a sofic atlas from a hyperlinear Pauli wreath nor
exactify actor matrices.  Their charts would solve a different, stronger
problem: once a lamp chart exists, its named site labels recover the set
action.  The estimate here bypasses charts if the relative actor correction
is supplied, but it does not supply that correction.

Accordingly, the exact external theorem still needed for the finite-rank
Pauli route is the quoted Pauli-compatible, \(T\)-relative flexible actor
stability statement.  Without it, (15) is a quantitative boundary, not a
nonhyperlinearity proof.


## 7. Named-host audit

The repository's named candidates do not currently instantiate the missing
relative theorem.

- The claim \( \textit{hs-stable-finite-bi-index-kazhdan-pair-exists}\) is
  explicitly an open search.  It asks for same-dimensional HS stability of
  the whole actor, which would imply more than the source-specific flexible
  correction used in (15).
- The André--Guirardel sharply two-transitive actor has finite orbit rank,
  but the published construction supplies neither finite presentation of
  the actor nor finite generation or property \((T)\) of the point
  stabilizer.  It also supplies no normalized-HS flexible correction
  theorem.
- For the original Kun--Thom/GKP coset action, the projection
  \[
   \operatorname{EL}_r(R)\rtimes\operatorname{SL}_d(\mathbb Z)
   \longrightarrow\operatorname{SL}_d(\mathbb Z)
  \]
  kills \(\Gamma=\operatorname{EL}_r(R_+)\), and therefore descends to a
  surjection
  \[
   \Gamma\backslash G/\Gamma\longrightarrow
   \operatorname{SL}_d(\mathbb Z).
  \]
  Its double-coset rank is infinite.  Thus this action fails (1) before the
  correction question is reached; see
  \( \textit{kun-thom-coset-action-has-infinite-orbit-rank}\).

Accordingly no named finitely presented infinite finite-rank action in the
audited graph has both a Kazhdan stabilizer and the restricted correction
modulus used in (15).  The minimal external input is not “the actor is HS
stable,” but the following fixed-interface statement: Pauli-compatible
microstates admit \(o(d)\)-flexible correction on \(T\) to one genuine actor
representation.  Equations (16) and (18) give the exact modulus that such a
theorem must beat.
