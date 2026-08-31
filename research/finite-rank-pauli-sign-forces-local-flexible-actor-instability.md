---
rg: 2
id: finite-rank-pauli-sign-forces-local-flexible-actor-instability
kind: claim
title: A separated Pauli sign forces padding-stable instability on one finite actor packet
artifacts:
  - research/padded-actor-correction-collapses-finite-rank-pauli-sign.md
distinct_from:
  kazhdan-stabilizer-collapses-shared-pauli-sign: that treats a coordinatewise genuine actor; this measures the exact perturbation cost from arbitrary Pauli-compatible actor matrices to a genuine actor after padding or deletion.
  kt-local-actor-correction-pays-majorana-return: that gives the analogous local correction estimate for the Kun--Thom Majorana return; this treats the finite-rank shared-center Pauli sign and all double-coset prototype rows.
  infinite-hyperlinear-kazhdan-group-is-not-hs-stable: that obstructs strict local HS stability for an entire Kazhdan group; this is a weaker source-specific assertion on one fixed actor packet, but it survives sublinear padding.
---

**ESTABLISHED QUANTITATIVE REDUCTION; RELATIVE ACTOR EXACTIFICATION
OPEN.**

Let \(G\curvearrowright X=G/\Gamma\) be transitive and infinite.  Suppose
that \(\Gamma\) has finite Kazhdan set \(Q\) with constant \(\kappa>0\), and
choose the finitely many nontrivial double-coset representatives
\[
 \Gamma\backslash G/\Gamma
 =\{\Gamma,\Gamma r_1\Gamma,\ldots,\Gamma r_s\Gamma\}.
\]
Set
\[
 T=Q\cup\{r_1,\ldots,r_s\},\qquad
 C_\kappa=2+\frac{16}{\kappa}.
\]

Let \(A,B,J,u_t\in U(d)\), \(t\in T\).  Let \(\delta\) be the maximum defect
of the following finite shared-Pauli rows:
\[
 ABA^*B^*=J,\qquad [A,u_q]=[B,u_q]=1\quad(q\in Q),
\]
and
\[
 [C,u_{r_\ell}D u_{r_\ell}^*]=1
 \quad(C,D\in\{A,B\},\ 1\le\ell\le s).
\]
For arbitrary \(p\ge0\) and arbitrary padding unitaries
\(v_t\in U(p)\), suppose a genuine representation
\[
 \rho:G\to U(d+p)
\]
satisfies
\[
 \epsilon=\max_{t\in T}
 \|\rho(t)-(u_t\oplus v_t)\|_{2,d+p}.
\]
Then, with \(\lambda=\sqrt{d/(d+p)}\),
\[
 \boxed{\quad
 \lambda\|J-I_d\|_{2,d}
 \le C_\kappa\bigl(\lambda\delta+4\epsilon\bigr).
 \quad}                                                    \tag{PFA1}
\]

Consequently, if \(\delta_n\to0\), \(p_n/d_n\to0\), and
\[
 \liminf_n\|J_n-I\|_{2,d_n}\ge c>0,
\]
then every such padded exact actor satisfies
\[
 \liminf_n\max_{t\in T}
 \|\rho_n(t)-(u_{n,t}\oplus v_{n,t})\|_2
 \ge\frac{c}{4C_\kappa}.                                  \tag{PFA2}
\]
For the tracial spin sector, \(c=\sqrt2\).  Thus the obstruction survives
arbitrary sublinear padding with the explicit floor
\[
 \frac{\sqrt2}{4(2+16/\kappa)}.                            \tag{PFA3}
\]

It also survives deletion.  If a projection of relative rank at least
\(1-\theta_n\) reduces all matrices \(u_{n,t}\), \(t\in T\), and their
restrictions are \(\epsilon_n\)-close on \(T\) to a genuine representation
of \(G\), then
\[
 \theta_n\to0,\quad\delta_n\to0,\quad
 \liminf_n\|J_n-I\|_2\ge c
 \quad\Longrightarrow\quad
 \liminf_n\epsilon_n\ge\frac{c}{4C_\kappa}.                \tag{PFA4}
\]

Only the fixed packet \(T\) must be corrected.  Full flexible HS stability
of the actor is sufficient but much stronger: the needed theorem concerns
only actor microstates which extend across the Pauli host and only their
coordinates in \(T\).

This pins down the spectral-atlas failure.  A robust Kazhdan adjoint
Laplacian for approximate actor matrices yields a low-energy Hilbert
subspace, not a finite von Neumann algebra or a conditional expectation.
Hence it does not supply the multiplicative polar rounding used for an
exact actor, and the two named Pauli rows leave an arbitrary unitary
multiplicity factor on every fixed packet.  Neither the 2025 local/flexible
HS-stability results nor the Gao--Kunnawalkam Elayavalli--Patchell
sofic-action permanence theorem supplies the relative correction required
by (PFA1).  No sofic atlas, and no nonhyperlinear group, is claimed here.

DERIVATION
padded-actor-correction-collapses-finite-rank-pauli-sign
