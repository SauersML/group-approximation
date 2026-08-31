---
rg: 2
id: right-core-equivariant-cayley-average-produces-relative-toeplitz-window
kind: claim
title: Right-core-equivariant Cayley averaging produces the full relative Toeplitz window
requires:
  - finite-positive-definite-window-is-a-relative-corner-selector
distinct_from:
  induced-rounding-needs-rms-section-fillings: that bounds one word-section gauge by relative van Kampen areas; this gives the exact positive kernel for an arbitrary coset gauge and isolates its optimized edge energy.
  gauge-optimized-induced-energy-target: that proposes a uniform estimate after moving the exact core; this proves the finite averaging identity to which such an estimate would apply.
  exact-core-multiplicative-domain-does-not-descend-to-normal-quotient: that shows the identity-coset induced corner misses translated normal rows; this averages all translated rows and identifies the exact energy required to repair them.
---

Let \(G\) be finite, \(B<G\), and
\(\beta:B\to U(d)\).  Choose a right-coset transversal
\(T\subseteq G\).  Choose arbitrary unitaries \(Z_t\in U(d)\),
\(t\in T\), and extend them to a function \(W:G\to U(d)\) by the unique
rule

\[
W_{tb}=Z_t\beta(b)\qquad(t\in T,\ b\in B).              \tag{RCA1}
\]

Define

\[
F(k)={1\over |G|}\sum_{g\in G}W_g^*W_{gk}.             \tag{RCA2}
\]

Then \(F\) is operator-valued positive definite, \(F(e)=1\), and

\[
F(b)=\beta(b)\qquad(b\in B).                            \tag{RCA3}
\]

For a prescribed marked tuple \(U_s\in U(d)\), put

\[
{\cal E}_s(W)
 ={1\over |G|d}\sum_{g\in G}\|W_{gs}-W_gU_s\|_F^2.      \tag{RCA4}
\]

Then

\[
\|F(s)-U_s\|_{2,d}\leq\sqrt{{\cal E}_s(W)}.             \tag{RCA5}
\]

Consequently, if a moving family admits right-core-equivariant gauges with

\[
\max_s{\cal E}_s(W)\longrightarrow0,                   \tag{RCA6}
\]

then (RCA2), followed by
'finite-positive-definite-window-is-a-relative-corner-selector', gives
finite-dimensional exact relative corners.  For a property-\((T;FD)\)
group these collapse to flexible exact representations on
\(d+o(d)\) dimensions.

The positivity proof includes every translated normal row.  For
\(g_i\in G\), reindexing \(a=cg_i\) gives

\[
F(g_i^{-1}g_j)
 ={1\over |G|}\sum_{c\in G}W_{cg_i}^*W_{cg_j}.          \tag{RCA7}
\]

Thus the block matrix
\([F(g_i^{-1}g_j)]_{i,j}\) is the average of Gram matrices and is positive.
Equation (RCA3) follows from \(W_{gb}=W_g\beta(b)\).  Finally,

\[
F(s)-U_s
 ={1\over |G|}\sum_g W_g^*(W_{gs}-W_gU_s),
\]

and Cauchy--Schwarz proves (RCA5).

The core symmetry compresses the apparent full-group table to double-coset
data.  Since (RCA3) is unitary, the multiplicative-domain identity gives

\[
F(b_1kb_2)=\beta(b_1)F(k)\beta(b_2).                   \tag{RCA8}
\]

In particular, if \(h\in B\cap kBk^{-1}\), then

\[
\beta(h)F(k)=F(k)\beta(k^{-1}hk).                      \tag{RCA9}
\]

Thus one operator in the indicated stabilizer-intertwiner space is attached
to each double coset \(BkB\), while positivity couples those operators.

For the finite Iwahori quotient

\[
G=A_N,\qquad B=B_N,
\]

take \(U_b=\beta(b)\) on the authenticated core and \(U_x=X\) on the
extending involution.  Every core edge in (RCA4) is then identically zero.
For this Cayley-average construction, the sufficient condition is the single
optimized extender energy

\[
{\cal E}_{N,\beta}(X)
 =\inf_{(Z_t)_{t\in A_N/B_N}}
 {1\over |A_N|d}\sum_{g\in A_N}
       \|W_{gx}-W_gX\|_F^2.                            \tag{RCA10}
\]

If \({\cal E}_{N_n,\beta_n}(X_n)\to0\), the authenticated-core flexible
lift follows.

Word evaluation on a Schreier section is one admissible choice of
\((Z_t)\); its estimate is exactly the RMS filling construction in
'induced-rounding-needs-rms-section-fillings'.  The cyclic core character
shows that this **frozen word-section gauge** can have macroscopic energy.
It does not lower-bound the infimum (RCA10), because nearby exact-core
motion can change the gauge and repair the known scalar counterfamily.
No current congruence or operator-algebraic theorem proves that (RCA10)
vanishes for every Iwahori microstate.  Hence (RCA10) is a finite, double-coset synchronization target.  It is a
sufficient gauge ansatz, not an assertion that every relative ucp kernel has
this unitary-fibre form, and not a completed proof of the root.
