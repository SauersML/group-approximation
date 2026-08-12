# An exact central phase satisfying the four stubborn atlas relations

Date: 2026-08-11

## Result

Let \(w_{70},w_{86},w_{90},w_{91}\) be the four certified-zero atlas
relations which remain worst in the phase-preserving \(64\)- and
\(128\)-dimensional optimizations, and let \(r=r_{11}\) be the surviving
phase relation.

**Theorem.** There are two honest representations

\[
\rho_1,\rho_2:A_8\longrightarrow U(20160),
\]

each unitarily equivalent to the regular representation of \(A_8\), such
that

\[
\rho(w_{70})=\rho(w_{86})=\rho(w_{90})=\rho(w_{91})=I,
\qquad
\rho(r)=-I.                                         \tag{1}
\]

In particular the phase is exactly scalar, hence commutes with both full
\(A_8\) charts. Therefore no exact inequality involving only these four
zero relations, full ambient-chart extendability, and centrality can force
the phase to vanish.

The construction is finite and exact. Its core is a perfect group \(H\) of
order \(2688\), with structure reported by GAP as

\[
H\cong (C_2^4):\operatorname{PSL}(3,2),
\qquad Z(H)\cong C_2.                              \tag{2}
\]

There are embeddings \(\alpha_i:S_4\hookrightarrow H\) for the two local
atlas factors such that all four \(w_j\) map to \(1\), while \(r\) maps to
the nonidentity central element \(z\in Z(H)\).

## Exact finite certificate

The local \(S_4*S_4\) presentation uses

\[
s_i^2=t_i^3=(s_it_i)^4=1.
\]

The following degree-16 permutations define the two embeddings:

\[
\begin{aligned}
s_1={}&(1\,11)(2\,6)(3\,9)(4\,15)(5\,10)(7\,14)(8\,13)(12\,16),\\
t_1={}&(1\,5\,14)(2\,9\,4)(3\,15\,8)(7\,11\,12),\\
s_2={}&(1\,3)(2\,11)(4\,7)(5\,15)(6\,8)(9\,13)(10\,12)(14\,16),\\
t_2={}&(3\,8\,9)(6\,13\,11)(7\,12\,14)(10\,16\,15).
\end{aligned}                                      \tag{3}
\]

Exact enumeration gives order \(24\) for each factor image and order \(2688\)
for their joint image. Its center consists of the identity and

\[
z=(1\,4)(2\,5)(3\,7)(6\,10)(8\,12)(9\,14)(11\,15)(13\,16). \tag{4}
\]

Direct substitution of the original atlas words—not a stored transcription—
gives

\[
w_{70},w_{86},w_{90},w_{91}\mapsto1,\qquad r\mapsto z. \tag{5}
\]

The self-contained Python certificate verifies (2)--(5) by exact matrix and
permutation arithmetic. GAP independently obtains (3) by forming the
central quotient of the local finite presentation and testing all perfect
groups of order at most \(5000\) with nontrivial center. The first successful
target in its library is `PerfectGroup(2688,2)`; there are eight epimorphisms
to it, four preserving the central phase.

## Completion to regular \(A_8\) charts

Let \(\lambda_H\) be the regular representation of \(H\), and let
\(\pi_-\) be its \((-1)\)-eigenspace for the central involution \(z\). Since
\(z\notin\alpha_i(S_4)\),

\[
\alpha_i(S_4)\times\langle z\rangle\leq H
\]

has order \(48\). Restricting the regular representation first to this
subgroup and then to the \(z=-1\) eigenspace gives

\[
\pi_-\!\downarrow_{\alpha_i(S_4)}
\cong [H:48]\lambda_{S_4}
=56\lambda_{S_4}.                                  \tag{6}
\]

On the other hand,

\[
\lambda_{A_8}\!\downarrow_{S_4}
\cong[A_8:S_4]\lambda_{S_4}
=840\lambda_{S_4}.                                 \tag{7}
\]

Since \(15\cdot56=840\) and
\(15\dim(\pi_-)=15\cdot1344=20160\), equations (6)--(7) give, separately
for \(i=1,2\), an intertwiner

\[
W_i:\ell^2(A_8)\longrightarrow 15\pi_-
\]

on the local \(S_4\). Transport the two regular \(A_8\) representations by
these intertwiners:

\[
\rho_i(g)=W_i\lambda_{A_8}(g)W_i^*.
\]

For every word in the local \(S_4*S_4\), evaluation under
\((\rho_1,\rho_2)\) agrees with \(15\pi_-\) applied to its image in \(H\).
Equations (4)--(5) therefore give exactly (1).

## Scope and next gate

This closes the four-class obstruction route more strongly than the earlier
order-168 quotient: the phase is now scalar and the local models extend to
honest full \(A_8\) representations. It still does not solve the full atlas
problem. The other 20 perfect-overlap-certified cyclic classes use letters
outside these local \(S_4\)'s, and the chosen extension intertwiners are not
known to make them identity.

The concrete next problem is to couple the central order-2688 block to those
20 outside classes while retaining a nonzero \(z=-1\) sector. Any no-go
proof must use at least one of those outside relations; the four persistent
optimizer classes are now completely discharged as a universal obstruction.

The full-chart extension can in fact be made with finite image, not merely
by transporting two complex representations. Attach an
\(A_8\times C_2\) vertex to each subgroup
\(\alpha_i(S_4)\times\langle z\rangle<H\). The resulting graph of finite
groups is virtually free, its common involution \(z\) is central, and a
vertex-injective finite quotient retains both \(A_8\) charts. On the
negative sector of the quotient's regular representation, both chart
restrictions are regular amplifications and \(r=-I\). Thus the remaining
twenty relations may be attacked inside the canonical regular-chart
stratum with finite-image seed data. Full proof:
`FALSE_ATLAS_CENTRAL_GRAPH_COMPLETION.md`.

## Reproduction

    python3 experiments/atlas_stubborn_s4_certificate.py

    /Users/user/.pixi/bin/gap -q \
      experiments/atlas_stubborn_s4_quotient.g
