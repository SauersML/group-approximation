---
rg: 2
id: q8-bs23-terminal-mark-is-exactly-invisible-but-hyperlinear
kind: claim
title: A five-generator terminal coequalizer has an exact invisible mark but remains hyperlinear
artifacts:
  - research/q8-bs23-amalgam-normal-form-and-hs-wall-proof.md
distinct_from:
  wagon-wheel-exact-radical-has-hs-wall: that locates a fixed HS wall in Slofstra's solution-group output; this gives a much smaller explicit Q8/BS(2,3) coequalizer, proves the mark survives by one amalgam normal form, and proves hyperlinearity directly from amenable-edge permanence.
  exact-fd-invisibility-has-no-general-hs-robustification: that is a general logical firewall; this realizes both sides in one finite presentation tailored to the terminal automorphic-coequalizer branch.
---

Put

\[
 A=BS(2,3)=\langle a,t\mid t a^2t^{-1}=a^3\rangle
\]

and

\[
 w=[tat^{-1},a].
\]

Let \(Q_8=\langle x,y,z\rangle\), with \(z\) its central involution,
\(x^2=y^2=z\), and \(yx=zxy\). The rule

\[
 \alpha(x)=y,\qquad \alpha(y)=x,\qquad \alpha(z)=z
\]

is an involutive automorphism of \(Q_8\). Define the explicit
five-generator group

\[
\begin{aligned}
 \Pi=\langle x,y,z,a,t\mid\;&
 z^2=1,\ x^2=y^2=z,\ [z,x]=[z,y]=1,\ yx=zxy,\\
 &t a^2t^{-1}=a^3,\ [z,a]=[z,t]=1,\\
 &w xw^{-1}=y,\quad w yw^{-1}=x\rangle .                \tag{1}
\end{aligned}
\]

Then:

1. \(z\ne1\) in \(\Pi\), and \(z\) is central;
2. every finite-dimensional unitary representation
   \(\pi:\Pi\to U(d)\) has \(\pi(z)=I\);
3. \(\Pi\) is hyperlinear; indeed there are matrix almost-representations
   of the fixed presentation (1) with defects tending to zero and
   \[
      \|\pi_n(z)-I\|_2\longrightarrow\sqrt2.             \tag{2}
   \]

Thus the first two requirements of the terminal coequalizer program can
hold simultaneously in a tiny finite presentation. They do not imply the
third, quantitative requirement.

The mechanism is exact. The word \(w\) is nontrivial and has infinite
order in \(BS(2,3)\), but every finite-dimensional unitary
representation of \(BS(2,3)\) kills it. Hence (1) is the
finite-dimensional image-collapse coequalizer with

\[
 K=Q_8,\qquad G=BS(2,3),\qquad
 \Lambda=1,\qquad \Gamma=\langle w\rangle .
\]

The coinvariant quotient of \(Q_8\) under \(\alpha\) kills \(z\).
Nevertheless

\[
 \Pi\cong
 (Q_8\rtimes_\alpha\mathbb Z)
 *_{\mathbb Z\times C_2}
 (BS(2,3)\times C_2),                                   \tag{3}
\]

where the edge generator maps to the stable \(\mathbb Z\)-generator on
the left and to \(w\) on the right. Amalgam normal form proves \(z\ne1\).

Both vertex groups in (3) are hyperlinear and the edge group is amenable.
Amenable-edge permanence therefore makes \(\Pi\) hyperlinear. The same
normal form which gives perfect infinite-dimensional survival places the
construction inside a closure class that supplies the HS countermodels
(2). Any successful terminal construction must leave this amenable-edge
architecture, or add relations whose quantitative force is not captured
by exact finite-dimensional image collapse. No nonhyperlinear group is
constructed here.

## Attempts

(Repair note: invalid requires-block and dangling proof-artifact removed; the authoring lane's route has not landed and carries the attack.)
