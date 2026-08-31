---
rg: 2
id: deligne-q8-finite-edge-terminal-compiler-is-equivalent-to-source-gap
kind: claim
title: The Deligne-Q8 property-T terminal compiler is exactly equivalent to the source gap
artifacts:
  - research/deligne-q8-amalgam-and-central-sector-equivalence-proof.md
requires:
  - deligne-triple-cover-fd-central-invisibility
  - deligne-sector-gap-is-exactly-nonhyperlinearity
  - amenable-edge-cycles-cannot-create-an-lcs-gap
distinct_from:
  q8-bs23-terminal-mark-is-exactly-invisible-but-hyperlinear: that uses an infinite-order BS(2,3) residual word and proves the output hyperlinear; this uses the order-three Deligne mark and proves that output hyperlinearity and one-word HS collapse are each exactly equivalent to the unresolved Deligne source question.
  shared-center-extraspecial-wreath-has-fd-invisible-spin-sector: that obtains exact finite-dimensional invisibility from unbounded Pauli rank but lacks a finite presentation in the pinned actor; this uses one Q8 packet and a finite property-T vertex, at the cost of inheriting the source's full HS gap.
---

Let

\[
 1\longrightarrow\langle c\rangle\cong C_3
 \longrightarrow E_3\longrightarrow Sp_4(\mathbb Z)
 \longrightarrow1
\]

be Deligne's triple cover. Let \(Q_8=\langle x,y,J\rangle\), with
\(J\) its central involution, and let

\[
 \alpha(x)=y,\qquad \alpha(y)=xy,\qquad \alpha(J)=J.
\]

This is an order-three automorphism. For any fixed finite presentation
\(E_3=\langle S,c\mid R_E\rangle\), define

\[
\begin{aligned}
 \Pi_D=\langle S,c,x,y,J\mid\;&R_E,\\
 &J^2=1,\ x^2=y^2=J,\ [J,x]=[J,y]=1,\ yx=Jxy,\\
 &[J,s]=1\ (s\in S\cup\{c\}),\\
 &cxc^{-1}=y,\quad cyc^{-1}=xy\rangle .                 \tag{1}
\end{aligned}
\]

Then:

1. \(\Pi_D\) is finitely presented, \(J\in Z(\Pi_D)\), and \(J\ne1\);
2. every finite-dimensional unitary representation of \(\Pi_D\) kills
   \(J\);
3. the following are equivalent:
   \[
   \begin{array}{ll}
   \text{(a)}&E_3\text{ is hyperlinear},\\
   \text{(b)}&\Pi_D\text{ is hyperlinear};
   \end{array}                                           \tag{2}
   \]
4. the following are equivalent:
   \[
   \begin{array}{ll}
   \text{(c)}&\text{every HS almost representation of }E_3
              \text{ sends }c\to I,\\
   \text{(d)}&\text{every HS almost representation of }\Pi_D
              \text{ sends }J\to I.
   \end{array}                                           \tag{3}
   \]

Consequently (3) holds if and only if both groups in (2) are
nonhyperlinear. The finite property-(T) interface has not made the
terminal estimate easier; it has repackaged the Deligne central-sector
problem exactly.

The algebraic survival is transparent:

\[
 \Pi_D\cong
 (Q_8\rtimes_\alpha C_3)
 *_{C_3\times C_2}
 (E_3\times C_2),                                       \tag{4}
\]

where the two edge generators are identified with \(c\) and \(J\).
Amalgam normal form preserves \(J\). Deligne--Mal'cev invisibility sends
\(c\) to the identity in every exact matrix representation, whereupon
the automorphism relations force \(x=y\), and the quaternion relation
forces \(J=1\).

Equation (2) follows in both directions: hyperlinearity passes from
\(E_3\) through the finite-edge amalgam (4), while \(E_3\) embeds as a
vertex subgroup of \(\Pi_D\). For (3), one direction follows from the
dimension-free estimate

\[
 \|J-I\|_2\leq4\|C-I\|_2+3\delta                         \tag{5}
\]

for a tuple of presentation defect at most \(\delta\). In the other
direction, a surviving \(c=\omega I\) central sector and its complex
conjugate combine to match the two eigenlines of the fixed two-dimensional
spin representation of \(Q_8\rtimes C_3\), producing \(\Pi_D\)
almost-representations with \(J=-I\).

The actor \(E_3\) has property (T), but the nontrivial amalgam (4) does
not: its Bass--Serre action has no global fixed point. Thus property (T)
does not cross the very normal-form interface used to preserve the mark.
Any successful construction must add a genuinely non-Bass--Serre
quantitative coupling. No nonhyperlinear group is constructed here.
