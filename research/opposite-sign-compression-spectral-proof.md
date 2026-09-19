---
rg: 2
id: opposite-sign-compression-spectral-proof
kind: route
title: Diagonalize the two relation-dependent gates
target: opposite-sign-compressions-are-spectral-routing
requires:
  - taller-vidick-positive-noise-collapses-central-sign
---

# Diagonalize the two relation-dependent gates

## 1. Spectral projections of the common equation word

A left-hand side of an LCS equation is a product of the reflections in one
equation context.  Those reflections commute, so their product \(L\) is
again a reflection:

$$
L=L^*,
\qquad
L^2=I.                                                  \tag{1}
$$

Fix \(s\in\{+1,-1\}\), and write

$$
E_s=\frac{I+sL}{2},
\qquad
E_{-s}=\frac{I-sL}{2}.                                 \tag{2}
$$

These are the two spectral projections of \(L\), with eigenvalues \(s\)
and \(-s\), respectively.

## 2. Exact compression forces spectral containment

Let \(p_+\) be an arbitrary projection satisfying

$$
p_+(L-sI)p_+=0.                                        \tag{3}
$$

Since

$$
L-sI=-2sE_{-s},
$$

equation (3) says

$$
p_+E_{-s}p_+=0.                                        \tag{4}
$$

But

$$
p_+E_{-s}p_+
 =(E_{-s}p_+)^*(E_{-s}p_+).
$$

Therefore \(E_{-s}p_+=0\).  It follows that

$$
p_+=E_sp_+,
\qquad
Lp_+=sp_+.                                              \tag{5}
$$

Taking adjoints also gives \(p_+L=sp_+\), so \(p_+\) commutes with \(L\).

Similarly, if

$$
p_-(L+sI)p_-=0,                                        \tag{6}
$$

then \(L+sI=2sE_s\), and the same positive-square argument gives

$$
E_sp_-=0,
\qquad
Lp_-=-sp_-,
\qquad
p_-L=-sp_-.                                             \tag{7}
$$

Thus the range of \(p_+\) lies in the \(s\)-eigenspace and the range of
\(p_-\) lies in the orthogonal \(-s\)-eigenspace.  In particular,

$$
p_+p_-=0.                                               \tag{8}
$$

Nothing about the two gates was assumed except that they are projections.

## 3. The covering case is only an observable identification

Suppose in addition that

$$
p_++p_-=I.                                              \tag{9}
$$

Using (5), (7), and (9),

$$
E_s
 =E_s(p_++p_-)
 =p_+,
\qquad
E_{-s}
 =E_{-s}(p_++p_-)
 =p_-.                                                  \tag{10}
$$

Consequently

$$
L=sE_s-sE_{-s}=s(p_+-p_-).                             \tag{11}
$$

The two conditional equations therefore do not hide the common source
word behind a genuinely noncommuting flag.  They identify that word with
the binary seed observable \(p_+-p_-\).  If (9) is absent, the complement
\(I-p_+-p_-\) is a reducing subspace on which this local pair imposes no
sign choice.

For the opposite-sign pair in the positive-noise Taller--Vidick support,
this is the exact minimal two-gate normal form.

## 4. Dimension-independent approximate form

The same calculation gives a useful robustness estimate.  Let
\((\mathcal M,\tau)\) be a finite tracial von Neumann algebra with
\(\tau(I)=1\), and put

$$
d_+
 :=\left\|p_+(L-sI)p_+\right\|_{2,\tau},
\qquad
d_-
 :=\left\|p_-(L+sI)p_-\right\|_{2,\tau}.               \tag{12}
$$

Positivity and Cauchy--Schwarz give

$$
\begin{aligned}
\left\|E_{-s}p_+\right\|_{2,\tau}^2
 &=\tau(p_+E_{-s}p_+) \\
 &=\frac12\left|\tau\bigl(p_+(L-sI)p_+\bigr)\right|
 \leq\frac{d_+}{2}.
\end{aligned}                                          \tag{13}
$$

Hence

$$
\left\|(L-sI)p_+\right\|_{2,\tau}
 \leq\sqrt{2d_+}.                                      \tag{14}
$$

Likewise,

$$
\left\|(L+sI)p_-\right\|_{2,\tau}
 \leq\sqrt{2d_-}.                                      \tag{15}
$$

Finally, insert \(E_s+E_{-s}=I\) between the two gates:

$$
\begin{aligned}
\|p_+p_-\|_{2,\tau}
 &\leq \|p_+E_sp_-\|_{2,\tau}
       +\|p_+E_{-s}p_-\|_{2,\tau} \\
 &\leq \|E_sp_-\|_{2,\tau}
       +\|p_+E_{-s}\|_{2,\tau} \\
 &\leq \sqrt{\frac{d_-}{2}}
       +\sqrt{\frac{d_+}{2}}.
\end{aligned}                                          \tag{16}
$$

Thus small compressed equation defects force the two purportedly
noncommuting gates to be close, in normalized Hilbert--Schmidt norm, to
opposite spectral sectors and force their overlap to be small.  The
constant is independent of matrix dimension.

This local estimate does not synchronize gates belonging to different
source words.  A global construction would still need cross-word
relations and a decoder for those relations.
