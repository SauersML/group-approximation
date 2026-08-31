---
rg: 2
id: one-kt-compressor-pauli-low-band-countermodel-proof
kind: route
title: Combine one-compressor sofic charts with the marked Pauli central product
target: one-kt-compressor-has-pauli-microstates-with-low-band-leakage
requires:
  - monomial-ascending-hnn-coset-action-sofic
  - sofic-action-gives-marked-pauli-central-product-microstates
  - strict-compressor-mixed-return-collapses-shared-pauli-sign
  - kt-two-positive-compressors-generate-full-obstruction
---

# One-compressor Kun--Thom Pauli microstates and their leaking low band

All matrix Hilbert--Schmidt norms are normalized.

## 1. The actor and its coset action are sofic

Let
\[
 \Gamma=\operatorname{EL}_r(k[x_1,\ldots,x_d]),\qquad k=\mathbb F_q,
\]
and let \(\alpha\) be an injective proper monomial self-embedding induced
by a matrix \(T\in M_d(\mathbb N)\) with nonzero determinant.  Its ascending
HNN extension is
\[
 V_T=\langle\Gamma,t\mid t\gamma t^{-1}=\alpha(\gamma),
                         \ \gamma\in\Gamma\rangle.        \tag{1}
\]

The actor \(V_T\) is sofic.  The kernel of the exponent map
\(V_T\to\mathbb Z\) is the directed union of the conjugate copies
\(t^{-j}\Gamma t^j\).  The group \(\Gamma\) is residually finite, hence
sofic; directed unions preserve soficity; and an extension of a sofic group
by the amenable quotient \(\mathbb Z\) is sofic.

The action
\[
                 V_T\curvearrowright V_T/\Gamma          \tag{2}
\]
is sofic by
\(\textit{monomial-ascending-hnn-coset-action-sofic}\).
The input proved there is stronger than residual finiteness of the actor:
every iterated stabilizer
\[
 \alpha^j(\Gamma)
   =\operatorname{EL}_r(k[T^j\mathbb N^d])
\]
is separable in \(\Gamma\), by finite monomial truncations.  The
all-iterates ascending-HNN criterion then gives a common chart for (2).

## 2. Add the common-center Pauli base

Write
\[
 P_X=(\bigoplus_X\mathbb F_2)\times
     (\bigoplus_X\mathbb F_2)\times\mathbb F_2
\]
with multiplication
\[
 (u,v,e)(u',v',e')
   =(u+u',v+v',e+e'+\langle v,u'\rangle).                \tag{3}
\]
The last coordinate is the common central involution
\(J=(0,0,1)\).  For \(x\in X\), set
\[
 A_x=(\delta_x,0,0),\qquad B_x=(0,\delta_x,0).            \tag{4}
\]
Thus
\[
 [A_x,B_x]=J,\qquad
 [A_x,A_y]=[A_x,B_y]=[B_x,B_y]=1\quad(x\ne y).            \tag{5}
\]

Both hypotheses of
\(\textit{sofic-action-gives-marked-pauli-central-product-microstates}\)
now hold: the actor \(V_T\) is sofic and its action (2) is sofic.  That
theorem gives
\[
                 P_X\rtimes V_T\text{ sofic}.             \tag{6}
\]
Its chart construction maps the common source mark to the tuple of
nontrivial local central signs on every carrier.  In the resulting
permutation models,
\[
        d_{\rm Hamm}(J,1)=1                               \tag{7}
\]
at every stage.

Permutation matrices turn a Hamming model into a normalized-HS model via
\[
        \|U_\sigma-U_\tau\|_2^2
        =2\,d_{\rm Hamm}(\sigma,\tau).                    \tag{8}
\]
Consequently (7) gives
\[
        \|J-I\|_2=\sqrt2                                  \tag{9}
\]
at every stage.  The approximations are trace-faithful on every fixed
nonidentity group word.

## 3. The mixed-return wall survives all Pauli rows

Choose
\[
 \gamma_0\in\Gamma\setminus\alpha(\Gamma),\qquad
 r_0=t^{-1}\gamma_0t.                                    \tag{10}
\]
If \(r_0\in\Gamma\), then
\(\gamma_0=tr_0t^{-1}\in\alpha(\Gamma)\), a contradiction.  Hence the
two sites
\[
        o=\Gamma,\qquad r_0o=r_0\Gamma                    \tag{11}
\]
are distinct.

The root site is fixed by \(\Gamma\), so the exact group rows include
\[
        [B_o,q]=1\qquad(q\in\Gamma).                      \tag{12}
\]
The transported lamp is
\[
        r_0B_or_0^{-1}=B_{r_0o}.                          \tag{13}
\]
By (11), the off-site Pauli rows give
\[
        [A_o,B_{r_0o}]=1.                                 \tag{14}
\]
All fixed instances of (12)--(14) have defects tending to zero in the
sofic/HS microstates.

On the other hand, the canonical group trace vanishes on every nonidentity
group element.  The two involutions in (13) are distinct, and
\(B_{r_0o}B_o\ne1\).  Therefore
\[
\begin{aligned}
 \|B_{r_0o}-B_o\|_2^2
 &=2-2\operatorname{Re}\tau(B_{r_0o}B_o)\\
 &=2.                                                      \tag{15}
\end{aligned}
\]
Equations (12)--(15) are exactly (KPL6).  They exhibit a
\(\Gamma\)-central unitary which is moved a fixed distance by the mixed
return, while its moved copy satisfies the required off-site commutation
row.  Thus this is a countermodel on the Pauli-compatible microstate class,
not merely an abstract low-spectrum example.

## 4. Quantitative leakage of the named vector

Let \(Q\) be a finite symmetric Kazhdan generating set of \(\Gamma\), put
\(m=|Q|\), and let \(L=|\gamma_0|_Q\).  For the \(n\)-th microstate define
\[
 d_{H,n}=\max_{q\in Q}\|[B_{o,n},u_{q,n}]\|_2,
\]
and define \(\Delta_n,P_{\eta,n},\nu_{\eta,n}\) as in (KPL8).

The spectral mixed-return estimate
\(\textit{strict-compressor-mixed-return-pauli-proof}\), equation (30),
applied to the present tuple says
\[
 \|J_n-I\|_2
 \leq d_{0,n}+d_{X,n}
      +2L\sqrt{m\eta}
      +4\nu_{\eta,n}
      +{4d_{H,n}\over\sqrt\eta}.                          \tag{16}
\]
Here \(d_{0,n},d_{X,n},d_{H,n}\to0\), while (9) gives
\(\|J_n-I\|_2\to\sqrt2\).  If
\(\eta_n\downarrow0\) and
\(d_{H,n}/\sqrt{\eta_n}\to0\), all terms in (16) except the leakage vanish.
Hence
\[
        \liminf_n\nu_{\eta_n,n}\geq{\sqrt2\over4}.         \tag{17}
\]
This is operator norm on \(L^2(M_{d_n})\), not normalized Hilbert--Schmidt
norm on the adjoint superoperator.  The vector witnessing it is the named
full-rank unitary \(B_{o,n}\).

The conclusion is compatible with robust property \((T)\).  A theorem which
bounds the normalized rank of the leaking spectral sector by \(o(d_n^2)\)
does not control its \(2\to2\) norm.  One vector has normalized adjoint rank
\(1/d_n^2\), yet a unit vector can witness norm-one leakage.  The Pauli
relations ensure that this exceptional vector is a full-rank observable;
they do not turn its one-dimensional adjoint span into positive normalized
spectral mass.

## 5. Why the full actor is different

For \(d=3\), the two positive strict compressors
\[
        B=I+E_{12},\qquad A=CB
\]
from
\(\textit{kt-two-positive-compressors-generate-full-obstruction}\)
generate \(\operatorname{SL}_3(\mathbb Z)\), and together with \(\Gamma\)
generate the full Laurent Kun--Thom actor.  Each one-compressor restriction
has the countermodel above, but their canonical permutation/Pauli charts
cannot be placed on one common actor map.

Thus no proof of full-actor mixed-return normalization can use only:

- property \((T)\) of the stabilizer;
- the robust adjoint spectral gap for one polynomial vertex;
- one nested compression chain;
- the complete shared-Pauli rows restricted to that chain; or
- normalized spectral-count control.

The first possible source of additional rigidity is simultaneous coherence
of two noncommuting compressor directions.  Producing operator-norm
normalization for the named \(B_o\) from that joint packet, or producing a
common unitary countermodel for the two individually sofic Pauli charts, is
exactly the remaining full-actor problem.
