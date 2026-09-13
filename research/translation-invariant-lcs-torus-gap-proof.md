---
rg: 2
id: translation-invariant-lcs-torus-gap-proof
kind: route
title: Periodize almost-models of translation-invariant linear systems onto tori
requires:
  - local-approximation-properties-are-marked-closed
target: translation-invariant-lcs-torus-gap-forces-nonhyperlinear
---

Notation as in the claim. \(\|A\|_2=(\operatorname{tr}(A^*A)/d)^{1/2}\) on \(M_d\);
it is unitarily invariant and \(\|A\otimes I\|_2=\|A\|_2\). For unitaries,
\(\|\prod A_i-I\|_2\le\sum\|A_i-I\|_2\).

## 1. Finite presentation

Present \(\mathrm{Sol}_R\rtimes\mathbb Z^2\) by the generators of \(\mathrm{Sol}_R\)
and \(a_1,a_2\), with the relations of \(\mathrm{Sol}_R\), \([a_1,a_2]=1\),
\(a_iJa_i^{-1}=J\), and \(a_ix_{t,s}a_i^{-1}=x_{t+e_i,s}\). By Tietze moves,
eliminate every \(x_{t,s}\) with \(t\ne0\) through \(x_{t,s}=a^tx_{0,s}a^{-t}\). A
context relator or commutation relator at translate \(t\) becomes the conjugate by
\(a^t\) of the one at \(0\), hence redundant. The conjugation relations become
trivial. What remains is finite: \(x_{0,s}^2=J^2=1\), \(J\) central, \([a_1,a_2]=1\),
and the finitely many context and commutation relators of the contexts at
translate \(0\), written with \(x_{u,s}=a^ux_{0,s}a^{-u}\). Also
\(\mathrm{Sol}_R\le\Gamma_R\) as the kernel of \(\Gamma_R\to\mathbb Z^2\). This proves (1).

## 2. Window models (claim (2))

Let \(F\subset\mathrm{Sol}_R\) be finite, containing \(J\), the generators in \(W\)
and all prefixes of the relators supported in \(W\); let \(L\) bound their lengths.
Hyperlinearity gives, for every \(\eta>0\), a map \(\varphi:\mathrm{Sol}_R\to U(d)\)
with \(\|\varphi(gh)-\varphi(g)\varphi(h)\|_2<\eta\) for \(g,h\in F\) and
\(|\operatorname{tr}\varphi(g)-\tau(g)|<\eta\) for \(g\in F\), where \(\tau\) is the
regular trace (standard definition; see e.g. arXiv:0804.3968).

- **Relators.** For a relator \(r\), telescoping gives \(\|r(\varphi)-\varphi(e)\|_2\le L\eta\),
  and \(\|\varphi(e)-I\|_2^2=2-2\operatorname{Re}\operatorname{tr}\varphi(e)\le2\eta\).
  So \(\|r(\varphi)-I\|_2\le L\eta+\sqrt{2\eta}\).
- **Exact involutions.** If \(U\) is unitary with \(\|U^2-I\|_2\le\kappa\), rounding each
  eigenvalue \(\lambda\) to the nearer of \(\pm1\) gives an involution \(X\) commuting
  with \(U\), with \(\|U-X\|_2\le\kappa/\sqrt2\), because \(|\lambda+\varepsilon|\ge\sqrt2\).
  Apply this to the generators and to \(J\). The relator defects change by at most
  \(O(L\kappa)\).
- **Sector.** Since \(J\ne e\), \(\tau(J)=0\), so the rounded \(X_J\) has
  \(|\operatorname{tr}X_J|=O(\eta)\). Set \(p=(I-X_J)/2\); then
  \(\operatorname{tr}p\ge\tfrac12-O(\eta)\). Also \(\|[X_x,X_J]\|_2=O(\eta)\) from the
  central relators, and \([X_x,p]=-[X_x,X_J]/2\).
- **Compression.** On \(pH\), with normalized norm \(\|\cdot\|_{2,p}\), let \(Y_x=pX_xp\).
  It is self-adjoint, and \(\|Y_x^2-I\|_{2,p}\le\sqrt{d/\operatorname{rk}p}\,\|[X_x,p]\|_2=O(\eta)\).
  For self-adjoint \(y\), \(|y-\operatorname{sign}y|\le|y^2-1|\), so
  \(Z_x=\operatorname{sign}Y_x\) (sign \(0=1\)) is an exact involution with
  \(\|Z_x-Y_x\|_{2,p}=O(\eta)\).
- **Relators on \(pH\).** For a word of length \(\le L\),
  \(\|p\,w(X)\,p-w(Y)\|_{2,p}\le L\sqrt{d/\operatorname{rk}p}\max\|[X_x,p]\|_2\). A context
  relator says \(\prod X\approx X_J^{b_c}\), and \(pX_J^{b_c}p=(-1)^{b_c}p\). With
  \(J\mapsto-I_{pH}\), every relator supported in \(W\) has defect
  \(O_{L}(\eta+\sqrt\eta)\). Choosing \(\eta\) small gives a \(\delta\)-model on
  \(\operatorname{rk}p\ge1\) dimensions.

## 3. Periodization (claim (3))

Let \((X_{u,s})_{u\in W_m}\) be a \(\delta\)-model on \(\mathbb C^d\) and \(m\mid n\).

- **One shift.** For \(\sigma\in W_m\), tile \(T_n\) by the squares
  \(Q_{\sigma,k}=\sigma+mk+W_m\), \(k\in(\mathbb Z/(n/m))^2\). Let
  \(H_\sigma=\bigotimes_k\mathbb C^d\), one factor per tile. For \(t\in Q_{\sigma,k}\),
  let \(X^\sigma_{t,s}\) be \(X_{t-\sigma-mk,s}\) on factor \(k\), tensored with
  identities, and \(J\mapsto-I\). These are exact involutions.
- **All shifts.** Put \(H=\bigoplus_{\sigma\in W_m}H_\sigma\) and
  \(X_{t,s}=\bigoplus_\sigma X^\sigma_{t,s}\). All summands have equal dimension, so
  \(\|A\|_2^2\) on \(H\) is the average over \(\sigma\) of \(\|A_\sigma\|_2^2\).
- **Good shifts.** Take a torus relator \(r\) from a context translate \(c+t\) (a
  context relator or a commutation relator). If \(c+t\) lies inside one tile
  \(Q_{\sigma,k}\), then \(r(X^\sigma)=r'(X)\otimes I\) for the translated relator
  \(r'\) supported in \(W_m\) (since \(m\ge2\rho+1\)). Hence
  \(\|r(X^\sigma)-I\|_2\le\delta\).
- **Bad shifts.** Otherwise the defect is at most \(2\). The context meets at most
  \(2\rho+1\) consecutive columns and rows. It crosses a vertical tile boundary for
  at most \(2\rho\) residues of \(\sigma_1\), and a horizontal one for at most
  \(2\rho\) residues of \(\sigma_2\). So at most \(4\rho m\) of the \(m^2\) shifts are
  bad.
- **Result.** Therefore \(\|r(X)-I\|_2^2\le\delta^2+4\cdot4\rho/m\). Involution and
  \(J\) relators are exact.

## 4. Corollary (claim (4))

If \(\Gamma_R\) were hyperlinear, so would be its subgroup \(\mathrm{Sol}_R\)
(`local-approximation-properties-are-marked-closed`, heredity). By §2 with
\(\delta=\varepsilon/\sqrt2\), and §3 with \(m\ge\max(2\rho+1,32\rho/\varepsilon^2)\),
every multiple \(n\ge n_0\) of \(m\) would carry an \(\varepsilon\)-model. That
contradicts the hypothesis.

## 5. Screen (claim (5))

- **Evaluating a derivation.** Let \(J=\prod_{i\le A}w_ir_i^{\pm1}w_i^{-1}\) in the free
  group, with \(r_i\) torus relators. Evaluated in an \(\varepsilon\)-model, it gives
  \(\|-I-I\|_2=2\le A\varepsilon\).
- **The derivation lifts.** In the diagram, cells sharing an \(x\)-edge form components.
  Different components can meet only along \(J\)-edges, and \(J\) is the same element
  in \(\mathrm{Sol}_R\) and \(\mathrm{Sol}_{R,n}\). A component of \(\le A\) cells has
  displacement at most \(2\rho A\) along any closed walk. If \(2\rho A<n\), each
  component lifts consistently to \(\mathbb Z^2\), and the lifted diagram shows
  \(J=1\) in \(\mathrm{Sol}_R\).
- **Conclusion.** So \(J\ne1\) in \(\mathrm{Sol}_R\) forces \(A\ge n/(2\rho)\), and the
  certified gap is at most \(2/A\le4\rho/n\).
