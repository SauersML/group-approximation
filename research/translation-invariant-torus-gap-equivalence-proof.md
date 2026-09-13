---
rg: 2
id: translation-invariant-torus-gap-equivalence-proof
kind: route
title: Stack a finite linear system at every site of Z^2
requires:
  - translation-invariant-lcs-torus-gap-forces-nonhyperlinear
  - lcs-tracial-ru-gap-equiv-nonhyperlinear
target: translation-invariant-torus-gap-iff-finite-lcs-ru-gap
---

Notation as in the claim. \(R_B\) has generators \(J\) and \(x_{t,s}\)
(\(t\in\mathbb Z^2\), \(s\in S\)). Its relators are \(J^2\), \(x_{t,s}^2\),
\([J,x_{t,s}]\), and, for every equation \(e\) of \(B\) and every \(t\), the
commutators of the generators \(x_{t,s}\) (\(s\in e\)) and the product relator
\(\prod_{s\in e}x_{t,s}=J^{b_e}\). These are exactly the relators of \(B\), copied
at each site; no relator involves two different sites. The torus system
\(\mathrm{Sol}_{R_B,n}\) has the same relators with \(t\in T_n\).

## 1. Dictionary (a)

- **Folding.** The assignment \(x_{t,s}\mapsto x_s\), \(J\mapsto J\) sends every
  relator of \(R_B\) to a relator of \(B\), so it defines a homomorphism
  \(f:\mathrm{Sol}_{R_B}\to\Gamma(B)\) with \(f(J)=J\).
- **Site inclusion.** The assignment \(x_s\mapsto x_{0,s}\), \(J\mapsto J\) sends
  every relator of \(B\) to a relator of \(R_B\), so it defines a homomorphism
  \(\iota:\Gamma(B)\to\mathrm{Sol}_{R_B}\) with \(\iota(J)=J\).
- If \(J\ne1\) in \(\Gamma(B)\), then \(f(J)\ne1\), so \(J\ne1\) in
  \(\mathrm{Sol}_{R_B}\). If \(J=1\) in \(\Gamma(B)\), then \(J=\iota(J)=\iota(1)=1\)
  in \(\mathrm{Sol}_{R_B}\).

## 2. Dictionary (b)

- **Restriction.** Given an \(\varepsilon\)-model \((X_{t,s})\) of
  \(\mathrm{Sol}_{R_B,n}\) in \(U(d)\), the operators \(X_{0,s}\) are exact
  involutions with \(J\mapsto-I_d\). Every relator of \(B\) evaluated at them is the
  site-\(0\) copy, which is a torus relator, so its defect is at most
  \(\varepsilon\). This is an \(\varepsilon\)-model of \(B\).
- **Folding.** Given an \(\varepsilon\)-model \((X_s)\) of \(B\) in \(U(d)\), put
  \(X_{t,s}=X_s\) for all \(t\in T_n\). Each torus relator is a site copy of a
  relator of \(B\) and evaluates to the same matrix, so its defect is at most
  \(\varepsilon\). The involution and \(J\) relators are exact.

## 3. Equivalence

- **(A)\(\Rightarrow\)(C).** Part (4) of
  `translation-invariant-lcs-torus-gap-forces-nonhyperlinear`: \(\Gamma_R\) is a
  finitely presented nonhyperlinear group.
- **(C)\(\Rightarrow\)(B).** `lcs-tracial-ru-gap-equiv-nonhyperlinear`
  (Paddock--Slofstra, Proposition 5.8).
- **(B)\(\Rightarrow\)(A).** Let \(B\) be tracially satisfiable but not
  \(\mathcal R^{\mathcal U}\)-satisfiable. By the bridge recorded in
  `lcs-tracial-ru-gap-equiv-nonhyperlinear` (their Lemma 5.7), \(J\ne1\) in
  \(\Gamma(B)\), and \(J\) is trivial in every approximate representation of
  \(\Gamma(B)\).
  - *Some \(\varepsilon>0\) admits no \(\varepsilon\)-model of \(B\).* Otherwise
    there are \(\varepsilon_k\)-models \(\sigma_k\) with \(\varepsilon_k\to0\). They
    assign exact involutions to the generators of the finite presentation of
    \(\Gamma(B)\), all relator defects tend to \(0\), and
    \(\|\sigma_k(J)-I\|_2=\|-I-I\|_2=2\). So \(J\) is nontrivial in approximate
    representations, a contradiction.
  - By (a), \(J\ne1\) in \(\mathrm{Sol}_{R_B}\). By (b), no torus system
    \(\mathrm{Sol}_{R_B,n}\), for any \(n\), has an \(\varepsilon\)-model. So \(R_B\)
    witnesses (A) with \(n_0=1\).

## 4. Remarks

- The stacked rule has \(\rho=0\) and no interaction between sites, so its
  solution group is the amalgamated product of site copies of \(\Gamma(B)\) over the
  central \(\langle J\rangle\). By `amenable-edge-cycles-cannot-create-an-lcs-gap`,
  stacking a hyperlinear \(\Gamma(B)\) can never produce a gap, consistent with (b).
- A rule with genuine interaction between sites is still subject to (A)\(\Rightarrow\)(C)\(\Rightarrow\)(B):
  its gap, if it exists, is also realized by some finite system. Tori add
  translation invariance, not a new source of non-approximability.
