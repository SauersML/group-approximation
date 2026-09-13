---
rg: 2
id: translation-invariant-torus-gap-iff-finite-lcs-ru-gap
kind: claim
title: A translation-invariant linear rule with a torus-uniform gap exists iff some finite linear system is tracially but not R^U-satisfiable
distinct_from:
  translation-invariant-lcs-torus-gap-forces-nonhyperlinear: that proves a torus-uniform gap gives a finitely presented nonhyperlinear group; this adds the converse by stacking a finite system, so the tiling formulation is equivalent to the finite endpoint.
  lcs-tracial-ru-gap-equiv-nonhyperlinear: that imports the Paddock--Slofstra equivalence between a finite tracial/non-R^U linear system and a nonhyperlinear finitely presented group; this identifies the translation-invariant torus problem with that same endpoint.
  translation-invariant-lcs-with-uniform-torus-gap-exists: that is the open existence statement; this proves it equivalent to the root problem without settling it.
---

Definitions of rules, \(\mathrm{Sol}_R\), torus systems \(\mathrm{Sol}_{R,n}\) and
\(\varepsilon\)-models are those of
`translation-invariant-lcs-torus-gap-forces-nonhyperlinear`. For a finite binary
linear system \(B\) (variables \(S\), equations with parities), \(\Gamma(B)\) is
its solution group with central involution \(J\), and an \(\varepsilon\)-model of
\(B\) in \(U(d)\) is a list of exact involutions, one per variable, with
\(J\mapsto-I_d\) and every relator of \(B\) within normalized Hilbert--Schmidt
distance \(\varepsilon\) of \(I_d\).

**Stacking.** Let \(R_B\) be the rule with site types \(S\) whose contexts are the
equations of \(B\), each placed at the single site \(0\) (so \(\rho=0\)).

**Claim.**

1. **(Dictionary.)** For every finite binary linear system \(B\), every \(n\ge1\),
   every \(d\) and every \(\varepsilon\ge0\):
   - (a) \(J\ne1\) in \(\mathrm{Sol}_{R_B}\) iff \(J\ne1\) in \(\Gamma(B)\);
   - (b) \(\mathrm{Sol}_{R_B,n}\) has an \(\varepsilon\)-model in \(U(d)\) iff \(B\)
     has one.
2. **(Equivalence.)** The following are equivalent:
   - (A) some translation-invariant binary linear rule \(R\) on \(\mathbb Z^2\) has
     \(J\ne1\) in \(\mathrm{Sol}_R\) and a torus-uniform gap: \(\varepsilon>0\) and
     \(n_0\) with no \(\varepsilon\)-model of \(\mathrm{Sol}_{R,n}\) for \(n\ge n_0\);
   - (B) some finite binary linear system is tracially satisfiable but not
     \(\mathcal R^{\mathcal U}\)-satisfiable;
   - (C) there is a finitely presented nonhyperlinear group.

So `translation-invariant-lcs-with-uniform-torus-gap-exists` is equivalent to the
existence of a finitely presented nonhyperlinear group. Translation invariance
neither adds a mechanism nor removes one: a torus-uniform rigidity argument for
some rule is exactly a finite linear-system gap in disguise.

(C)\(\Rightarrow\)(B) is the imported Paddock--Slofstra equivalence;
(A)\(\Rightarrow\)(C) is part (4) of the periodization claim. The new content is
the elementary stacking dictionary and (B)\(\Rightarrow\)(A). No novelty is claimed.

Proof: `translation-invariant-torus-gap-equivalence-proof`.
