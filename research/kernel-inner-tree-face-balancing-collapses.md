---
rg: 2
id: kernel-inner-tree-face-balancing-collapses
kind: claim
title: Independent kernel conjugations of the two tree faces collapse to one global conjugation in an A2-A2 Kac-Moody triangle
distinct_from:
  three-face-ucp-balancing-needs-macroscopic-tree-motion: that gives a norm floor around the canonical tree-face lift but allows arbitrary macroscopic movement; this rules out a macroscopic noncanonical class, namely independent inner conjugations of the two tree faces by relator-kernel elements.
  kernel-relator-forces-two-edge-ucp-section-gap: that treats a closing-face ucp section with canonical edge lifts; this first uses Bass-Serre centralizer rigidity to show that two apparently independent moved tree-face embeddings are globally conjugate, and only then invokes the cycle gap.
  position-window-ucp-sections-collapse-to-folner-vectors: that rules out position-indexed window formulas through the trivial character; this rules out facewise inner kernel gauges through a self-normalizing amalgam edge, with no window or coefficient formula.
  triangle-relator-extension-admits-local-ucp-sections: that permits arbitrary ucp restrictions on all three finite faces and remains open; this proves only that a successful restriction on at least one tree face must be genuinely nonmultiplicative, rather than a conjugate of the canonical face embedding.
---

**ESTABLISHED (a noncanonical balancing no-go).**  There is an explicit
rank-three Kac--Moody instance for which simultaneous triangular balancing
cannot be obtained by independently conjugating the two canonical tree-face
embeddings inside the relator kernel.

Take the generalized Cartan matrix

```text
A = [[ 2, -1, -1],
     [-1,  2, -1],
     [-2, -1,  2]].                                      (IK1)
```

Its Coxeter labels are `(m_12,m_23,m_13)=(3,3,4)`, its determinant is `-3`,
and every rank-two subdiagram is spherical.  Thus it is indecomposable,
2-spherical, nonspherical and nonaffine.  For a prime power
`q>1764^3`, Caprace--Remy's theorem used in
`simple-kazhdan-kac-moody-lattices-exist` supplies the corresponding
infinite finitely presented simple Kazhdan quotient `Lambda`.

Use its rank-`<=2` triangle presentation and write

```text
G_0=P_12 *_(P_2) P_23,       K=ker(G_0 ->> Lambda),
A_0=C^*(G_0),                S_Delta=C^*(P_12)+C^*(P_23)+C^*(P_13).
                                                               (IK2)
```

The two vertex groups adjacent to `P_2` have type `A_2`.  The standard
rank-one subgroup containing the common torus is self-normalizing in each:

```text
N_(P_12)(P_2)=P_2=N_(P_23)(P_2).                       (IK3)
```

One quick verification of `(IK3)` uses the rank-two `BN`-pair.  The Weyl
group is `S_3`; the stabilizer of the root subsystem `{+-alpha_2}` is exactly
`<s_2>`.  Hence an element normalizing the standard rank-one Levi lies in
the inverse image of `<s_2>`, which is that Levi itself.  Passing through
the finite central quotient does not change the assertion because the
centre lies in the common torus.

Let `i_12,i_23` denote the canonical face embeddings in `A_0`.  There do not
exist `k_12,k_23 in K` and a ucp map `Phi:S_Delta->A_0` satisfying

```text
Phi|_(C^*(P_12)) = Ad(u_(k_12)) o i_12,
Phi|_(C^*(P_23)) = Ad(u_(k_23)) o i_23.                 (IK4)
```

Indeed, the Bass--Serre tree of `(IK2)` has an edge `e` with stabilizer
`P_2`.  By `(IK3)`, `e` is the unique edge adjacent to either endpoint that
is fixed by `P_2`; connectedness of a fixed subtree then gives

```text
T^(P_2)=e,                  C_(G_0)(P_2) <= P_2.         (IK5)
```

The two formulas in `(IK4)` agree on the shared algebra `C^*(P_2)`.  Equality
of its group unitaries implies

```text
k_23^(-1) k_12 in K cap C_(G_0)(P_2).
```

Every finite face embeds in `Lambda`, so `K cap P_2={1}`.  Equation `(IK5)`
therefore forces `k_12=k_23=:k`.  Consequently
`Psi=Ad(u_k^*) o Phi` is ucp and is canonical on **both** tree faces.  For a
nontrivial reduced kernel cycle `n=a_1...a_L` with
`a_j in P_1 union P_3`, all its closing-face letters are simultaneously
tree-face letters, so

```text
Psi(u_(q_E(a_j)))=u_(a_j)       for every j.
```

This contradicts `three-face-ucp-balancing-needs-macroscopic-tree-motion`,
which says that one of these values has norm displacement at least `2/L^2`.

**Exact scope and positive residue.**  This is stronger than the perturbative
canonical no-go: the two conjugators may be arbitrary long kernel words and
the movement may have norm two.  But it does not refute local ucp splitting.
A successful triangular balance can still move the face orders by genuinely
nonmultiplicative ucp maps.  In particular, the surviving finite-relator
reservoir problem is now sharper: its correction cannot merely implement
independent inner gauges on `P_12` and `P_23`; at least one corrected tree-face
restriction must leave the multiplicative domain.

DERIVATION
bass-serre-edge-rigidity-kills-independent-kernel-gauges
