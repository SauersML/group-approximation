---
rg: 2
id: km-l0-three-subspace-proof
kind: route
title: Building isotropy collapse, polygon-cycle vanishing, and the relation-space isomorphism
target: km-l0-h2-is-the-three-subspace-defect
requires:
  - locally-finite-bernoulli-first-l0-cohomology-nonzero
  - simple-kazhdan-kac-moody-lattices-exist
---

Full derivation: artifact Addendum 13; the steps are as follows.

(a) `X_-` is contractible with type-preserving `Lambda`-action and
one chamber quotient; all stabilizers are locally finite (finite
Levi extension of the locally finite unipotent radical), and for
divisible `V`, Milnor + finite-subgroup vanishing give
`H^q(locally finite, V) = 0` for `q >= 2`.  So on the degree-two
diagonal the `(0,2)` entry vanishes identically, and the `(2,0)`
entry is `H^2(Delta^2; R) = 0` because every parabolic acts
ergodically on the Bernoulli shift (restriction of Bernoulli to an
infinite subgroup is mixing), making all invariants constant.

(b) Restrictions to `B_-` are injective (`[P_K^- : B_-]` is the
finite chamber count of the K-residue; cores o res = index;
divisibility), with Cartan--Eilenberg stable images `St_K`.  For a
vertex pair: the five-term sequence of `P_j^- *_(B_-) P_k^- ->>
P_jk^-` (free Bass--Serre kernel `N`, acting trivially on `V`,
`H^2(P_jk^-, V) = 0`) identifies `(St_j cap St_k)/St_jk` with
`Hom(N, V)^(P_jk^-)`.  `N^ab = H_1` of the parabolic coset graph,
which is the rank-two polygon incidence graph of the finite Levi
(the radical is contained in every group in sight, hence acts
trivially on the graph); equivariance under the radical forces
values into `V^(radical) = R` (mixing again), leaving Levi-invariant
rational cycles; the Levi is flag-transitive, the invariant edge
space is spanned by the all-ones vector, and its boundary is nonzero
in a `(q+1)`-biregular bipartite graph.  So the Hom-space is zero.

(c) In the `E_2^(1,1)` complex, identify all groups with their
stable images; the relation space maps onto `((St_1 + St_2) cap
St_3)` by projection to the third coordinate, with kernel exactly
the `{1,2}`-vertex diagonal (using (b)); quotienting by the other
two vertex diagonals yields the stated defect module.

(d) `P_13^-` and `P_23^-` generate `Lambda` (their Levis contain
all `U_(+-alpha_i)`), the amalgam kernel `N_3` is free (vertex
groups embed), Mayer--Vietoris computes `H^2` of the amalgam as
`St_3/(St_13 + St_23)` (using `H^2(P^-, V) = 0`), and the five-term
sequence for `Lambda = Gamma_3/N_3` gives the stated extension;
`N_3^ab` is `H_1` of the corresponding coset graph, which is the
cotype-3 subgraph of `X_-`.
