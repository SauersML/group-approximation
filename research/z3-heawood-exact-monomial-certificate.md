---
rg: 2
id: z3-heawood-exact-monomial-certificate
kind: route
title: A class-three 3-quotient, induced from a self-centralizing abelian normal subgroup, verified by exact monomial arithmetic
target: z3-heawood-incidence-system-has-a-finite-dimensional-solution
requires: []
artifacts:
  - experiments/odd-p-incidence-pquotient-2026-09-17/verify_monomial.py
  - experiments/odd-p-incidence-pquotient-2026-09-17/heawood_p3_monomial.json.gz
  - experiments/odd-p-incidence-pquotient-2026-09-17/pq.g
  - experiments/odd-p-incidence-pquotient-2026-09-17/reduce.g
  - experiments/odd-p-incidence-pquotient-2026-09-17/monomial.g
  - experiments/odd-p-incidence-pquotient-2026-09-17/minor.g
  - experiments/odd-p-incidence-pquotient-2026-09-17/RESULTS.md
---

## Item 1

Every column of the oriented incidence matrix has one `+1` and one `-1`, so
summing all vertex equations gives `0 = sum_v b_v = 1` in `Z_3`, which is
impossible.

## Item 2 (exact certificate)

The file `heawood_p3_monomial.json.gz` lists 22 monomial matrices of size
`n=6561`: one for each of the 21 edges, in the order stated in the claim, and
one for `J`.  Each matrix is a permutation `pi` of `{0..n-1}` together with
phases `c_i in Z_3`, acting by `e_i -> zeta_3^{c_i} e_{pi(i)}`.  Such a matrix
is unitary.  Products, inverses and scalar tests are exact integer operations.

`verify_monomial.py` rebuilds the Heawood graph and its orientation from
scratch and checks:

- the `J` matrix is the scalar `zeta_3^2`, a primitive cube root of unity;
- `X_e^3 = I` for every edge;
- `X_e X_f = X_f X_e` for every pair of edges meeting at a vertex;
- the ordered vertex products equal `J^{b_v}`.

Usage (under a second of CPU): `gunzip -k heawood_p3_monomial.json.gz;
python3 verify_monomial.py heawood_p3_monomial.json heawood 3`.  Output:
`OK: heawood, p=3: exact operator solution in dimension 6561; ...`.  As a
negative control, changing a single phase makes the script fail with
`X_0^p != I`.

The certificate is induced from a linear character of an abelian subgroup,
so no step of the verification depends on GAP.

## How the certificate was found (item 3)

1. `pq.g` builds the finitely presented `Gamma_3(H,delta_0)`.
   `EpimorphismPGroup(Gamma,3,c)` computes its largest 3-quotient of class
   `<=c`.  For `c=1,2` the image of `J` is trivial.  This is forced by
   `lcs-phase-dies-in-every-nilpotent-quotient-of-class-below-p`.  For `c=3`
   the quotient has order `3^79` and the image of `J` is nontrivial.
2. `reduce.g` repeatedly factors out a hyperplane of `Omega_1(Z)` avoiding
   `J`, where `Z` is the centre.  This leaves a quotient `P` of order `3^17`
   with centre `<J>` of order 3, nilpotency class 3 and exponent 9.  The script
   re-evaluates every relator of `Gamma` on the images and confirms that all
   of them hold.
3. `monomial.g` grows an abelian normal subgroup `A` (order `3^9`) until it
   is self-centralizing.  It then picks a linear character `chi` with
   `chi(J)` primitive and writes the induced representation `Ind_A^P chi` in
   monomial form.  Since `J` is central, it acts by the scalar `chi(J)`.

## Item 4 and minor monotonicity

`run_p3.g` and `run_batch_more.g` rerun step 1 for the other graphs.  The
survival of `J` in item 4 gives a finite quotient in which `J` survives, by
construction of the epimorphism.  Its non-survival for `K_{4,4}` and Petersen
is a statement about the quotients of class `<=4` (for `K_{4,4}`, `<=5`)
only.

**Minor monotonicity** (elementary).  Let `G` be connected.

- *Deleting* an edge `e`: the map `x_e -> 1` (other generators fixed) is a
  surjection `Gamma_p(G,b) -> Gamma_p(G-e,b)`.
- *Contracting* `e=(u->w)`: define
  `x_e -> (prod_{f at w, f!=e} x_f^{sigma(w,f)})^{-1} J^{b_w}`, fixing every
  other `x_f` and `J`.  This is a surjection
  `Gamma_p(G,b) -> Gamma_p(G/e,b')`, where `b'` puts `b_u+b_w` on the merged
  vertex and loops are sent to 1.
  - The image of `x_e` lies in the abelian vertex group of the merged vertex,
    so it has order `p` and commutes with every edge at `u` or `w`.
  - The relation at `w` holds by definition.
  - The relation at `u` becomes the merged relation times `J^{-b_w}`.

Right-hand sides can be moved along edges by `x_f -> x_f J^k`, so one may
keep them on surviving vertices.  Both maps fix `J`.  Hence survival of `J`,
whether in `Gamma_p` itself, in a finite quotient or in a `p`-quotient of
class `<=c`, passes from a minor to the graph.  Greedy minimisation (`minor.g`)
calibrates correctly at `p=2`, where it ends at `K_{3,3}`.  At `p=3`, starting
from Heawood, it reaches an 11-vertex, 17-edge minor that still survives at
class 3.
