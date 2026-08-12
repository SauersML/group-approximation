# Metric cone repair on the spherical building

Date: 2026-08-11

## Outcome

The cone argument of Dinur--Meshulam admits a metric strengthening which is
not stated in their support-norm theorem.  Let

```text
X=A_3(F_q)
```

be the order complex of the nonzero proper subspaces of `F_q^4`.  If `G` is
any group with a bi-invariant metric `d`, then every `G`-valued edge cochain
`phi` admits a vertex gauge `psi` such that, for every `1<=p<infinity`,

```text
(sum_e c(e) d((psi.phi)(e),1)^p)^(1/p)
 <=9 (sum_tau c(tau) d(d^1 phi(tau),1)^p)^(1/p).       (MGL1)
```

The constant is independent of `q`, of `G`, and of the size of a
representation of `G`.

In particular, for `G=U(n)` with normalized Hilbert--Schmidt distance,

```text
inf_(psi_v in U(n))
 (sum_e c(e)||psi_u phi_e psi_v^*-1||_2^2)^(1/2)
 <=9 (sum_tau c(tau)||phi_uv phi_vw phi_wu-1||_2^2)^(1/2).  (MGL2)
```

Thus the spherical building has dimension-free nonlinear unitary cocycle
repair, not only support cover stability.  For permutation coefficients the
same argument gives a fixity-free estimate in the **sheetwise Hamming edit
metric**: average sheet-edge repair is at most nine times average triangle
Hamming defect.  This is not the all-or-nothing base-edge metric used in the
published cover-stability corollary.

This is a strong standalone robust-repair theorem.  It does not solve the
main problem: the current projective cellular charts use `P^2(F_p)` and a
stabilizer resolution, not the simply connected `A_3(F_q)` order complex.
The theorem identifies an exact possible bridge: factor the projective
carry system through uniformly bounded geometric-lattice cone patches.

Primary source for the cone family and its exact counts:
Dinur--Meshulam, *Near Coverings and Cosystolic Expansion -- an example of
topological property testing*,
[arXiv:1909.08507](https://arxiv.org/abs/1909.08507), Theorem 8 and Figure 1.

## 1. Metric cochains

Let `X` be a finite pure two-dimensional simplicial complex with the usual
probability weights `c(e)` and `c(tau)`.  Give every unoriented edge one
orientation.  A `G`-valued one-cochain satisfies

```text
phi(v,u)=phi(u,v)^(-1).                                (MGL3)
```

For an oriented triangle `tau=(u,v,w)`, put

```text
curv_phi(tau)=phi(u,v)phi(v,w)phi(w,u).                (MGL4)
```

A zero-cochain acts by

```text
(psi.phi)(u,v)=psi(u)phi(u,v)psi(v)^(-1).              (MGL5)
```

Bi-invariance makes `d(curv_phi(tau),1)` independent of orientation and
gauge.  Define

```text
||phi||_(p,1)^p=sum_e c(e)d(phi(e),1)^p,
||curv phi||_(p,2)^p=sum_tau c(tau)d(curv_phi(tau),1)^p. (MGL6)
```

## 2. Quantitative cone lemma

Suppose a probability space of cone choices `s` assigns to every edge `e`
a triangulated disk `Y_s(e)` and a gauge `psi_s` with the following
properties.

1. `(psi_s.phi)(e)` is the boundary holonomy of `Y_s(e)`.
2. Every disk contains at most `M` triangular faces.
3. With

   ```text
   delta_s(tau)=sum_(e:tau in Y_s(e)) c(e)/c(tau),
   D=max_tau E_s delta_s(tau),                         (MGL7)
   ```

   one has `D<infinity`.

**Theorem 1 (metric cone repair).**  Under these hypotheses, for every
`1<=p<infinity` there is a cone choice `s` such that

```text
||psi_s.phi||_(p,1)
 <=M^(1-1/p)D^(1/p)||curv phi||_(p,2).                 (MGL8)
```

**Proof.**  Peel the triangular disk from its boundary.  Interior oriented
edges cancel in inverse pairs, so its boundary holonomy is a product of
conjugates of the face curvatures, with each face used once.  The triangle
inequality and bi-invariance give

```text
d((psi_s.phi)(e),1)
 <=sum_(tau in Y_s(e)) d(curv_phi(tau),1).             (MGL9)
```

For nonnegative `a_1,...,a_m`, with `m<=M`, Holder gives

```text
(sum_i a_i)^p<=M^(p-1)sum_i a_i^p.                    (MGL10)
```

Multiply `(MGL9)^p` by `c(e)`, sum over edges, and average over `s`:

```text
E_s ||psi_s.phi||_(p,1)^p
 <=M^(p-1) sum_tau d(curv_phi(tau),1)^p
       E_s sum_(e:tau in Y_s(e)) c(e)
 =M^(p-1) sum_tau c(tau)d(curv_phi(tau),1)^p
       E_s delta_s(tau)
 <=M^(p-1)D ||curv phi||_(p,2)^p.                     (MGL11)
```

At least one `s` is no larger than the average.  Taking the `p`-th root
proves `(MGL8)`.  End proof.

The disk-peeling sentence is literal for the Dinur--Meshulam patch in
Figure 1.  Put

```text
J=a_0 join a_1 join a_2,       K=a_0 join a_1.        (MGL11a)
```

Its displayed seven-edge boundary is filled by the following nine ordered
chains:

```text
(a_2,a_0 join a_2,J),       (a_0,a_0 join a_2,J),
(a_0,K,J),                  (a_1,K,J),
(a_1,a_1 join a_2,J),       (a_2,a_1 join a_2,J),
(a_0,v_0,v_1),              (a_0,K,v_1),
(a_1,K,v_1).                                         (MGL11b)
```

Peeling this explicit disk expresses the boundary word as a product of
conjugates of these nine face words, each used once.  Degenerate vertex
coincidences delete faces and can only decrease the right side.

## 3. The uniform constant for `A_3(F_q)`

Dinur--Meshulam construct the gauges `psi_s` from linear orderings of the
atoms of the geometric lattice.  Their patch `Y_s(e)` has

```text
f_2(Y_s(e))<=9,                                      (MGL12)
```

so `M=9`.  Averaging the orderings by `GL_4(F_q)`, they prove

```text
max_tau E_s delta_s(tau)<=9,                         (MGL13)
```

so `D=9`.  Substitution in `(MGL8)` gives

```text
M^(1-1/p)D^(1/p)=9                                   (MGL14)
```

for every finite `p`, proving `(MGL1)`.

For `U(n)`, normalized Hilbert--Schmidt distance is bi-invariant, so `p=2`
gives `(MGL2)` with no dimension dependence.

For a permutation action on a finite set `S`, take

```text
d_Ham(g,h)=|{x:g x!=h x}|/|S|.                       (MGL15)
```

This is bi-invariant.  The triangle term in `(MGL1)` for `p=1` is exactly
the fraction of sheets on which the triangle equation fails, while the edge
term is exactly the fraction of sheet edges changed by the gauge.
Consequently, in this sheetwise metric, the repair estimate is

```text
edge Hamming distance to a genuine cover
 <=9 triangle Hamming deficiency,                    (MGL16)
```

without the factor involving the maximum number of fixed points of a
nonidentity coefficient.  Dinur--Meshulam define distance by charging one
unit whenever two entire matchings above a base edge differ, regardless of
how many sheets move.  Their theorem is therefore not literally improved in
its own metric.  The sheetwise Hamming theorem is a metric refinement:
their support-norm argument first replaces Hamming size by the indicator of
nonidentity, whereas `(MGL9)` retains it.

## 4. Why this does not yet close TRUE

There are two distinct mismatches with the current `SL_3(Z)` projective
program.

1. The finite coefficient set `P^2(F_p)` is the rank-two spherical
   building for `SL_3`, whereas the theorem uses the simply connected
   rank-three building `A_3(F_q)` for `SL_4`.
2. The projective carry complex includes stabilizer homology and an
   absolute-versus-relative integral closing map.  It is not merely the
   edge-to-triangle cochain complex of the building.

Thus `(MGL1)` cannot be cited as a decoder for the exported projective
matrix.  A valid application must construct a bounded chain comparison
which sends its carry rows into these cone patches and controls the
integral closing kernel.  This is exactly the layer left open by
`TRUE_ASH_RUDOLPH_PACKET_SCOPE_AUDIT.md`.

## 5. Relation to the other supplied papers

Kaufman--Oppenheim--Weinberger,
[arXiv:2411.02819](https://arxiv.org/abs/2411.02819), prove nonabelian
coboundary expansion for a different family of coset complexes.  Their
formal theorem fixes a finite coefficient group `Lambda` and requires the
residue characteristic to exceed `|Lambda|`; it is therefore not uniform
when `Lambda=Sym(N)` and `N` grows.  Their cosystolic input is uniform over
all groups, but the cohomology-vanishing step is not.  This prevents a
direct all-dimensions rounding theorem.

Becker--Lubotzky,
[arXiv:1809.00632](https://arxiv.org/abs/1809.00632), prove that an infinite
hyperlinear property-`(T)` group is not Hilbert--Schmidt stable.  This is
consistent with `(MGL2)`: the building theorem repairs one simply connected
finite cocycle complex, not arbitrary approximate representations of an
infinite property-`(T)` group.

Sinclair--Smith,
[arXiv:math/0111330](https://arxiv.org/abs/math/0111330), control a single
unitary which almost normalizes one fixed masa.  As recorded separately in
`TRUE_SINCLAIR_SMITH_MASA_PERTURBATION_AUDIT.md`, that theorem neither
selects a common masa for several generators nor fixes the residual phase
system.  It does not subsume `(MGL2)` or the remaining projective closing
problem.
