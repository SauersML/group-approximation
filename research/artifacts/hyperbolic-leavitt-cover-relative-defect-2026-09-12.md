# The hyperbolic Leavitt cover and rigid defects modulo Kazhdan kernels

Date: 2026-09-12. Lane `hyperbolic-sofic`. Everything marked THEOREM has a
complete proof below. The two OPEN statements are the hinges.

## 0. Where a defect can sit in a hyperbolic group

Two facts from the graph fix what can and cannot happen.

- **Absolute defects are dead.** In a hyperbolic `G`, the centralizer of a
  non-elementary subgroup is finite, and compressors normalize it
  (`hyperbolic-compression-centralizer-rigidity`). So
  `sofic-groups-kill-rigid-compression-defects` certifies nothing hyperbolic,
  whatever the rigid pair.
- **Soficity passes to subgroups, not to quotients.** A nonsofic quotient says
  nothing about the host.

That node left one thing open: whether hyperbolic groups admit strictly
compressing non-elementary subgroups at all. THEOREM 3 below shows they do,
even infranormal Kazhdan ones. The defect of such a configuration does not
vanish; it lives modulo a normal Kazhdan subgroup. So the missing
nonsoficity input is a **relative** criterion (OPEN A).

## 1. THEOREM 1 (hyperbolic Kazhdan cover)

Put `R = L_(F_2)(1,2)`. There is `1 -> N -> G -> R^x -> 1` with:

- `G` word-hyperbolic;
- `G` and `N` Kazhdan;
- `N` infinite;
- `phi(N) = phi(G)` for every finite image `phi`.

*Proof.* Belegradek--Osin (arXiv:math/0605553, abstract verbatim in
`belegradek-osin-rips-construction`): for non-elementary hyperbolic `H` and
finitely presented `Q` there is `1 -> N -> G -> Q -> 1` with `G` hyperbolic and
`N` a quotient of `H`. Choose:

- `H` a torsion-free cocompact lattice in `Sp(2,1)`, which is Kazhdan;
- `Q = R^x`, which is finitely presented by Khanh Theorem 6.1 and Kazhdan
  because `R^x = EL_D(R) ~= EL_9(R)`, Kazhdan by the nine-leaf configuration and
  `GL_9(R) = EL_9(R)`.

Then:

- `N` is Kazhdan as a quotient of `H`;
- `G` is Kazhdan as a Kazhdan-by-Kazhdan extension;
- `N` is infinite: otherwise `R^x` would be quasi-isometric to `G`, hence
  hyperbolic, but it contains Thompson's `V`, which contains `Z^2`;
- for a finite image, `phi(G)/phi(N)` is a finite quotient of the infinite
  simple group `R^x`, so it is trivial. ∎

## 2. THEOREM 2 (the Leavitt defect)

In the nine-leaf configuration (`Gamma = EL_alpha(R)`, `G_L = EL_D(R)`,
`J = V_(1000)`, compressors `u, v`), the pair `Gamma <= G_L` is rigid and
`[u j u^-1, gamma] != 1` for some `j in J` and `gamma in Gamma`. In particular
`Gamma` is not normal in `G_L`.

*Proof.*

- `[Gamma, J] = 1` and `u J u^-1 = V_(0001) <= Gamma`.
- If all the commutators vanished, `V_(0001)` would lie in `Z(Gamma)` and be
  abelian. It is isomorphic to `V`, which is not.
- A normal `Gamma` would have its centralizer normalized by all of `G_L`,
  which kills the defect. ∎

## 3. THEOREM 3 (infranormal Kazhdan pair in a hyperbolic group)

With `pi : G -> R^x` from Theorem 1, put `Gamma_hat = pi^-1(Gamma)` and
`G_hat = pi^-1(G_L)`. Then:

- **(a)** `Gamma_hat <= G_hat` are Kazhdan, `Gamma_hat` is infranormal and not
  normal in `G_hat`, and lifts of `u` compress strictly;
- **(b)** `D_G(G_hat, Gamma_hat) = 1`;
- **(c)** for any lift `z` of `j`: `[z, Gamma_hat] <= N`, but
  `[u_hat z u_hat^-1, gamma_hat]` is not in `N`;
- **(d)** `Gamma_hat` is not quasiconvex.

*Proof.*

- **(a)** Each group is a Kazhdan-by-Kazhdan extension. Compressors lift, the
  kernel `N <= Gamma_hat` compresses trivially, and the semigroup generated
  maps onto a generating set and contains `N`. Strictness and non-normality
  are read off in the quotient.
- **(b)** `Gamma_hat` contains the infinite `N`, so it is infinite Kazhdan,
  hence non-elementary. Its centralizer is finite and is normalized by the
  compressors, hence by `G_hat`.
- **(c)** Apply `pi`.
- **(d)** Every conjugate of `Gamma_hat` contains `N`, so all pairwise
  intersections are infinite. Quasiconvex subgroups have finite height
  (Gitik--Mitra--Rips--Sageev), so a quasiconvex `Gamma_hat` would have finite
  index, but its image `Gamma` has infinite index in `G_L`
  (`infranormal-nonnormal-has-infinite-compression-orbit`). ∎

## 4. OPEN A: rigid defects modulo Kazhdan kernels

**RDD.** For every countable sofic `H`, every normal Kazhdan `M <= H`, and
every rigid pair `M <= Gamma <= G <= H`: if `[z, Gamma] <= M`, then
`[g z g^-1, gamma] in M` for all `g in G` and `gamma in Gamma`.

- **Equivalent form:** quotients of sofic groups by normal Kazhdan subgroups
  have trivial rigid defect. Rigid pairs of `H/M` lift to rigid pairs
  containing `M`, and `zM` centralizes `Gamma/M` iff `[z, Gamma] <= M`.
- **`M = 1`** is the established absolute criterion.
- **COROLLARY 4.** RDD implies that the Leavitt cover `G` is not sofic. By
  Theorem 3(c), its relative defect is nontrivial. So some word-hyperbolic
  Kazhdan group is not sofic, and hence not residually finite.
- **COROLLARY 5 (win--win).** Either some hyperbolic group is not sofic, or the
  sofic hyperbolic group `G` refutes RDD with `M = N`.

## 5. OPEN B: quotient permanence

**QP.** If `H` is sofic and `M <= H` is normal and Kazhdan, then `H/M` is
sofic. QP implies RDD, through the absolute criterion applied to `H/M`.

- Without (T) on `M`, QP is false: `F_n -> R^x`.
- If all hyperbolic groups are sofic, Theorem 1 refutes QP.

## 6. What the natural attacks give

1. **Normalization modulo `M`.** For a sofic representation `sigma` of `H`,
   Kun--Thom Theorem 4.1 for the pair `Gamma <= G` (which contains `M`) gives
   `sigma(G)` normalizing `C(sigma(Gamma))`. The relative centralizing element
   `z` commutes with `sigma(Gamma)` only up to `sigma(M)`. After the
   `o(|Y_n|)` edge edit of Kun--Thom Lemma 2.3, the `M`-fixed algebra is a
   block algebra. A proof of RDD would follow from correcting `sigma(z)` by a
   blockwise permutation `w` so that `sigma(z) w` commutes with
   `sigma(Gamma)`. That is a conjugacy problem between two expander actions of
   `Gamma` on each block, differing by an `M`-valued cocycle. No uniqueness
   statement for such conjugacies is known here. OPEN; this is the hinge.
2. **Fixed algebras.** Kun--Thom Theorem C for pairs containing `M` restricts
   to fixed-algebra rigidity for the `H/M`-action on the `M`-invariant factor.
   But that action need not be free. For the Leavitt cover, in every
   finite-quotient model `N` acts transitively on each orbit of `G`, so `R^x`
   acts trivially on the factor. Corollary D needs freeness, so nothing
   follows. DEAD as a direct route.
3. **Canonical-trace blindness.** In a trace-preserving model of `H`,
   `tr(sigma(w)) = 0` for every nontrivial word `w` in `M`, so the spectral
   measure of the Laplacian `sum_s (1 - Re sigma(s))` over a generating set of
   `M` equals that of `lambda_M`. Since `M` is infinite and Kazhdan, the
   measure has a gap at `0` and no atom there. So the Kazhdan projection has
   trace `0`: `H/M` acts on no nonzero corner of the tracial ultraproduct. Any
   proof of QP or RDD must discretize the diagonal side. RECORDED as a
   constraint.
4. **Finite quotients.** Theorem 1's last clause says every finite image of
   `G` is the image of `N`. So residual finiteness of `G`, which is open, would
   give sofic approximations of `G` in which `R^x` is invisible. This is
   consistent with both answers.

## 7. Relation to other lanes

- `hyperbolic-rf`: Theorem 1 gives a hyperbolic Kazhdan group all of whose
  finite images are already images of a Kazhdan normal subgroup of infinite
  index. Whether this `G` is residually finite is open.
- `hs-stable` / `hs-unstable`: the hyperlinear analogue of RDD, with `M`
  Kazhdan, would make `G` non-hyperlinear by the same contraposition.
  `hyperlinear-groups-kill-rigid-compression-defects` is its `M = 1` case.
