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

## 7. THEOREM 6 (block invariance)

**Setting.**

- `1 -> N -> G -> Q -> 1`, with `N` infinite Kazhdan and finite symmetric
  generating set `S`.
- Every homomorphism `Q -> S_U` is trivial.
- `sigma_n : G -> Sym(X_n)` is a sofic approximation.

**Conventions.**

- `f_n = o(X)` means `f_n / |X_n| -> 0` along `U`.
- By Kun's theorem (`kun-expander-decomposition-formalized`, on the prescribed
  generating set `S`), editing `o(X)` edges of the `S`-graphs of `sigma_n|N`
  makes them a disjoint union of blocks `B`, each with Cheeger constant at least
  `h > 0`: `|E_S(A, B \ A)| >= h |A|` for `A ⊂ B` with `|A| <= |B|/2`.
- Put `L = max over s in S of the word length of g^-1 s g` and of `g s g^-1`,
  and `K = max over s of |{x : sigma(g)sigma(s)x != sigma(gsg^-1) sigma(g) x}|`
  summed appropriately. All these defects are `o(X)`.

**Claim.** For every `g` and `eps > 0`, the blocks with
`|sigma(g)B Δ B| > eps|B|` have total size `o(X)`.

*Step 1 (almost invariance of images).* For `s in S`, write `g^-1 s g` as a
word `w_s` of length at most `L`. Since `sigma` is an asymptotic homomorphism,
`sigma(s)sigma(g)x = sigma(g) sigma(w_s) x` off `o(X)` points. Letter by letter,
`sigma(w_s)` moves at most `L` times the edited boundary of `B`, plus
approximation error. Summing over blocks, the total `S`-boundary
`e(B) = sum_s |sigma(s)A Δ A|` of `A = sigma(g)B` is `o(X)`.

*Step 2 (almost invariant sets are unions of blocks).* Let `C` have `S`-boundary
`e(C)` in the edited graph, and let `B'` be a block. The boundary of `C cap B'`
inside `B'` is at most the part of `e(C)` in `B'`. Cheeger then gives

```text
min(|C cap B'|, |B' \ C|) <= e_(B')(C) / h.
```

*Step 3 (one block).* `A = sigma(g)B` with generators `gSg^-1` is isomorphic,
through `sigma(g)` and off `o(X)` points, to `B` with generators `S`. So it has
Cheeger constant about `h` for `gSg^-1`. Let `C = A cap B'` for a block `B'`
that `A` meets in at least half of `B'`. By Step 2, `C` is almost `S`-invariant.
Each element of `gSg^-1` is a word of length at most `L` in `S`, so the
`gSg^-1`-boundary of `C` is at most `L` times its `S`-boundary, plus
approximation error. Expansion of `A` then forces `|C| ≈ 0` or `|C| ≈ |A|`.
Both approximations are relative to `|A|`, with total error `o(X)` by a Markov
count over blocks. So on most blocks, one block `B' = beta_g(B)` satisfies
`|sigma(g)B Δ B'| <= eps|B|`, and `||B'| - |B|| <= eps|B|`.

*Step 4 (the quotient representation).*

- `beta_(gn)(B) = beta_g(B)` for `n in N` on most blocks, since `sigma(n)B ≈ B`
  by Step 2 applied to words in `S`.
- `beta_(gh) = beta_g beta_h` on most blocks.
- Fix an ordering of each block. Define `tau_n(q)` for `q = gN` by sending the
  `k`-th point of `B` to the `k`-th point of `beta_g(B)` for
  `k <= min(|B|, |beta_g(B)|)`, and complete arbitrarily to a permutation.
- Off `o(X)` points, `tau_n(q q')` agrees with `tau_n(q) tau_n(q')`: both send
  `B` to the same block, and order-preserving maps compose. So `tau` is a
  homomorphism `Q -> S_U`.

*Step 5.* By hypothesis `tau` is trivial, so `tau_n(q)` fixes all but `o(X)`
points. A point of `B` is fixed only if `beta_g(B) = B`. Hence
`|sigma(g)B Δ B| <= eps|B|` on most blocks. ∎

**Fixed-algebra form.** Kun--Thom Lemma 2.3 identifies `D_U^(sigma(N))` with the
block algebra, and Theorem 6 says `sigma(G)` fixes it. So
`D_U^(sigma(G)) = D_U^(sigma(N))`.

**For the Leavitt cover.** `Q = R^x` is simple, so a nontrivial homomorphism
`R^x -> S_U` is injective. For `q != 1`, the element `tau(q)` then has trace
less than `1`, and tensor amplification gives a trace-zero embedding, so `R^x`
would be sofic. So `tau` is trivial.

**Consequence for OPEN A.** Every G-invariant partition or orbit datum of a
sofic approximation of the cover is already N-invariant. The relative defect
`[u_hat z u_hat^-1, gamma] not in N` has to be detected inside one
N-expander block, where elements of `N` and of `G \ N` alike act freely and `N`
is ergodic.

## 7b. Finite quotients of the cover (THEOREM 7)

Node: `leavitt-cover-finite-quotients-split-over-the-kernel`.

- **Outer action.** `G` is torsion-free (Belegradek--Osin Corollary 1.2 with a
  torsion-free source) and `N` is non-elementary. So `C_G(N) = 1`, and
  `R^x` embeds in `Out(N)`.
- **Splitting.** For every `L <= N` normal in `G` of finite index in `N`, the
  outer action of `R^x` on `N/L` is trivial, by simplicity. The central
  extension `C_(G/L)(N/L)` of `R^x` splits, because Khanh Theorem 4.4 gives
  `H_1 = H_2 = 0`. This gives `G/L = N/L x K_L` with a unique complement.
- **Consequences.**
  - The finite quotients of `G` are exactly the `N/L`.
  - The profinite completion of `G` equals the completion of `N` along the
    `G`-invariant finite-index subgroups.
  - `G` is residually finite iff the canonical inner realizers
    `g -> (N/L-coordinate of g)_L` separate `G`.
- **For RDD.** In every finite model, the relative defect lands in the image of
  `N`. RDD for this host is therefore at least as strong as non-residual
  finiteness of `G`.

## 8. Relation to other lanes

- `hyperbolic-rf`: Theorem 1 gives a hyperbolic Kazhdan group all of whose
  finite images are already images of a Kazhdan normal subgroup of infinite
  index. Whether this `G` is residually finite is open.
- `hs-stable` / `hs-unstable`: the hyperlinear analogue of RDD, with `M`
  Kazhdan, would make `G` non-hyperlinear by the same contraposition.
  `hyperlinear-groups-kill-rigid-compression-defects` is its `M = 1` case.
