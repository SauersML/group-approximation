# RC3 standard-tools failure audit

Former Cairn claim `rc3-standard-tools-all-fail-audit`, demoted because it is
a falsification/status audit rather than a proposition used by a route.

Target `(RC3)`: for `A = L(SL_3(Z)) subseteq B = L(SL_3(Z[1/2])) subseteq M`
(matrix ultraproduct, regular trace), `A' cap M subseteq B' cap M`;
equivalently, with `h = diag(2,1,1/2)`, every `k in A' cap M` commutes with
`pi(h)`. Four standard tools were each pushed to their failure point.

1. **Property (T) as `H^1`-vanishing (cocycle) -- FAILS, vacuously.**
   The orbit map `g |-> alpha_g(k) = pi(g) k pi(g)^*` gives a 1-cocycle
   `c(g) = alpha_g(k) - k` for the conjugation representation on `L^2(M)`,
   with `c|_{SL_3(Z)} = 0`. Property (T) gives `H^1 = 0`, so `c` is a
   coboundary -- but `c = partial k` is ALREADY the coboundary of `k`, so
   `H^1`-vanishing is automatic and yields nothing. The orbit cocycle is
   trivially exact; (T) in this form is empty here.

2. **Property (T) as spectral gap -- FAILS, wrong quantifier.**
   `(RC3)` compares the exact fixed-point spaces of two nested subgroups:
   `A' cap M cap L^2` (= `SL_3(Z)`-fixed) versus `B' cap M cap L^2`
   (= `SL_3(Z[1/2])`-fixed). Spectral gap controls ALMOST-invariant vectors,
   not the relation between two spaces of EXACTLY invariant vectors of nested
   subgroups. A vector fixed by the subgroup generates an isolated trivial
   subrep; (T) isolates it but does not forbid it, so `SL_3(Z)`-fixed
   vectors orthogonal to `B' cap M` are not excluded. `(RC3)` is exactly the
   statement that the conjugation rep on `L^2(M) ominus (B' cap M)` has no
   `SL_3(Z)`-invariant vector, which (T) does not deliver.

3. **1-bounded entropy -- FAILS, constrains size not absorption.**
   `SL_3(Z)` commensurated implies `B` and `A' cap M` lie in
   `W^*(wqN_M(A))`, which has `h = 0` (Hayes monotonicity; Jung's
   `h(L(SL_3(Z))) = 0`). So `A' cap M` is strongly 1-bounded and contains no
   free-group factor. But `h = 0` is consistent with an amenable extension
   `B <= <B, k>` for `k in A' cap M setminus B' cap M`, so the entropy
   invariant does not force the absorption.

4. **Co-density -- FAILS, about finite quotients not ultraproduct vectors.**
   `SL_3(Z)` surjects onto every finite quotient of `SL_3(Z[1/2])`, so in
   any GENUINE finite-dimensional `rho`, `rho(SL_3(Z))' = rho(SL_3(Z[1/2]))'`.
   But `M` is a limit of APPROXIMATE finite-dimensional representations; a
   `k in A' cap M` need not be a limit of genuine-representation commutants,
   and co-density says nothing about `L^2`-vectors of the ultraproduct that
   are not so approximable. This is precisely the non-hyperfinite gap.

**The exact residue.** `(RC3)` is equivalent to: the expanding
commensuration `Ad(h)` fixes the strongly-1-bounded space `A' cap M`
pointwise. In the hyperlinear scenario it demonstrably does NOT
(`Ad(h)(u_t) = u_{h t h^{-1}} != u_t`, since `t` centralizes `SL_3(Z)` but
not `h`), so proving `(RC3)` for all embeddings rules out that scenario --
`(RC3)` is the non-hyperlinearity, restated at the II_1-factor level. Closing
it needs a genuine deformation/rigidity or 1-bounded-entropy ABSORPTION
theorem (Peterson--Thom-conjecture flavour) for a commensurated property-(T)
arithmetic inclusion in a matrix ultraproduct, which is not in the
literature.

## Attempts

- All four rows above are the attempts; each is complete and its failure
  point is exact. The productive residue is row 3's absorption question, the
  only one where current technology (Hayes--Jekel--Kunnawalkam Elayavalli
  1-bounded-entropy absorption) is even the right shape.
