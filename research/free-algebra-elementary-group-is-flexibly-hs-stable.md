---
rg: 2
id: free-algebra-elementary-group-is-flexibly-hs-stable
kind: claim
title: For some n >= 3 and k >= 4, the elementary group E_n of the free algebra on k generators over Z or over F_p is flexibly Hilbert--Schmidt stable
distinct_from:
  el-r-polynomial-vertex-not-flexibly-hs-stable: that asks for instability of EL_r over a commutative polynomial ring; this asks for stability of E_n over a free algebra. The two are in tension through the retract E_n(F_p<x_1..x_k>) -> SL_n(F_p[t]), recorded under Attempts.
  rf-kazhdan-group-not-flexibly-hs-stable: that is an explicit residually finite Kazhdan group without flexible stability; this asks for flexible stability of another residually finite Kazhdan group, where the scalar-cocycle engine of that proof has no stable data.
  infinite-hyperlinear-kazhdan-group-is-not-hs-stable: that excludes strict, same-dimension stability for every infinite hyperlinear Kazhdan group, so it excludes the strict form of this claim; this asks only for flexible stability, with padding allowed.
  universal-lattice-flexible-stability-forces-nonhyperlinear-group: that derives a non-hyperlinear group from this claim; this is the stability hypothesis itself.
---

**OPEN.** Let `A` be `Z` or `F_p` for a prime `p`. The claim is that for some `n >= 3` and `k >= 4`,

```text
Γ = E_n(A<x_1, ..., x_k>)
```

is flexibly Hilbert--Schmidt stable in the Dogon--Vigdorovich sense:

- for every asymptotic representation `σ_m : Γ -> U(d_m)` in normalized HS norm,
- there are genuine representations `λ_m : Γ -> U(D_m)` with `D_m >= d_m` and isometries `P_m`,
- such that `||σ_m(g) - P_m* λ_m(g) P_m||_2 -> 0` for every `g`.

The ratio-one form, with `D_m/d_m -> 1`, is stronger and also suffices.

`Γ` is a residually finite Kazhdan group:
- it is Kazhdan by `ershov-jaikin-kassabov-steinberg-groups-have-property-t`;
- it is residually finite by `universal-lattice-stability-nonhyperlinear-proof`, Step 5.

**Why it matters.** By `universal-lattice-flexible-stability-forces-nonhyperlinear-group`, this claim
makes `E_n(L_(F_q)(1,2))` a non-hyperlinear group, with `q = 2` over `Z` and `q = p` over `F_p`.
That is the only open prerequisite of the goal route
`nonhyperlinear-via-free-algebra-lattice-flexible-stability`.

## Attempts

- **Necessary conditions through retracts (elementary; 2026-09-17, `swarm-0917-w23-w23-nh-last1`).**
  - `x_1 -> t`, `x_j -> 0` for `j >= 2` retracts `A<x_1..x_k>` onto the subring `A[x_1] = A[t]`,
    and `t -> 0` retracts that onto `A`.
  - So `SL_n(A[t]) = E_n(A[t])` (when `A = F_p`) and `E_n(A)` are retracts of `Γ`.
  - Flexible stability, in either dimension regime, passes to retracts. For `r∘i = id`, round
    `σ∘r` on `Γ` and restrict along `i`: the correcting representations `λ∘i` have the same
    dimensions.
  - The ratio-one case is `flexible-hs-stability-descends-to-retracts-finite-index`.
  - Hence the claim at `(A, n)` **requires**:
    - `SL_n(Z)` and `E_n(Z[t])` to be flexibly HS stable when `A = Z`;
    - `SL_n(F_p[t])` to be flexibly HS stable when `A = F_p`.
  - **Collision with the Kun--Thom program.** `el-r-polynomial-vertex-not-flexibly-hs-stable`
    reduces to ratio-one instability of `SL_r(F_q[t])`, and both of its recorded rank-3 routes aim
    there.
    - Establishing either route at `q = p`, `r = n` kills the ratio-one form of this claim at
      `(F_p, n)`.
    - It kills the Dogon--Vigdorovich form only if the models it builds also fail to round with
      unbounded padding.
    - Conversely, this claim at `(F_p, 3)` would refute that vertex claim for `r = 3, q = p` in the
      Dogon--Vigdorovich sense.
    - The two programs are therefore mutually exclusive. Progress on either one is a test of the
      other.
- **Descent test (2026-09-17).** By `relative-elementary-quotients-inherit-flexible-hs-stability`,
  the claim makes every `Q_I = E_n(S)/E_n(S,I)` flexibly HS stable, where `S = A<x_1..x_k>` and `I` is
  a finitely generated ideal.
  - A single hyperlinear `Q_I` with a non-roundable asymptotic representation refutes the claim.
  - `Q_I` is a quotient of `St_n(S/I)` and maps onto `E_n(S/I)`, because
    `St_n(S) / <<x_ij(I)>> = St_n(S/I)`.
  - The kernel of `St_n(S/I) ->> Q_I` is the image of `K_2(n, S)`.
- **Scalar cocycles give no refutation at the stable level (remark, not a proof).**
  - Gersten: `K_2(F_p<X>) = K_2(F_p) = 0` and `K_2(Z<X>) = K_2(Z) = Z/2`.
  - So at the stable level `H^2(Γ; R) = 0`, and `Q_I` is the Steinberg group `St(S/I)` up to a
    finite kernel. That group is superperfect, so `H^2(Q_I; R) = 0`.
  - A real two-cocycle of `E(S/I)` pulled back to `Q_I` is a coboundary `dβ`. Twisting a
    projective model by `e^(-2πiβ/k)` makes it a genuine representation that is close pointwise.
  - So the Ioana--Spaas--Wiersma / Dogon mechanism used in `rf-kazhdan-group-not-flexibly-hs-stable`
    has no data, either on `Γ` or through the descent. Any refutation must be of another kind, for
    example the truncated-cover or extra-finite-quotient type recorded for `SL_3(F_q[t])`.
  - Homological stability of `K_2(n, -)` for free algebras at `n = 3` is not checked, so this
    remark is only for large `n`.
- **Laurent Steinberg decomposition (established pieces; 2026-09-20, `swarm-0917-w23-w23-nh-follow`).**
  - One relative quotient is identified exactly: for `I = (x_1x_2 - 1, x_2x_1 - 1, [x_1,x_3], [x_2,x_3], f(x_3), x_j (j >= 4), p)`,
    `Q_I ≅ St_n(F_q[t,t^-1])` (`free-algebra-relative-quotient-is-laurent-steinberg`, from
    `gersten-free-algebra-k-theory` and `laurent-unstable-k2-splits-by-tame-symbol`).
  - For `q >= 3` that group is finitely generated, Kazhdan, not residually finite, and of
    Deligne-type for `q` odd, with `ker_RF = K_2 = ⟨{t,a}⟩ ≅ Z/(q-1)`
    (`laurent-steinberg-groups-are-deligne-type`).
  - So this claim implies `laurent-steinberg-group-is-flexibly-hs-stable`
    (`laurent-steinberg-stability-from-free-algebra-stability`). That claim alone gives the goal
    through `nonhyperlinear-via-laurent-steinberg-flexible-stability`, with no Leavitt input.
  - **Sharper refutation screen.** Hyperlinearity of a single `St_n(F_q[t,t^-1])` with `q >= 3`
    refutes this claim at `(Z, n)`, and at `(F_p, n)` when `p | q`. Such a proof would be a
    positive-characteristic Deligne-cover hyperlinearity theorem.
- **Correction to the scalar-cocycle remark above.** The statement "any refutation must be of
  another kind" is right about scalar two-cocycles. But the obstruction to this claim that the
  descent exposes is a finite central kernel `K_2(n, F_q[t,t^-1]) = Z/(q-1)` that is invisible in
  finite quotients. That is not a real cocycle, and `H^2(Q_I; R) = 0` does not see it. The
  relevant test is the hyperlinearity of a Deligne-type cover, not cocycle rounding.
- **Why a proof is hard.** Any proof of this claim, by the target of its goal route, constructs a
  non-hyperlinear group.
  - So it cannot use only features shared with hyperlinear groups (property (T), residual
    finiteness, regular limit trace). Those do not force flexible rounding
    (`rf-kazhdan-group-not-flexibly-hs-stable`).
  - The strict form is false by `infinite-hyperlinear-kazhdan-group-is-not-hs-stable`, so padding
    is essential.
