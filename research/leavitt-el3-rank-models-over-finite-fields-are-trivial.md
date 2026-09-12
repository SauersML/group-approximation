---
rg: 2
id: leavitt-el3-rank-models-over-finite-fields-are-trivial
kind: claim
title: Rank models of EL_3 over a Leavitt algebra over a finite field are trivial in the field's characteristic
refuted_by:
  - binary-leavitt-unit-group-is-f2-linear-sofic
distinct_from:
  el3-rank-models-factor-through-ring-rank-models: that is the class statement over every simple characteristic-p ring without a ring rank model, which one linear sofic EL_3 over any such ring would refute; this is the single Leavitt instance over a finite field, where self-similarity R ~= R^n and known nonsoficity are available.
  matrix-unit-root-rank-models-of-simple-el3-are-trivial: that kills only the characteristic-two models whose unit root elements are block supported; this asserts that every model of the Leavitt instance is trivial.
  binary-leavitt-unit-group-is-f2-linear-sofic: that is the open positive gate for the binary unit group; this instance with K = F_2 and n = 2 would refute it, since EL_3(R) is an infinite subgroup of R^x.
artifacts:
  - research/artifacts/el3-rank-ring-rigidity-2026-09-12.md
---

**OPEN.** Let `K` be a finite field of characteristic `p`, `n >= 2` and `R = L_K(1,n)`. Every
homomorphism

```text
sigma : EL_3(R) -> M^x,     M = prod_omega M_(n_i)(k) / d_omega,  char k = p,
```

is trivial.

**Payoff.**
* `EL_3(R)` is infinite, so it is not linear sofic over any field of characteristic `p`. With
  `K = F_2` and `n = 2` this settles `non-linear-sofic-group`
  (`non-linear-sofic-via-leavitt-el3-rank-triviality`).
* For `n = 2`, `R ~= M_3(R)` gives `EL_3(R) <= GL_3(R) ~= R^x`. So `R^x` is not `F_p`-linear
  sofic, and neither is `PG` when `K = F_3` (through
  `leavitt-units-embed-in-their-scalar-quotient`).
* This instance is the payoff carrier. The class statement
  `el3-rank-models-factor-through-ring-rank-models` implies it
  (`leavitt-el3-rank-triviality-from-ring-rank-rigidity`), but a counterexample to the class
  statement over some other ring leaves this claim untouched.

## Attempts

- **Root identities decide (lane `gk-rk-unipotent`, 685d99751a).**
  - `N_12^2 = 0` and `N_23 N_12 = 0`, with `N_ij = sigma(x_ij(1)) - 1`, already build the
    matrix units, so the matrix-unit theorems apply.
  - In characteristic two `N_12^2 = 0` is automatic. So for `K = F_2` this claim is
    equivalent to: every characteristic-two rank model of `EL_3(L_(F_2)(1,2))` satisfies
    `(sigma(x_23(1)) - 1)(sigma(x_12(1)) - 1) = 0`.
  - Free content on `SL_3(F_2)` is exactly where that identity fails
    (`free-rank-models-on-sl3-admit-no-block-support`), and it is the family's target.
- **Excluded in every characteristic (established).**
  - Block support of the six unit root elements on orthogonal idempotents:
    `matrix-unit-root-rank-models-of-simple-el3-are-trivial` (char 2) and
    `matrix-unit-root-rank-models-of-odd-char-simple-el3-are-trivial` (odd), with
    `gk-vf-linear`'s scope note. This is `(natural (x) W) (+) trivial` on `SL_3(F_p)`.
  - `(dual natural (x) W) (+) trivial`, through transpose-inverse
    `EL_3(R) ~= EL_3(R^op)` (`gk-vf-linear`, verification artifact Section 29, eda113e5ce).
  - Monomial models: `monomial-rank-models-are-hamming-models` together with
    `d-ary-leavitt-groups-nonsofic-over-finite-fields`.
- **Free content is not reached by propagation.** `free-rank-models-on-sl3-admit-no-block-support`:
  - a model with positive free content on `SL_3(F_p)` has
    `rk((sigma(x_23(1)) - 1)(sigma(x_12(1)) - 1)) > 0`, so it never meets the matrix-unit
    hypothesis;
  - such models exist for `EL_3` of the locally matricial algebra `lim M_(p^k)(F_p)`, which
    has a ring rank model;
  - so the Leavitt structure has to enter any proof here.
- **Instance-specific tools (artifact Sections 4 and 4b).**
  - The level subgroups `SL_(3 n^k)(K)`.
  - The doubling identity `g = g (x) I_n`, and the corner copy `g ~ g (+) I` by absorption
    whenever `g` has a trivial Jordan summand. For `n = 2` these give `f(2r) = f(r)` on
    involution types `1 <= r < N/4` in `SL_N(F_2)`, `N = 3·2^(k+1)`. The endpoint `r = N/4`
    is excluded, and an earlier version wrongly attributed the conjugacy to the nine-leaf
    compressor (artifact Section 4, corrected).
  - Per-finite-subgroup data cannot force the gate identity (lane `gk-rk-unipotent`), so a
    proof must use an infinite subgroup. Artifact Section 4f gives an explicit compressor
    `c x_12(a) c^-1 = x_12(s_0 a t_0)` and the amenable subgroup `<U_12(R), c>`, as a pointer.
  - `x_12(1)` as a product of `n^k` commuting conjugates of itself, for every `n`.
  - Conjugacy `x_12(e_S) ~ x_12(1)` for a sum `e_S` of `|S|` distinct level idempotents holds
    exactly when `|S| ≡ 1 mod (n-1)`, since `Im(x_12(e_S) - 1) ~= e_S R ~= R^|S|` and
    `R^m ~= R` iff `m ≡ 1 mod (n-1)`. So it holds for every nonzero `S` only when `n = 2`
    (scope correction by `gk-vf-linear`, Section 34).
- **Equidistance on the locally matricial part (binary case, artifact Proposition 12).**
  - Every nonzero root element with coefficient in `A_inf = union M_(2^k)(F_2)` has the same
    displacement `rho`, so the model is equidistant on each `U_ij(A_k) ~= (Z/2)^(4^k)`.
  - Free modules and uniform permutation modules are equidistant too, and regular models of
    level groups meet every level-group constraint (doubling, compressor corners, idempotent
    conjugacy).
  - So a contradiction must use coefficients outside `A_inf`: `s_0`-type coefficients and
    Thompson `V`.
- **Rank extraction from root displacement: dead as a standalone route** (lane `gk-rk-free`;
  artifact `root-displacement-rank-extraction-2026-09-12.md`).
  - The displacement function `rho(a) = rk(sigma(x_12(a)) - 1)` is Weyl and unit invariant,
    `<= 1/2`, subadditive, with `rho(ab) <= 2 min(rho(a), rho(b))` and `rho/4 <= rho(a) <= 2 rho`
    for every nonzero `a`. Orthogonal idempotent root tuples are simultaneously conjugate
    (`leavitt-rank-models-have-uniform-root-displacement`).
  - All of this is realized by `(1 - epsilon)` trivial `(+)` `epsilon` free models of the dyadic
    root group, at every displacement in `[0, 1/2]`
    (`dyadic-root-displacement-data-admit-trivial-plus-free-models`). The extracted function is
    Boolean, not a Sylvester rank function.
  - It does not see the gate identity `N_23 N_12 = 0` of
    `el3-unit-root-matrix-units-iff-two-root-identities`: natural block models over the locally
    matricial algebra and free models both have uniform displacement.
- **Unipotent values and flags (lane `gk-rk-extensions`, 1940cc8920).**
  - `unipotent-valued-rank-models-of-el3-are-trivial`. For unipotent representatives and `m`
    invertible in `k`, `rk(x^m - 1) = rk(x - 1)` at every stage. Now take one torsion element
    of `SL_3(F_p)` of order prime to `p`: the 3-cycle for `p = 2`, `diag(-1,-1,1)` for odd `p`.
    Its image must be `1` if unipotent, and it normally generates `EL_3(R)`.
    - Filter: in every nontrivial characteristic-`p` model that image is not unipotent.
      Re-checked by lane `gk-l-gate-neg`.
  - `flag-preserving-rank-models-of-el3-reduce-to-their-diagonal`: finite-stage flags of any
    length with block-triangular representatives give a diagonal homomorphism, and the model is
    trivial iff its diagonal is.
    - So non-split extensions along such flags are no independent obstacle, and G-invariant
      flags in `M` are not needed.
- **Bounded-degree level content (lane `gk-rk-composition`, edfa936ea7).**
  - `dyadic-involution-profiles-kill-bounded-degree-content`, established. It is a finite-group
    statement about a level group `SL_N(F_2)` with `N >= 4(D+1)`. Suppose the restriction is an
    orthogonal sum of trivial, projective and strict-polynomial pieces `F(V_N, V_N*)` of degree
    at most `D`, and the involution profile satisfies `f(2r) = f(r)`. Then every polynomial piece
    is trivial.
    - Proof: on `F(V_N, V_N*)` the displacement of a rank-`r` involution is a polynomial in `r`
      of degree at most `D` with value `0` at `r = 0`, and dyadic invariance at `D + 1`
      integers kills it.
  - Proposition 2 supplies the identity for every char-two model of `L_K(1,2)^x`, and so does the
    diagonal of any flag above. So natural, dual, natural-plus-dual, adjoint `V (x) V*`, and
    bounded tensor, exterior or symmetric content never occur as nonzero orthogonal level-group
    pieces, including as graded pieces of such flags.
  - Projective pieces, the Steinberg module included, have profile `1/2` and survive with free
    content, as do pieces whose degree grows with `N`.
  - Artifact `research/artifacts/level-group-polynomial-content-2026-09-12.md`.
- **Surviving shapes to cover.**
  - Diffuse block-diagonal models. These are general models on smaller blocks, so they meet
    the same identity `N_23 N_12 = 0`.
  - Natural and dual pieces mixed with no finite triangular ordering.
  - Free or projective content on finite subgroups, glued through level-changing units such as
    `s_0` and Thompson `V`.
  - Bounded-degree polynomial pieces are excluded at level groups by Proposition 2 (lane
    `gk-rk-composition`). Coefficients from the Jacobson subring `F_2<s_0, t_0 | t_0 s_0 = 1>`
    alone never force triviality, so a proof must use the Cuntz relation.
