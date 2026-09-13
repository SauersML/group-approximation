# The Jones-index surviving shape for RNORM adds no leverage

Date: 2026-09-12. Lane `rnorm-jones-index` (swarm 7). Corrected after the first
landing.

- **Target:** the surviving shape recorded on
  `relative-normalization-modulo-kazhdan-kernel` and in
  `rnorm-kazhdan-projection-sizes-2026-09-12.md` Section 4: a quantized Jones-type
  relative index on the unbounded-multiplicity Kazhdan sector `H_inf`, forced to
  `1` by an almost-invariance bound below `2`.
- **Outcome:** such an index exists, but it gives nothing.
  - Its gap below `2` is automatic for every conditional expectation.
  - "Index `< 2`" is equivalent to `P' = P`, which is the normalization on `H_inf`
    itself.
  - Landed as `jones-index-blind-on-unbounded-defect-sector`. The id wording is
    historical. RNORM and `nonsofic-hyperbolic-group` stay OPEN.
- **Correction.** The first version (commits 939a37611, eb8fd6e76) made two claims.
  The first is false and the second is withdrawn (Section 2):
  - the Pimsner--Popa index of a non-factor inclusion has no gap in `(1,2)`;
  - quantization and the defect live on disjoint sectors.

## 1. What was proposed

On `H_inf` the position of `Gamma_hat = EL_alpha(R)` is genuine data. `P` is the
fixed space of `W_rho(Gamma_hat)`, and `P' = W_rho(u)^* P W_rho(u)`. The two are
unitarily conjugate and nested, and strict inclusion is allowed at infinite
multiplicity. Relabel so that `P' <= P`, and put `Q = P - P'`.

The proposal had four steps, copying Kun--Thom's integer index below `2` on the
*finite* cluster groupoid:
1. read a Jones index `[P:P']`;
2. use a median/(T) argument to bound it below `2`;
3. conclude that it equals `1`, so `P = P'`;
4. hence the twist is trivial, normalization holds, and RNORM follows.

## 2. The gap below 2 is free

**Lemma 1.** Let `N <= M` be a unital inclusion of von Neumann algebras, `E : M -> N`
a conditional expectation, and `Ind(E) = inf{lambda^-1 : E(y) >= lambda y, y >= 0}`.
Then `Ind(E) in {1} U [2, infinity]`, and `Ind(E) = 1` iff `N = M`.

*Proof.* Suppose `N != M`.
1. Some self-adjoint `a` lies outside `N`. Put `h = a - E(a)`, which is nonzero with
   `E(h) = 0`.
2. Normalize so that `||h|| = 1` and `1 in spec(h)`.
3. Put `y = 1 + h >= 0`. Then `E(y) = 1`, and `1 >= lambda(1+h)` at the spectral
   point `1` forces `lambda <= 1/2`. ∎

No factoriality, trace, Jones quantization, or (T) enters. The first version's
"weighted diagonal with no gap in `(1,2)`" was wrong. The smallest check:
`C <= C^2` with `E(a,b) = ta + (1-t)b` has `lambda = min(t, 1-t) <= 1/2`.

So the analogy with Kun--Thom holds on this point, but it holds trivially.
- Their step "integer below `2` is `1`" is the same free gap.
- The content of their argument was the median/(T) estimate, not the gap.

## 3. The index of `P' <= P` is the defect indicator

**Lemma 2.** Put `M = P B(H_inf) P`, `N = P'MP' + QMQ`, and `E_P(x) = P'xP' + QxQ`,
with `P != 0`. Then `Ind(E_P) = 1` if `P' = P`, and `Ind(E_P) = 2` if `P' != P`.

*Proof.*
1. If `Q = 0`, then `N = M`.
2. If `Q != 0`, then `P'MQ != 0`, since `P'` is conjugate to `P != 0`. So `N != M`
   and `lambda <= 1/2`.
3. Conversely, `(P'-Q)x(P'-Q) >= 0` gives `x <= 2E_P(x)` for `x >= 0`. ∎

The same holds for any expectation onto a subalgebra attached to `(P, P')` that
equals the whole algebra exactly when `P' = P`: by Lemma 1, "index `< 2`" means
`P' = P`.

**Consequence.** The proposed bound "index `< 2`" is literally
`W_rho(u)^* P W_rho(u) = P` on `H_inf`. The index does not jump in stages as the
defect grows. It is `2` as soon as `Q != 0`, however small `Q` is in any trace.
Jones' finer quantization `{4 cos^2(pi/n)}` in `[2,4)` is never used.

## 4. Sector picture (corrected)

| sector | `Ind(E_P)` | defect visible? |
|---|---|---|
| `H_b` (bounded mult.) | `1`: Theorem B gives `P' = P` | no |
| `H_wm` (weakly mixing) | no `rho`-isotypic part, nothing to index | no |
| `H_inf` (unbounded mult.) | `1` or `2`; `2` exactly when `P' != P` | yes, as the jump `1 -> 2` itself |

The first version's table said `H_b` is quantized and `H_inf` is not. That is
withdrawn: every expectation index has the gap below `2`, on every sector.

## 5. What survives

- **The index step is a relabeling.** Lemma 1 holds for amenable hosts too, so any
  (T) input must go entirely into proving `P' = P` on `H_inf`.
- **What a Kun--Thom-style argument would need.** On `H_inf`, `A_rho` commutes with
  `W_rho(R^x)`: block invariance makes `1 (x) A_rho` commute with
  `U_rho (x) W_rho`. So the argument would disintegrate over `A_rho` and need
  `Q_omega = 0` fibre by fibre, which is the defect statement again. That is not
  pursued here.
- **The dimension-ratio reading is unsupported.** Reading `[P:P'] = tau(P)/tau(P')`
  needs a trace on an algebra containing `P, P'` with `0 < tau(P) < infinity`.
  None has been constructed, and `W_rho(R^x)''` has no evident finite trace in a
  sofic model. The first version asserted that none exists. That is not proved,
  and it is dropped.
- **What any working mechanism must do.** Force `Q = 0` exactly. Index theory offers
  no intermediate quantity. **This is where it stops.**

## 6. Red-flag check

- **The (T) test.** The brief required that the index use (T) of `N` essentially
  and fail for amenable hosts. The Jones-type index fails that test: its only gap
  holds for every inclusion. This is why it cannot be the mechanism.
- **Scope.** Nothing here uses soficity of `G` or proves anything about `V`, and no
  root is established.

Literature: Pimsner--Popa (Ann. Sci. ENS 19, 1986) for the constant
`lambda(E)`; Lemmas 1 and 2 are proved in full here. Jones (Invent. Math. 72,
1983) is cited only for the finer quantization, which is unused.
