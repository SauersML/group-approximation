# sk-free-7 plan: an algebraic Putnam theorem for LC(X,F) ⋊ Z (2026-09-13)

Lane sk-free-7 (wave 10, free lane). This is a plan artifact with no claims.

## Choice and why
The generalizations I considered first are already on main:
- the boundary of the expander family and "simple iff minimal": `research/artifacts/pestov91-four-regular-expanders-and-limits-2026-09-13.md` §3–4;
- the binary simplicity criterion for any acting group: `binary-el-simple-iff-minimal-topologically-free`;
- Z^d, free groups and Steinberg algebras: un-* and ex-* swarms;
- the ring-level LEF iff at Z^2: the Labbé lanes.

What remains open, and gates three questions at once, is the **ring structure** of R_X = LC(X,F) ⋊_T Z for a minimal Cantor system:
- `minimal-cantor-crossed-product-is-an-exchange-ring` (OPEN);
- `minimal-cantor-crossed-product-has-stable-rank-at-most-two` (OPEN; "Is it 1?").

Both owners, sk-stable-rank-a and sk-stable-rank-b, have finished. The C*-analogues are Putnam's theorem (tsr 1) and real rank zero.

Target, the statement a reader remembers: **R_X is an exchange ring of stable rank one** (an algebraic Putnam theorem).

## What it would give (each step with its import)
1. **Simplicity by citation.** Preusser, Theorem 3 (exchange rings, standard normal structure) or Vaserstein (sr ≤ 2), via `standard-normal-structure-makes-simple-ring-el-simple`.
2. **Injective K_1-stability.** sr = 1 gives GL_n(R_X)/EL_n(R_X) ≅ K_1(R_X) for n ≥ 2.
   - The algebraic Pimsner–Voiculescu sequence with K_1(LC) = 0 gives K_1(R_X) ≅ ker(1−T on C(X,Z)) = Z for minimal X.
   - So G_X = [GL_3(R_X), GL_3(R_X)] and GL_3(R_X)/G_X ≅ Z, via the class of the shift.
3. **K_2-stability.** van der Kallen: injective stability for n ≥ sr+2 = 3. With stable K_2(R_X) = 0 (`binary-cantor-ring-stable-steinberg-group-centrally-closed`), K_2(3,R_X) = 0, so G_X ≅ St_3(R_X). This settles `subshift-elementary-groups-are-steinberg-groups-in-finite-rank` at n = 3 as far as St_n → EL_n goes.
4. **The dictionary.** If the argument extends to aperiodic non-minimal subshifts Y: K_2(3,R_Y) = 0, so normal subgroups of G_X correspond exactly to subsystems (`aperiodic-subshift-ring-unstable-k2-vanishes`, `accumulating-minimal-sets-el-restriction-kernel-elementary`).

## Approach
- **(A) Exchange.** Nicholson's criterion: for each a, find an idempotent in a + (a − a²)R.
  - Kakutani–Rokhlin towers with heights ≫ the degree of a, made pattern-equivariant through markers.
  - Generalize the tower-to-base witness of sk-stable-rank-a §2.2 from Laurent polynomials to arbitrary coefficients.
  - Alternative: represent R_X faithfully on F^(Z) at a point with dense orbit, run a local Gaussian elimination whose pivot rules read only windows of bounded radius, and show the output is a sliding block code, so it lies in R_X.
- **(B) Stable rank one.** For exchange rings, sr = 1 iff idempotents cancel internally (Yu 1995; Camillo–Yu; to be checked at source).
  - Idempotent classes via K_0(R_X) = coinvariants (`subshift-crossed-product-k0-is-coinvariant-group`) and the faithful rank functions of Ara–Claramunt.
  - Or directly: nilpotent tower shifts turn a unimodular pair into a unit, as in `1 + u e_(X∖T^{-1}Y)`.
- **(C) Consequences** 2–4 above, with every stability theorem quoted at source (van der Kallen 1977; Vaserstein 1971; Bass).
- **Literature first** (bounded): exchange and stable rank of Steinberg algebras and skew group rings over Cantor sets; the Ara–O'Meara–Perera translation algebras (Trans. AMS 2004).

## Honest risk
- sk-stable-rank-a found no tower construction for general a.
- A counterexample is also valuable: a unimodular pair with no unit, or an element with no exchange idempotent, would be the first ring-level difference between R_X and C(X) ⋊ Z.

Fallback targets if (A) stalls within ~2 h:
- sr ≤ 2 through a cancellation argument;
- the exchange property only for elements of degree ≤ 1 (enough for suitable roots?);
- a precise obstruction map.

Claims are queued in `sk/queue/sk-verify-13.txt`.
