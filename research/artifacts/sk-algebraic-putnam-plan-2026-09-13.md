# sk-algebraic-putnam plan: exchange property and stable rank one for LC(X,F) ⋊ Z (2026-09-13)

Lane sk-algebraic-putnam (wave 11). Plan artifact; no claims.

## Problem
For a minimal homeomorphism T of the Cantor set X and a field F, let R = LC(X,F) ⋊_T Z. Is R an exchange ring of stable rank one? This is the algebraic analogue of Putnam's theorem (topological stable rank one and real rank zero for C(X) ⋊ Z).

Open nodes on main:
- `minimal-cantor-crossed-product-is-an-exchange-ring`;
- `minimal-cantor-crossed-product-has-stable-rank-at-most-two` (asks for ≤ 2, and whether sr = 1);
- `subshift-crossed-product-ring-has-bass-stable-rank-at-most-two` (special case).

Where earlier lanes stopped:
- sk-stable-rank-a: the tower-to-base witness for the Laurent element u + u²; no construction for general a.
- sk-stable-rank-b: two colourings, "dimension one" picture, no theorem to finish.
- sk-free-7: compression to tridiagonal block matrices with couplings of rank ≤ w; gluing per-block witnesses across couplings is missing.

## New ingredient
sk-free-6 Theorem D (`subshift-el-groups-boundedly-elementary-generated`, part3 §1) glues finite linear algebra across Kakutani–Rokhlin cuts:
- compress an element to each tower occurrence;
- correct the compression inside a window at each end, choosing the correction from the local configuration only;
- the corrected block operator is invertible with banded inverse;
- the remainder is supported near the cuts and is handled on the midpoint towers.

The only obstruction is the Fredholm index of half-line compressions. Blockwise-defined elements whose choices depend only on the local configuration lie in R automatically.

## Targets, in order
1. **(T1) Exchange property.** Nicholson: for each a ∈ R an idempotent e ∈ aR with 1 − e ∈ (1 − a)R. Attack: finite exchange witnesses on corrected tower compressions, glued along cuts with end corrections, then fix the cut neighbourhoods on midpoint towers as in Theorem D.
2. **(T2) Stable rank one.** Given T1: for exchange rings, sr = 1 iff idempotents cancel (Yu; Camillo–Yu: iff every regular element is unit-regular; check at source). The candidate cancellation input is V(R) against K_0(R) = coinvariants (`subshift-crossed-product-k0-is-coinvariant-group`), a simple dimension group, together with the faithful rank functions from invariant measures.
   - Direct attack as well: a unimodular pair aR + bR = R, completed to a unit a + bc blockwise with end corrections. Units of R have index-compatible compressions, so check where the index enters.
3. **Fallbacks (each a clean claim):**
   - (P1) every Laurent polynomial p(u) is suitable in R, generalizing sk-stable-rank-a §2.2;
   - (P2) unimodular pairs of Laurent polynomials become stable in R, i.e. the sr-2 obstruction of F[u^{±1}] disappears;
   - (P3) sr(R) ≤ 2;
   - (P4) a precise obstruction: an element with no exchange idempotent, or a unimodular pair with no unit completion.

## Imports to check at source
- Nicholson (exchange criterion; suitable elements).
- Camillo–Yu, Trans. AMS 347 (1995); Yu, stable range one for exchange rings.
- Ara–Goodearl–O'Meara–Pardo, Israel J. Math. 105 (1998) (separative exchange rings, sr ∈ {1, 2, ∞}).
- Vaserstein's stability theorems, only if T2 is reached.

Claims are queued in `sk/queue/sk-verify-13.txt`.
