---
rg: 2
id: weak-determinant-violations-move-to-cubic-operators
kind: claim
title: Every determinant violation by an injective integral matrix over G becomes a violation by an injective operator 1 + w1 + w2 with monomial w1, w2 over G x Z, so the weak-isomorphism determinant conjecture is the norm band just above 3/sqrt2
distinct_from:
  cubic-serre-violations-transfer-to-norm-near-3-over-sqrt2: that moves violations from cubic operators of norm below three to norm near 3/sqrt2; this makes every injective violation cubic in the first place (over G x Z) and removes the norm-below-three hypothesis from that transfer
  determinant-conjecture-iff-serre-class-spectra: that reformulates the conjecture through spectra of arbitrary self-adjoint integral matrices; this changes the operator, collapsing all injective matrices to sums of three monomial unitaries
  tripod-free-integral-matrices-reduce-to-virtually-cyclic: that proves Serre below absolute norm 3/sqrt2; this shows that one step above that threshold already carries the full weak-isomorphism determinant conjecture
artifacts:
  - experiments/determinant-cubic-linearization-2026-09-17/linearize_check.py
  - experiments/determinant-cubic-linearization-2026-09-17/output.txt
  - experiments/determinant-cubic-linearization-2026-09-17/gadget_search.py
  - experiments/determinant-cubic-linearization-2026-09-17/gadget_output.txt
---

**ESTABLISHED** by `weak-determinant-violations-move-to-cubic-operators-proof`.
Unreviewed.

**Notation.**
- `det` is the Fuglede--Kadison determinant: unnormalized trace on matrices,
  normalized trace on the group.
- `DC(G)` means `det' A >= 1` for all integral matrices over `G`.
- `DC_wi(G)` restricts `DC(G)` to injective square matrices, where `det' = det`.
- A *monomial* matrix has exactly one nonzero entry in each row and column,
  and that entry is a group element.
- *Cubic without inversions* is as in
  `cubic-serre-violations-transfer-to-norm-near-3-over-sqrt2`.
- `K = G x Z`, with `s` the central generator of `Z`.

**Theorem 1 (cubic linearization).** Let `T in M_n(Z[G])` be injective.
Explicitly and finitely, there is `M' in M_N(N[K])` with the following
properties:
- every entry is a sum of group elements with coefficient sum `3` in each row
  and in each column;
- `M'` is injective;
- `det_{N(K)} M' = det_{N(G)} T`.

Consequently:
- `M' = u1 + u2 + u3` with monomial unitaries `u_i` (König), so
  `det T = det(1 + w1 + w2)` with `w_i = u1^* u_(i+1)` monomial over `K`;
- `B = [[0, M'], [M'^*, 0]]` is cubic without inversions and injective, with
  `det B = (det T)^2`.

**The construction** has four steps:
1. **Schur trees.** Out-trees and in-trees realize each monomial of `T` as a
   path, giving `L = [[0,E],[F,-I+K_nil]]` whose Schur complement is `T`.
2. **Sign removal.** `M1 = [[P,N],[I,I]]`, where every coefficient is `0` or
   `1` and all row and column sums are at most `3`.
3. **Padding.** One gadget `G(s) = [[0,1,s],[1,1,1],[s,1,1]]` is added for each
   pair of row and column deficits. It has `det G = -(1-s)^2` (Mahler measure
   `1`) and `adj(G)_(00) = 0`, which kills the cross term of the Schur
   complement.
4. **Bipartite double.**

**Theorem 2 (norm-free violation transfer).** In
`cubic-serre-violations-transfer-to-norm-near-3-over-sqrt2`, part 3, the
hypothesis `||r_B|| < 3` can be dropped. Suppose a cubic operator `B` without
inversions over `H` violates Serre with `R`. Then its `L`-subdivision `A_L`,
of norm below `3/sqrt 2 + 3 * 2^(-(L+1)/2)`, violates Serre with
`((t^2-9) R^m) o p_L` for all large `m`.

**Two obstructions** show why the central variable is needed:
- **No scalar gadget.** No nonnegative integer padding `[[M1, E'], [F', G]]`
  with all margins `3` and `|det G| = 1` has a vanishing cross term
  `E' G^-1 F'`, in any size. The reason is that `E' G^-1 F' 1 = 3E'u - E'1`
  with `u = G^-1 1` integral, and the deficits `E'1` are `1` or `2` mod `3`.
- **No same-group cubic model over finite groups.** For finite `H`, every
  cubic `M'` over `H` has `3 | det rho(M')`. So `det_H M'` is either `0` or at
  least `3^(1/|H|)`, and no cubic operator over `H` can carry `det T = 1`.

  In particular, over finite groups the cubic determinant bound is strict.
  Any exact cubic model must leave the group, and `G x Z` is the minimal
  change.

**Corollaries.**
1. **All groups.** The following are equivalent:
   - `DC_wi(G)` for every group `G`;
   - `det B >= 1` for every injective cubic operator without inversions over
     every group;
   - `det(1 + w1 + w2) >= 1` for all monomial `w1, w2` over every group,
     whenever `1 + w1 + w2` is injective.
2. **Per group.** For every group `H`:

   ```text
   DC(H) => DC(H x Z) => NR(H x Z) => CubicSerre(H x Z) => CubicDet(H x Z)
         => DC_wi(H x Z) => DC_wi(H)
   ```

   - `NR(K)` means: for some `eps > 0`, every nonnegative self-adjoint integral
     matrix over `K` of norm below `3/sqrt 2 + eps` obeys every Serre
     inequality.
   - The first implication is the amenable-extension theorem of Schick
     (Lück, *L2-invariants*, Theorem 13.3). A short direct proof by weak
     convergence of `H x Z/q` spectra is in the proof route.
3. **Norm band.** If Serre holds just above norm `3/sqrt 2` over every group,
   then `DC_wi` holds for every group. Serre holds below `3/sqrt 2`
   (`tripod-free-integral-matrices-reduce-to-virtually-cyclic`). So the whole
   weak-isomorphism determinant conjecture sits in the band
   `[3/sqrt 2, 3/sqrt 2 + eps)`.

**What is not claimed (kernel gap).** `DC_wi => DC` is not proved.
- Step 1 is a unipotent similarity, and with a kernel it changes `det'`. For
  `T = 1 + h` over `Z/2`: `log det' T = 0.3466`, `log det' L = 1.2425`,
  `log det' M1 = 1.5673`.
- Central-variable tricks such as `X + (1-X)s` compute `m(P_lambda)`, which
  is continuous at `lambda = 0`. They yield
  `integral log max(lambda, |1-lambda|) d mu`, which never sees the kernel.

**Verification.**
- `linearize_check.py` checks the linearization identity exactly, modulo
  `2^31-1`, in the regular representation. The groups are
  `H in {Z/2, Z/3, Z/5, S_3}` with the `Z` coordinate as a variable, and
  matrices go up to size `315`. Results are in `output.txt`.
- The script also checks:
  - exact 3-regularity and the König split;
  - the FK determinant by quadrature;
  - negative controls (a gadget with `adj(G)_(00) != 0` fails, and so does a
    kernel case);
  - the Theorem 2 identity on finite cubic graphs of norm exactly `3`, with
    atoms at `+-3`.
- `gadget_search.py` confirms the no-scalar-gadget lemma by exhaustive search
  for sizes up to `4`.

## Attempts

- 2026-09-17 (sw-046): cubic linearization over `G x Z` with a central
  gadget. It lands the reductions above. The kernel gap `DC_wi => DC` stays
  open.
