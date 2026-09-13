# un-open-8 plan: one compression lemma, read by the target

Lane `un-open-8` (UN swarm, open-ended; lens: simplicity of proof), 2026-09-13. Plan only; nothing here is
established.

## Target

The non-MF paper and the Pestov 9.1 answer both rest on one two-line mechanism, but main carries it in four
separate places, each with its own rigidity input:
- exact finite groups and finite-dimensional linear groups (`unsquared-defect-finite-model-invisible`, for one
  specific group);
- operator-norm coronas, through Kazhdan projections and stable finiteness of the adjoint corona (tex
  Thm l.478, Cor l.581);
- exact ring models (towers), through matrix rank (the Pestov ring is directly finite; tex l.1514);
- and it fails for tracial targets (`un-hyperlinear-paradox` §3).

**Lemma C (target-agnostic compression lemma).** Let `ψ: G -> H` be a homomorphism, `L <= G`, `u` a compressor
(`uLu^-1 <= L`), `c in C_G(L)`, `l in L`. If some `S <= H` contains `ψ(L)`, has `C_H(ψ(L)) = C_H(S)`, and
satisfies `ψ(u) S ψ(u)^-1 = S`, then `ψ([ucu^-1, l]) = 1`. (Proof: `ψ(ucu^-1)` centralizes `ψ(u)Sψ(u)^-1 = S`.)

**Rigid targets** (where the hypothesis is automatic): finite groups (`S = ψ(L)`, counting); `GL_d(K)` for any
field `K` (`S` = Zariski closure: dimension plus component count); ring models into directly finite rings (rank);
MF targets only after property (T) and the adjoint corona (Hilbert–Schmidt form, then the normal-Kazhdan
upgrade). Tracial targets are not rigid.

**Corollaries to land.**
1. For every unital ring `R` with `ts = 1`, `e = 1 - st`, and `N >= 4`: every homomorphism from `EL_N(R)` to
   `GL_d(K)` (any field, any `d`), in particular to any finite group, is trivial on `E_N(R, ReR)`. No (T), no
   finite generation. The input is the printed rank-four compression cell, tex l.866.
2. The towers side: a unital map to a directly finite ring kills `ReR`, so exact matricial models (Pestov)
   exist only where no defect ideal is nonzero; the same `ReR` is killed at every rigid target level.
3. A calibration table: which conclusions hold at which target level for `L_k(1,2)`, the Pestov ring, the
   algebraic Toeplitz ring, integral Jacobson `Z<s,t | ts=1>` (linear targets kill the finitary part while the MF
   status is undecided: `integral-jacobson-mf-radical-is-all-or-nothing`), and `F_q[Γ]`.

## Why it matters

It makes the two papers the same argument read by two kinds of target. The only varying ingredient is
the rigidity of `S`: counting, algebraic dimension, rank, or Kazhdan projections in a finite C*-algebra.
It isolates exactly where (T) is needed (MF), where it is not (finite, linear, ring), and where the argument
must stop (tracial, since the adjoint support lives in `B(L^2(M^ω))`).

## Not duplicated

- `un-open-1` owns the ring radical `i(R)` and MF radicals; I use only one defect step and no transfinite
  iteration.
- `un-hyperlinear-paradox` owns the HS failure; I cite §3.
- `un-architect` owns the ladder; I land lemma-level nodes and send ids for wiring.
- The finite-additive-order MF nodes (char p, exact) are cited, not reproved.
