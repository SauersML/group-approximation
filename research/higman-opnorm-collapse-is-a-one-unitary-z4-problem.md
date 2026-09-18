---
rg: 2
id: higman-opnorm-collapse-is-a-one-unitary-z4-problem
kind: claim
title: Higman operator-norm collapse is a one-unitary problem over an exact order-four symmetry
artifacts:
  - research/higman-opnorm-collapse-is-a-one-unitary-z4-problem-proof.md
  - experiments/higman-minimax-2026-09-17/equivariant_search.py
  - experiments/higman-minimax-2026-09-17/minimax_polish.py
  - experiments/higman-minimax-2026-09-17/chain64.npy
  - experiments/higman-minimax-2026-09-17/chain80.npy
  - experiments/higman-minimax-2026-09-17/run_chain64.txt
  - experiments/higman-minimax-2026-09-17/run_chain80.txt
  - experiments/higman-minimax-2026-09-17/chain80b.npy
  - experiments/higman-minimax-2026-09-17/chain96.npy
  - experiments/higman-minimax-2026-09-17/run_chain80b.txt
  - experiments/higman-minimax-2026-09-17/run_chain96.txt
  - experiments/higman-minimax-2026-09-17/run_pad96.txt
  - experiments/higman-minimax-2026-09-17/pad48_from32_b.npy
  - experiments/higman-minimax-2026-09-17/pad48_from32.npy
  - experiments/higman-minimax-2026-09-17/amp48.npy
  - experiments/higman-minimax-2026-09-17/rand_N32.npy
  - experiments/higman-minimax-2026-09-17/rand_N64.npy
  - experiments/higman-minimax-2026-09-17/witness_polished.npy
  - experiments/higman-minimax-2026-09-17/run_pad48_from32.txt
  - experiments/higman-minimax-2026-09-17/run_pad48_from32_eps10.txt
  - experiments/higman-minimax-2026-09-17/run_amp48.txt
  - experiments/higman-minimax-2026-09-17/run_rand_N16.txt
  - experiments/higman-minimax-2026-09-17/run_rand_N32.txt
  - experiments/higman-minimax-2026-09-17/run_rand_N64.txt
  - experiments/higman-minimax-2026-09-17/run_witness_long.txt
distinct_from:
  order-four-bs-matcher-builds-higman-opnorm-microstate: that builds tuples from a BS packet and a matcher K whose fourth return must be paid approximately; this shows every tuple is exactly of the form S^i P S^(-i) with S^4=1 after amplification, so no fourth return is ever paid and no packet D is involved.
  higman-opnorm-defect-profile-has-dim-twelve-witness: that defines the four-unitary profile m_c(L) and records a descent plateau near 0.31; this proves the profile equals a one-unitary Z/4 profile and records far microstates below that plateau.
  higman-group-is-the-swap-twisted-double-of-a-bs-amalgam: that is an exact group-theoretic decomposition of Hig; this is an operator-norm statement about approximate representations and their order-four amplification.
  higman-four-cycle-intrinsic-mf-seed: that asks for the collapse modulus itself; this reformulates the modulus without deciding it.
---

**ESTABLISHED** by `higman-opnorm-collapse-is-a-one-unitary-z4-problem-proof`.
Items 1--5 are proofs.  The census section is evidence only.

For unitaries `P,S` in `U(N)` with `S^4=1` put

```text
def_S(P) = || P (S P S^*) P^* - (S P S^*)^2 ||_op.                (HZ1)
```

1. **Orbit to tuple.**  `U_i=S^i P S^(-i)`, `i in Z/4`, is a well-defined
   four-tuple.  Each of its four Higman relator defects equals `def_S(P)`, and
   `||U_i-1||=||P-1||` for every `i`.

2. **Tuple to orbit.**  For `U_0,...,U_3` in `U(L)`, let `P=diag(U_0,...,U_3)`
   on `C^(4L)`, and let `S` be the cyclic block shift
   `(x_0,x_1,x_2,x_3) -> (x_1,x_2,x_3,x_0)`.  Then `S^4=1`,
   `def_S(P)=def(U)` and `||P-1||=max_i||U_i-1||`.                 (HZ2)

3. **Equal profiles.**  Put

   ```text
   m^(4)_c(N) = inf { def_S(P) : P,S in U(N), S^4=1, ||P-1||>=c }.   (HZ3)
   ```

   Both `m_c` of `higman-opnorm-defect-profile-has-dim-twelve-witness` and
   `m^(4)_c` are nonincreasing, and

   ```text
   m_c(4L) <= m^(4)_c(4L) <= m_c(L).
   ```

   Hence the two limits coincide, and the collapse modulus `(HMF5)` of
   `higman-four-cycle-intrinsic-mf-seed` holds if and only if

   ```text
   lim_(N->infinity) m^(4)_c(N) > 0        for every c>0.           (HZ4)
   ```

4. **Diagonal form.**  After conjugating, `S=D=diag(i^(a_k))`.  Then
   `def_S(P)=||R P R^* - P^2||` with `R=D^* P D`.  So a noncollapsing sequence
   is exactly a sequence of unitaries `P_n`, far from `1`, that approximately
   conjugate their own square by their own `Z/4`-twist.

5. **Grading collapse.**  If `P` lies within `eta<1` of the commutant `{S}'`,
   then

   ```text
   ||P-1|| <= def_S(P) + 12 eta.                                    (HZ5)
   ```

   In particular a noncollapsing sequence must keep `P_n` at distance at
   least `(c-def_(S_n)(P_n))/12` from `{S_n}'`.  That is, `P_n` must mix the
   four eigenspaces of `S_n` uniformly.

**Consequences for the four-seam gate.**  The target's gate asks for a matcher
`K_n` with small one-step error *and* small fourth return
`||K_n^4P_nK_n^(-4)-P_n||`.  Item 2 shows that every noncollapsing sequence,
if one exists, already has an amplified form with an exact order-four matcher
`K=S` and return exactly `0`.  So the fourth-return clause of `(HOM5)` is never
an obstruction for general microstates.  It is an artifact of fixing the
clock `P_n` and a separate packet `D_n`.  The whole difficulty sits in the
single equation `(HZ1)`.

## Census (evidence, not established)

`equivariant_search.py` minimizes `def_S(P)` for the block shift `S` on
`C^N`.  It uses:

- Riemannian descent on the smooth maximum of the singular values of
  `(HZ1)`, with continuation `beta=10,...,3000`;
- then the bundle minimax polish of `minimax_polish.py`, restricted to one
  relator.

Every stored `P` was rechecked independently.  The script extracts
`U_i=S^iPS^(-i)`, recomputes all four defects in `U(N)^4`, and confirms
unitarity error `<1e-13`.  By item 1, each stored `P` is a far four-tuple in
`U(N)`, so each line below is an upper bound on `m_1.99(N)`, and never a
lower bound.

```text
start                                   N    def_S(P)   ||P-1||
L=12 witness, four-tuple minimax polish 12   0.308580   >=1.985
random Haar, best of 4                  16   0.314373   >1.5
random Haar, best of 4                  32   0.309881   1.9995
L=12 witness amplified by (HZ2)         48   0.301445   1.9944
random Haar, one start                  64   0.303254   1.9999
best N=32 padded by (+)1, eps=0.05      48   0.285011   1.9997
best N=32 padded by (+)1, eps=0.10      48   0.284947   1.9997
N=48 optimum padded by (+)1             64   0.282726   1.9995
N=48 optimum padded by (+)1             80   0.282938   1.9995
N=64 optimum padded by (+)1             80   0.280644   1.9995
N=64 optimum padded by (+)1             96   0.280783   1.9995
N=48 amplified witness padded by (+)1   96   0.300810   1.9937
```

The warm-start optima have a visible structure.

- *Low rank.* `P-1` has 32 or 33 eigenvalues at distance `>=1e-3` from `0`
  at `N=48,64,80,96`.  So each optimum is, up to `1e-3` in eigenvalues, a
  rank-33 perturbation of the identity.
- *Not `S`-invariant.* The span of the four `S`-translates of that range has
  dimension `43, 47, 51, 54` at `N=48, 64, 80, 96`.
- *Mixed grades.* In the eigenbasis of `S`, every off-diagonal grade block of
  the `N=64` optimum has norm in `[0.74,0.89]`, in line with item 5.
- *Start matters.* Warm starts from the amplified witness stay near `0.30`.

What the census shows:

- **No 0.31 barrier.**  The minimax polish lowers the recorded twelve-dimensional
  witness to a stationary point at `0.308580`, below `sin(pi/10)=0.309017`.
  Equivariant descent then goes further, to `0.2849` at `N=48`, `0.2827` at
  `N=64` and `0.2806` at `N=80`.
- **Warm starts continued in dimension lower the defect, with shrinking
  gains.**  Padding an optimum and re-descending beats both Haar starts and
  the amplified witness.  This contradicts the earlier census verdict that
  descent cannot see the defect decrease with dimension.  The chain goes
  `0.3099 (N=32) -> 0.2849 (48) -> 0.2827 (64) -> 0.2806 (80)`.  The `N=96`
  run from the same `N=64` start gives `0.2808`, so the chain has flattened.
  The data are equally consistent with a positive limit near `0.28` and with
  slow decay.
- **No lower bound.**  All values come from local optimization.  They say
  nothing about whether `lim m^(4)_c(N)` is positive, so they neither refute nor
  prove `(HMF5)`.
