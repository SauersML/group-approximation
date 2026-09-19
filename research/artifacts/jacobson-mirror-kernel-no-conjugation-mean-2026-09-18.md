# Kernel-averaging descent through the Jacobson mirror quotient: a spectral-gap class-kill

Lane `swarm-0917-w14-w14-nh-break` (belief breaker, `non-hyperlinear-group`), 2026-09-18.
Claim: `jacobson-mirror-kernel-has-no-conjugation-invariant-mean`. Route: `jacobson-mirror-kernel-no-conjugation-mean-proof`.

## 1. Where this sits

- The open decision point of the Jacobson branch is whether `E = EL_n(J)` is sofic or hyperlinear. It is load-bearing
  for `binary-jacobson-el3-is-sofic`, and through the trace gate for `agent-leavitt-not-bcs-negative-root-corner`.
- By `jacobson-toeplitz-extension-is-a-mirror-quotient-of-a-lef-group`, `E = P / L_-` with `P` LEF and `L_-`
  infinite, locally finite and simple. So the whole difficulty is one quotient step by an amenable kernel. This is
  the Jacobson instance of Thom's Kourovka question 21.118.
- Finite kernels are handled by averaging. In the tracial picture the averaging is the central projection
  `p_N = |N|^-1 sum_(n in N) u_n`, which is fixed by `N` and gives `p_N L(G) = L(G/N)`. The sofic orbit-set argument
  is the combinatorial shadow of the same thing.
- The natural infinite analogue averages over Følner sets of the kernel. It needs one of two things:
  - a mean on the kernel that is translation invariant and conjugation invariant, which is (CIM); or
  - rescaled projections that almost commute with the ambient group and are almost fixed by the kernel.

## 2. The result

Theorem A of the claim: if `phi : G ->> W` with `W` Kazhdan and `phi(k_0) notin FC(W)`, then no mean on `G` is
conjugation invariant and `k_0`-translation invariant.

**The Jacobson instance.** Take `G = P`, `W = E_-` (the mirror half, which is `EL_n(J)` and so Kazhdan by
Ershov–Jaikin-Zapirain), and `k_0 = (1,t)` with `t in L_-` nontrivial. Consequences:
- (CIM) fails for `(P, L_-)` and for `(E, L)`.
- The diagonal is not co-amenable in `P x_E P`.
- No coherent Følner windows exist.
- No rescaled compression of `lambda_P ⊗ v` descends to `E` while seeing `L`.

**Why the mirror half is the right quotient.** Pushing forward to `E_+` loses everything, because the kernel dies
there. Pushing forward to `E_-` keeps the kernel `L_-` faithful, and `E_-` still has (T). The fibre-product
structure of `P` is exactly what makes a Kazhdan group see the kernel. So P's own LEF-ness cannot be combined with
kernel averaging.

## 3. Why this is not the bilateral-envelope kill

`bilateral-envelope-fuses-the-mirror-kernel-with-the-head` kills approximations inherited from `H_bi`, from
`<P, c>` or from periodic models, through a conjugacy between the mirror head and the head. That argument works at
the level of characters. The present argument uses no envelope, only the spectral gap of `E_-`, and it kills
approximations *drawn from the regular representation of `P`* (tensor any `v`). The two kills are independent:
- The bilateral kill needs the *descended* character (the one that is `1` on `L_-`) to extend to `<P,c>`. A
  compression `p U_g p` with `p in L(P) ⊗̄ B` need not almost commute with `c`, so its descended character need not
  extend. Theorem B kills it anyway.
- Conversely, the periodic LEF models are not of the form `lambda_P ⊗ v`. Theorem B says nothing about them, and
  the bilateral kill handles them.

## 4. Surviving routes to "E is sofic or hyperlinear"

1. **Non-regular averaging.** A rescaled projection almost commuting with a tracial representation `sigma` of `P`
   and almost fixed by `sigma(L_-)`, where `sigma` is neither regular-type nor inherited from `<P,c>`. The argument
   of Theorem B does not apply when the conjugation representation of `P` on `L^2(sigma(P)'')` does not carry
   densities on `P` itself, as `lambda_P ⊗ v` does. Heuristic, not proved here: if `P` had (T) (unknown; only
   `E_+` and `E_-` are known to be Kazhdan), an almost-invariant projection would sit near the relative commutant
   `sigma(P)' ∩ M`. The problem would then be to find `sigma` whose relative commutant contains a projection fixed
   by `sigma(L_-)` whose corner trace vanishes off `L_-`, which is the full problem without any averaging shortcut.
2. **Direct approximations of `E`,** not through `P`. According to the live bus, lanes w10 and w11 landed
   `jacobson-haar-relation-is-laurent-affine-restriction` and `jacobson-haar-relation-is-kazhdan-and-unsplittable`
   on another branch; they are not in this worktree. Per those reports, the Haar relation route is Kazhdan and
   unsplittable.
3. **The linear rank-model side.** Every characteristic-two rank model kills `Q` by index. That is recorded
   separately in `binary-jacobson-el3-rank-radical-is-the-finitary-kernel`.

## 5. Explorations in this lane that reproduced known deaths (not new nodes)

- **Ring rank models.** `rank(1 - ST) = rank(1 - TS)` in finite dimensions, so every finite-dimensional ring model
  of `J` kills `Q`. This is the Fredholm index obstruction, already in the graph.
- **Mirror orientation.** No anti-automorphism of `J` covers the identity symbol, since `T` plus finite rank has
  index `+1`. Finite interval models realize `P`, not `E`. Already recorded under MQ and the bilateral kill.
- **Haar fixed-point character.** The orbit relation of `E` on `F_2^(N x n)` reduces to the affine action of
  `EL_n(A) x| A^n` on Laurent series. This is already landed by lane w10, per the bus, as
  `jacobson-haar-relation-is-laurent-affine-restriction` (not in this worktree). The dual solenoid picture gives periodic approximations for the linear part, which the translations break,
  and reproduces the far-end obstruction.
- **Følner-type sofic criteria for Kazhdan groups.** They reduce to LEF (`jacobson-elementary-groups-are-lea-only-if-lef`).

## 6. Calibration

`Z^3 x| SL_3(Z)` with kernel `Z^3` also fails (CIM), by the same theorem, yet its quotient is residually finite. So
failure of kernel averaging is a statement about methods. It gives no evidence that `E` is nonsofic, and it should
not shift beliefs about the truth value, only about which proofs can exist.
