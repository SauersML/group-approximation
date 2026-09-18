# Corner tame symbols of R_l (lane gq-k2-q, 2026-09-18)

Coordinator's question on the `Z_(l)` bottleneck (lane gq-infinite-primes): is `K_2(N, R_l)`, or at least the
finite residual of `St_N(R_l)`, finitely normally generated? The crux was whether the corner tame symbols from
`K_2(Z_(l)) ⊇ ⊕_(q≠l) F_q^x` survive independently.

**Verdict: they survive and are independent, and both routes through `R_l` are closed.**

| node | status | content |
|---|---|---|
| `resolvent-ring-corner-symbols-survive-in-k2` | ESTABLISHED (lane) | `θ_* : K_2(Z_(l)) -> K_2(R_l)` injective; corner symbols infinitely generated |
| `resolvent-elementary-groups-are-not-fp` | ESTABLISHED (lane) | `E_N(R_l)` not f.p. for every `l` and `N >= 3`; refutes `resolvent-elementary-group-is-fp` |
| `resolvent-steinberg-rf-residual-is-infinitely-normally-generated` | OPEN, proof modulo (DS), (vdK) | the corner symbols also lie in the finite residual; refutes the RF-residual route once confirmed |

## 1. The detecting quotient

The path normal form makes this nearly mechanical.
- Kill the ideal `J` of paths `[a|K|b]` with a nonempty middle word. The quotient is `D ⋉ M_Z^fin(Z_(l))`, and the
  corner `e` becomes the matrix unit `E_(0,0)`.
- Split excision for the local-unit ideal gives `K_2(D) ⊕ K_2(Z_(l))`, with `Z_(l)` detected through Morita
  invariance.
- So `K_2(Z_(l))` injects into `K_2(R_l)` through the corner. No computation of `K_2` of the tensor algebra `T(N)`
  is needed: the retraction `R_l -> R_l/J` already sees `Z_(l)`.

## 2. Why this is decisive

- The corner symbols `{u_λ, u_μ}` with `u_λ = θ(λ) + (1 − e)` are Steinberg symbols of commuting units of `R_l`.
  The symbol lemma therefore applies directly to `E_N(R_l)`, with no centrality hypothesis on `K_2(N, R_l)`.
- For the finite residual, each finite quotient sees the corner only through some `Z/l^r`, where `K_2` is `0` for
  odd `l` and at most `Z/2` for `l = 2`. So the symbols are residually invisible.
- Kervaire centrality of stable `K_2` makes normal closures of finite sets have finitely generated stable image.
  That rules out finite normal generation.

## 3. What survives, and what to change (for gq-infinite-primes)

- `R_l` itself is still a finitely presented, residually finite ring containing `Z_(l)` in a corner. Only the
  passage to finitely presented groups through `E_N` or `St_N/K_rf` is blocked.
- Any finitely presented residually finite ring `S` containing `Z_(l)` in a corner that has a retraction onto
  finite matrices over `Z_(l)`, as `R_l/J` does, will fail the same way.
- A repair must kill the corner symbols with finitely many relators. Two natural ways out both kill the corner in
  every finite quotient, since there `[ē]` is not divisible by large `n` and has no Leavitt pair:
  - making `[e]` divisible in `K_0`, so that the product `K_0 ⊗ K_2(Z_(l)) -> K_2` kills them;
  - a Leavitt pair in the corner.

  Either conflicts with detecting `Z_(l)` residually. A repair therefore needs a relator that kills the symbols
  themselves: a Steinberg-level relation among `x_ij(θ(λ))`.
- The alternative in Attempt 2 of `resolvent-steinberg-rf-residual-is-finitely-normally-generated` remains: replace
  the corner ring `Z_(l)` by a ring with finitely generated symbol group that still inverts all primes but one.
  Any such corner ring inverts every prime but `l`, so it contains `Z_(l)`. The symbols `{q, g_q}` must therefore die
  in the corner ring or in the ambient ring, and by the previous bullet not through `K_0` divisibility.

## 4. Source reads for the finite-residual node (2026-09-18)

Both PDFs were downloaded on MSI through institutional access and read page by page. Local copies are in the
session scratchpad `gq/src/k2/`, and MSI copies are in `/projects/standard/hsiehph/sauer354/gq-k2/`.

- **Dennis–Stein, *The functor K_2: a survey of computations and problems*.** LNM 342 (1973), pp. 243–303 (the downloaded chapter, 63 pages, includes the part-title page 241),
  doi:10.1007/BFb0073728.
  - §12, pp. 254–255: `K_2(W_m(F_q)) = 1` if `p` is odd or `m = 1`, and `= Z/2Z` if `p = 2` and `m >= 2`. The
    general formula is their [27, Theorem 4.3], for quotients `A/P^m` of discrete valuation rings.
  - §12, p. 254: for `A` a DVR or a quotient of one, `K_2(A)` and `K_2(n, A)` for `n >= 3` are presented by
    symbols subject to (S1)–(S7) [27, Theorems 2.3, 2.5].
  - §4, pp. 246–247: `K_2(Z_S) ≅ {±1} ⊕ ⊔_(p∈S) (Z/pZ)^*` for `Z_S = Z[1/S]`. With `S` the primes other than
    `l`, this is `K_2(Z_(l))`, which confirms input (K-c) of `resolvent-steinberg-rf-residual-is-finitely-normally-generated`.
  - §1, p. 245: `K_2(R)` is the centre of `St(R)` [69, §5], for any ring.
- **van der Kallen, *Injective stability for K_2*.** LNM 551 (1976), pp. 77–154, doi:10.1007/BFb0079997.
  - Theorem 1, p. 77, is quoted verbatim in the node. It assumes a commutative ring with noetherian maximal
    spectrum of dimension `d`, and needs `n >= d + 2`.
  - Our use is `R = Z/l^r`, with `d = 0` and `N = n + 1 >= 3`. The noncommutative `R_l` is never fed to it.
