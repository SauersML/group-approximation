---
rg: 2
id: window-zero-twists-are-fixed-point-free-proof
kind: route
title: A fixed point of the twist commutes with the shift, and the centralizer of the shift is the shift
target: window-zero-twists-are-fixed-point-free
requires: []
artifacts:
  - research/artifacts/gq-bh-bh-shell-kazhdan-rigidity-attempt.md
---

**Item 1.** Suppose `f s^k = s^k f` in `NearSym(N)`, that is, `f(n+k) = f(n) + k` for all but finitely many `n`. This says exactly that `f` is eventually `k`-periodic, and conversely every such `f` commutes with `s^k`.

For `k = 1` it gives `f(n) = n + c` for all large `n`, so `f = s^c` in `NearSym(N)`.

The index-zero eventually `k`-periodic near permutations are determined, near infinity, by the following data:
- a permutation `pi` of the residues mod `k`;
- integers `d_r` with `f(r + k m) = pi(r) + k(m + d_r)`.

So they form a subgroup of `Z^k ⋊ Sym(k)`, which is virtually abelian.

**Item 2.**
- The window relation with `psi(g) = g` reads `s^-eps rho_g s^eps = rho_g`, so `rho_g` commutes with `s`.
- By item 1, `rho_g = s^c` in `NearSym(N)`.
- The index is a homomorphism `NearSym(N) -> Z`. `rho_g` is a genuine permutation, so its index is `0`, while `s^c` has index `c`. Hence `c = 0`, and `rho_g` is finitary.
- Infinite supports then force `g = 1`.

**Item 3.**
- Iterating the window relation gives `s^(-k eps) rho_g s^(k eps) = rho_(psi^k(g))` for every `g`, since both sides are homomorphisms to `NearSym(N)` agreeing on generators.
- If `psi^k(g) = g`, then `rho_g` commutes with `s^k` and is eventually `k`-periodic by item 1.
- `Fix(psi^k)` is a subgroup. The near action is faithful, so `rho` embeds `Fix(psi^k)` into the virtually abelian group of item 1.

**Item 4.**
- If `psi^k = id`, then `P = Fix(psi^k)`, which is virtually abelian by item 3.
- The generator statements are items 2 and 3 applied to that generator.
- In the lamplighter example, `psi(t) = t` gives `rho_t = 1` in `NearSym(N)` by item 2. So `t` would act finitarily, contradicting infinite support. `∎`
