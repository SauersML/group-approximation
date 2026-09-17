---
rg: 2
id: quadrangle-closed-patterns-do-not-force-domination
kind: claim
title: Incidence patterns with both cancellation laws and quadrangle closure carry Bernoulli configurations with Phi tending to zero
distinct_from:
  cancellative-incidence-patterns-do-not-force-domination: that firewall satisfies (L) and (R) but fails (Q); this one satisfies (L), (R) and (Q) and fails only the holonomy of class words, so it moves the needed axiom past quadrangle closure.
  quadrangle-closure-kills-shared-pointer-parity-gadgets: that kills gadgets with a coherent cyclic 3-shift at (Q) by the invariant |Delta| mod 3; this gadget leaves the pointer rotation open (shifts a, a, -2a), has no coherent 3-shift, and answers its recorded open question negatively.
  rokhlin-window-transport-is-dominated: that is domination over group patterns; this refutes the same bound for abstract quadrangle-closed patterns and names holonomy as an axiom a proof must use beyond (L), (R), (Q).
  coset-local-decoders-force-gated-domination: that proves gated gadgets are dominated in every group through coset projection; this shows the finite incidence axioms alone do not reach that conclusion.
artifacts:
  - research/artifacts/quadrangle-closed-pattern-firewall-2026-09-17.md
  - experiments/quadrangle-firewall-2026-09-17/verify_rotation_gadget.py
  - experiments/quadrangle-firewall-2026-09-17/verify_rotation_gadget.json
---

**Setting.** A pattern is a full rectangle `w : F x E -> sites`, `(c, e) -> c e`, with a special site `o`, and
`Phi = (1/k)[H(psi(iid)) + H(x(o) | y_F)]` as in `bernoulli-rokhlin-deficit-has-a-finitary-witness`. Axioms:
**(L)** rows injective, **(R)** columns injective, **(Q)** `c e = c' e'`, `c r = c' r'`, `d e = d' e'`
imply `d r = d' r'`. Under (L) and (R), (Q) says the row-pair classes `R(c, c') = {(e, e') : c e = c' e'}` are
pairwise disjoint or equal.

**Claim.** Take `q = 2`, `k = 2^t >= 4` and `R = ceil(2 k ln k)`. There is a finite pattern with (L), (R) and (Q)
and a code with `H(psi) = t + 1` such that

    Phi = (t + 1 + k (1 - 1/k)^R) / k  <=  (log2 k + 1 + 1/k)/k  ->  0 ,

giving `0.7817` at `k = 4` and `0.5107` at `k = 8`.

**The gadget (artifact §2).**
- **Positions.** Pointer positions `Z/L` (`L` prime, `L > 16R`) and value positions `Z/n` (`n` prime,
  `n >= R^2 + R + 1`). The code outputs `(j, XOR_values x[j])`, where `j` is the sum of the pointer prefixes
  mod `k`, invariant under every rotation of the pointer positions.
- **Codewords.** Gadget `rho` has three codewords with `W_i u_y = p(y + i a_rho)`. The four shifts
  `±a_rho, ±2a_rho` are distinct across all gadgets.
- **Value table.** The table follows the Hamiltonian cycle `x -> x + c_rho` of `Z/n`, split as
  `s_1 t_1 ... s_m t_m z_rho`. It gives `R(W_0, W_1) = R(W_1, W_2) = T_a ∪ N_c(s)` and
  `R(W_0, W_2) = T_(2a) ∪ N_c(t, z)`.
- **Decoding.** Every value site is read twice, except `o = W_1 z_rho`. So the XOR of the three outputs is
  `x(o)[j_rho]`.
- **Across gadgets.** Only `o` is shared, through the singleton classes `(z_rho, z_rho')`.

**Where it leaves the groups (artifact §6).**
- **Holonomy.** The class word `(tau sigma)^m sigma` fixes `s_1` but translates every pointer by `-(3m+2) a`.
  So the pattern fails the holonomy axiom:
  **(H)** a composite of classes that fixes one position is the identity on its domain.
  Every group pattern satisfies (H).
- **No group realizes it.** With `gcd(L, 3m + 2) = 1`, in any group `g = W_1^-1 W_0` has `g^L = g^(3m+2) = 1`,
  which is a contradiction.
- **Outside the mod-3 invariant.** There is no coherent 3-shift, and `|Δ| = L + 1 ≡ 2 (mod 3)` for
  `L ≡ 1 (mod 3)`.

**Consequences.**
- **Proof side.** The open question of `quadrangle-closure-kills-shared-pointer-parity-gadgets` is answered
  negatively. A proof of `rokhlin-window-transport-is-dominated` that uses the pattern only through (L), (R)
  and (Q) cannot exist. It must use a compositional property of class words of unbounded length, such as (H).
- **Counterexample side.** A deficit search filtered by (L), (R) and (Q) returns non-group false positives.
  Add the (H) test.
- **Open.** Do (L), (R), (Q) and (H) force domination? Do they force realizability in the canonical host?

**ESTABLISHED** by [[quadrangle-closed-patterns-do-not-force-domination-proof]].
