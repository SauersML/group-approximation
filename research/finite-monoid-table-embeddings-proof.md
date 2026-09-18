---
rg: 2
id: finite-monoid-table-embeddings-proof
kind: route
title: Colorings of a finite monoid act give exact functional models, and exact models are monoid acts
target: finite-monoid-table-embeddings-forbid-bernoulli-deficit
requires:
  - bernoulli-rokhlin-deficit-has-a-finitary-witness
artifacts:
  - research/artifacts/finite-monoid-certificates-2026-09-17.md
  - experiments/finite-monoid-certificates-2026-09-17/check_monoid_model.py
---

Sections 1 to 5 of the artifact.

**Step 1: functional count (Lemma 1, proved in full in Section 2).**
- *Setup.* Take a finite `X` with maps `T_f, S_e`. A point `w` is good when `1 -> w`, `e -> S_e w`,
  `fe -> S_e T_f w` is a well-defined injective map `Q -> X`.
- *Chain.* Put `x` iid uniform on `A^k` over `X` and `c(w) = psi((x(S_e w))_e)`. Then
  `k|X| log q <= sum_w H(c(w)) + sum_w H(x(w) | (c(T_f w))_f)`.
- *Good points.* A good point contributes `k Phi`.
- *Bad points.* A bad point contributes at most `log|R| + k log q`.
- *Result.* `log q <= Phi + beta(log|R|/k + log q)`.

**Step 2: act.**
- Put `Y = M` and `phi_u(m) = lambda(u) m`, with `y_0 = 1_M`.
- Then `[fe] = phi_f ∘ phi_e`, and `q -> [q](y_0)` is injective.

**Step 3: exact model.**
- Put `X = [N]^Y` and `(T_f c) = c ∘ phi_f`, `(S_e c) = c ∘ phi_e`.
- Then `S_e T_f c = c ∘ phi_f ∘ phi_e = c ∘ [fe]` at every `c`. So the chart `q -> c ∘ [q]` is well
  defined everywhere.
- It fails to be injective only if `c([q]y_0) = c([q']y_0)` for some `q != q'`. So `beta <= C(|Q|,2)/N`.
- Let `N -> infinity`; Step 1 gives Theorem M.

**Step 4: converse.**
- For an exact model, take the monoid of self-maps of `X` with product `a * b = b ∘ a`, and put
  `lambda(f) = T_f`, `lambda(e) = S_e`.
- Exactness makes `[·]` well defined, and one good point makes it injective. This gives Theorem M'.

**Step 5: corollaries.**
- *Corollary A.* Take levels `R_r = K_Z B(r)` for `r <= L`, plus a sink.
  - `phi_u` raises the level by `mu t(u)`, with `mu = 1 + max_(K_Z)|·|`, and acts by `g -> ug`.
    It sends a point to the sink past `L`.
  - `phi_f phi_e` depends only on `fe` and `ht(fe)`.
  - `y_0 = (0, 1)` separates `Q`.
- *Proposition R.* In a finite monoid, `xy = 1` implies `yx = 1`.
- *Corollary R.* Use `E = F = S ∪ S^-1` for the forward direction, and restrict a finite-group local
  embedding for the converse.

The route uses no imports: only Shannon inequalities, a union bound, and finite monoid arithmetic.
The `requires` entry supplies the definition of `Phi` and the fact that it depends only on the
pattern.

**Check.** `experiments/finite-monoid-certificates-2026-09-17/check_monoid_model.py` checks (W) and (I)
exhaustively on two examples, and samples the bad fraction against the union bound:
- the sink model of Corollary A over `Z/2 * Z` with `E = F = {1, z, s}`;
- `Z` with `E = F = {1, s, s^-1}` in `Z/5`, where Theorem A says nothing because the only core is `Z`.
