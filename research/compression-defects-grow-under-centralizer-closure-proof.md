---
rg: 2
id: compression-defects-grow-under-centralizer-closure-proof
kind: route
title: Invert the compressor, swap the commutator, and feed the normalized centralizer to the bead-residue central series
target: compression-defects-grow-under-centralizer-closure
requires:
  - intrinsic-compression-defect-functoriality-and-saturation
  - infranormal-sources-never-saturate-sofic-mapping-tori
  - sofic-groups-kill-rigid-compression-defects
---

Commutators are `[a,b] = a b a^-1 b^-1`, so `[a,b]^-1 = [b,a]` and
`h [a,b] h^-1 = [h a h^-1, h b h^-1]`. `X^c = C_G(X)`. Centralizers reverse inclusions, and
`C_G(h X h^-1) = h X^c h^-1`.

## Step 1: (GC1)

Let `u in Comp_G(L)`, so `u L u^-1 <= L`. Reversing inclusions,

```text
L^c <= C_G(u L u^-1) = u L^c u^-1,     so     u^-1 L^c u <= L^c.
```

Hence `u^-1 in Comp_G(L^c)`. Applying this to `L^c` gives `Comp_G(L^c)^-1 <= Comp_G(L^cc)`, so
`Comp_G(L) <= Comp_G(L^c)^-1 <= Comp_G(L^cc)`. Applying it to `L^cc` and using `L^ccc = L^c`
gives `Comp_G(L^cc)^-1 <= Comp_G(L^c)`. The two inclusions give
`Comp_G(L^cc) = Comp_G(L^c)^-1`.

## Step 2: (GC2)

Take a generator `y = [u c u^-1, l]` of `D_G(L)`, with `u in Comp_G(L)`, `c in L^c`, `l in L`.
Conjugate by `u^-1`:

```text
u^-1 y u = [c, u^-1 l u] = [u^-1 l u, c]^-1.
```

Here `v = u^-1 in Comp_G(L^c)` by Step 1, `l in L <= L^cc = C_G(L^c)`, and `c in L^c`. So
`[v l v^-1, c]` is a generator of `D_G(L^c)`, with compressor `v`, centralizing element `l` and
source element `c`. `D_G(L^c)` is normal, so it contains `u^-1 y u` and hence `y`. Therefore
`D_G(L) <= D_G(L^c)`.

Applying this to `L^c` gives `D_G(L^c) <= D_G(L^cc)`. Applying it to `L^cc` gives
`D_G(L^cc) <= D_G(L^ccc) = D_G(L^c)`. So `D_G(L^c) = D_G(L^cc)`.

## Step 3: (GC3)

Let `K` be normal in `G`, `L <= K`, and `L^ = L^cc ∩ K`.
- *Centralizer.* `L <= L^ <= L^cc` gives `L^ccc <= C_G(L^) <= L^c`, so `C_G(L^) = L^c`. Hence
  `(L^)^ = C_K(C_G(L^)) = C_K(L^c) = L^`.
- *Compressors.* If `u in Comp_G(L^)`, then Step 1 gives `u^-1 in Comp_G(C_G(L^)) = Comp_G(L^c)`.
  Conversely, if `u^-1 in Comp_G(L^c)`, then Step 1 gives `u in Comp_G(L^cc)`. Also
  `u K u^-1 = K`, so `u L^ u^-1 <= L^cc ∩ K = L^`. So `Comp_G(L^) = Comp_G(L^c)^-1`, and it
  contains `Comp_G(L)` by Step 1.
- *Defects.* A generator `[u c u^-1, l]` of `D_G(L)` has `u in Comp_G(L) <= Comp_G(L^)`,
  `c in L^c = C_G(L^)` and `l in L <= L^`. So it is literally a generator of `D_G(L^)`, and
  `D_G(L) <= D_G(L^)`. Step 2 applied to `L^` gives `D_G(L^) <= D_G(C_G(L^)) = D_G(L^c)`.
- *Formula.* Substituting `u = v^-1` with `v in Comp_G(L^c)` into (ICD1) for `L^` gives the
  displayed formula for `D_G(L^)` in terms of `Z = L^c`.

## Step 4: (PT)

Suppose `K` normalizes `Z = C_G(L)`, and put `N = <<L>>^K`. For `k in K` and `c in Z`,
`k^-1 c k in Z` centralizes `L`, so `c` centralizes `k L k^-1`. Hence `c` centralizes `N`, and
`C_G(L) = C_G(N)`. This is exactly (IS0) of `infranormal-kernel-sources-die-in-sofic-mapping-tori`.

The proof in `infranormal-sources-never-saturate-sofic-mapping-tori-proof` uses soficity, the
Kazhdan property of `L` and infranormality only to obtain (IS0). Its "Checks" section says
where soficity and infranormality enter, and the w8 audit (live lemma 16a18747) confirmed this.
The remaining steps use only the following facts:
- (IS1): `u N u^-1 <= N` for `u in Comp_G(L)`, which needs only `u K u^-1 = K`;
- the one-sign argument and the Frobenius step, which are pure group theory;
- (DZ), which needs (IS0) and `l in L <= N`;
- (BF), which needs finite generation of `K`;
- (NC), which is pure group theory;
- the final kill, which needs "nilpotent Kazhdan implies finite" for `K`.

None of these uses that `L` is Kazhdan or infranormal. So the same argument gives
`D_G(L) != K`.

The degenerate case is also covered. If no compressor is strict, then (IS1) gives
`D_G(L) = 1`, which is not `K` since `K != 1`.

## Step 5: (CI)

Let `Gamma <= K` be Kazhdan and infranormal in `K`, with `C_G(Gamma) = Z`.
- If `L <= Gamma <= L^`, this holds by the centralizer computation of Step 3.
- Apply `sofic-groups-kill-rigid-compression-defects` with `H = G` and the Kazhdan pair
  `Gamma <= K`. For `g in K` and `z in Z = C_G(Gamma)`, it gives `[g z g^-1, gamma] = 1` for
  all `gamma in Gamma`, so `g Z g^-1 <= Z`.
- Applying this to `g^-1` as well shows that `K` normalizes `Z`. Step 4 then gives
  `D_G(L) != K`.

## Step 6: the survivor conditions

- If `K` normalized `Z^c`, it would normalize `Z^cc = Z`, since `Z = L^c` is closed.
  Conversely, normalizing `Z` implies normalizing `Z^c`. So the two survivor forms are the same.
- `Comp_K(L) <= Comp_K(L^)` is Step 3 intersected with `K`.
- If `L^` is Kazhdan and `Comp_K(L^)` generates `K`, then `Gamma = L^` is admissible in Step 5.
  This proves the last survivor condition.

## Checks

- **Abelian quotient.** `D_G(X) <= K` for every `X`, since each generator is a commutator and
  so dies in `G/K`. Step 3 therefore places the whole chain inside `K`.
- **Scope.** Part A uses no hypothesis on `G`. Part B needs `K` Kazhdan: Step 4 kills through
  "nilpotent Kazhdan implies finite", and Step 5 needs the Kazhdan pair `Gamma <= K`. The
  literal sofic group `E` has a nontrivial defect with a non-Kazhdan compressor group, and its
  radical has no infinite Kazhdan subgroup (`literal-mf-radical-has-no-infinite-kazhdan-subgroup`).
  So it is outside Part B, and Part B does not conflict with it.
