---
rg: 2
id: traced-kazhdan-transport-counterexample-proof
kind: route
title: Conjugate a commuting Thompson copy into a nonabelian subgroup of the Kazhdan core
target: traced-kazhdan-transport-counterexample
requires:
  - openai-nine-leaf-leavitt-configuration
artifacts:
  - research/artifacts/traced-kazhdan-transport-counterexample-2026-08-19.md
---

Use the notation of `openai-nine-leaf-leavitt-configuration`.  Thus

```text
[Gamma,J]=1,
u Gamma u^{-1}<=Gamma,
u J u^{-1}=V_(0001)<=Gamma,
```

and `Gamma` has property `(T)`.  Since `V_(0001)~=V` is nonabelian, choose
`w,gamma in uJu^{-1}` with `[w,gamma]!=1`, and put `j=u^{-1}wu in J`.

Take the finite tracial group von Neumann algebra

```text
M=L(G)
```

and its faithful left regular representation `lambda`.  Set `x=lambda(j)`.
The relation `[Gamma,J]=1` gives

```text
x in lambda(Gamma)' cap M.
```

But

```text
lambda(u) x lambda(u)^* = lambda(w),
```

and this does not commute with `lambda(gamma)`, because `lambda` is faithful
and `[w,gamma]!=1`.  Therefore the conjugated element is not in the original
relative commutant.  Taking the constant exact coordinate family gives zero
multiplicative defect, so this is a counterexample to the arbitrary traced
coordinate statement, not merely to a quantitative modulus.
