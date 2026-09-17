---
rg: 2
id: surjunctive-decoder-subgroups-force-surjectivity-proof
kind: route
title: Translate the decoder memory into the subgroup, freeze the input off the subgroup, and apply surjunctivity to the frozen encoder
target: surjunctive-decoder-subgroups-force-surjectivity
requires: []
---

Conventions: `G` acts on `A^G` by `(g.x)(h) = x(g^-1 h)`. An automaton with memory `M` and rule
`mu : A^M -> A` is `tau(x)(g) = mu((x(gm))_(m in M))`. By Curtis--Hedlund--Lyndon (valid over every
group) the automata are exactly the continuous equivariant self-maps.

**Step 0. Translating the memory.** For `g in G` let `R_g(x)(h) = x(hg)`. It is equivariant:
`R_g(k.x)(h) = x(k^-1 hg) = (k.R_g x)(h)`. So `R_g` is an automaton with memory `{g}`, bijective with
inverse `R_(g^-1)`. Fix `s_0 in S` and put `g = s_0^-1`,

```text
sigma' = R_g sigma,      tau' = tau R_(g^-1).
```

Then `sigma' tau' = R_g sigma tau R_(g^-1) = id`, `tau'` is surjective iff `tau` is, and
`sigma'(y)(h) = sigma(y)(hg)` reads `y` on `h g S = h S'` with `S' = s_0^-1 S`. Now `S' <= H`, because
`s_0^-1 s in S^-1 S`. Conversely `s^-1 t = (s_0^-1 s)^-1 (s_0^-1 t)`, so `<S'> = H`.

**Step 1. The restricted decoder.** Let `sigma_H` be the automaton over `H` with memory `S'` and the
rule of `sigma'`. Let `rho : A^G -> A^H` be restriction. For `h in H` the value `sigma'(y)(h)` reads only
`y` on `h S' <= H`, so

```text
rho sigma' = sigma_H rho.                                                      (1)
```

For a left transversal `T` of `H` put `y_t(h) = y(th)`. The same computation at `th` gives
`sigma'(y)_t = sigma_H(y_t)`, so `sigma'` acts on `A^G = prod_(t in T) A^(tH)` coset by coset by copies of
`sigma_H`. In particular

```text
sigma_H injective  =>  sigma' injective.                                       (2)
```

**Step 2. Freezing.** Fix `a_0 in A` and define `iota : A^H -> A^G` by `iota(z)(k) = z(k)` for `k in H`
and `iota(z)(k) = a_0` otherwise. For `h in H`, left translation by `h` maps `H` to itself and `G \ H`
to itself, so `iota(h.z) = h.iota(z)`. Restriction is also `H`-equivariant. Put

```text
tau_H = rho tau' iota : A^H -> A^H.
```

It is continuous and `H`-equivariant, hence an automaton over `H`. Explicitly, if `tau'` has memory `M'`
and rule `mu'`, then `tau_H(z)(h) = mu'(w)` with `w(m) = z(hm)` for `m in M' ∩ H` and `w(m) = a_0` for
`m in M' \ H`, since `hm in H` iff `m in H`. By (1),

```text
sigma_H tau_H = sigma_H rho tau' iota = rho sigma' tau' iota = rho iota = id_(A^H).
```

**Step 3. Surjunctivity of `H`.** `sigma_H tau_H = id` makes `tau_H` injective. `H` is surjunctive at
`|A|`, so `tau_H` is surjective. Every `y in A^H` is `tau_H(z)`, and `sigma_H(y) = sigma_H(y')` with
`y' = tau_H(z')` gives `z = z'`, so `sigma_H` is injective. By (2) `sigma'` is injective.

**Step 4. Surjectivity.** For `y in A^G`, `sigma'(tau'(sigma'(y))) = sigma'(y)`, so `tau'(sigma'(y)) = y`.
So `tau'` is surjective, and so is `tau`. QED

**Descent.** Suppose `tau` is not surjective. Steps 0--2 do not use surjunctivity of `H` and give
automata over `H` with `sigma_H tau_H = id`. If `tau_H` were surjective, Step 3 from its second sentence
on and Step 4 would make `tau` surjective. So `tau_H` is injective and not surjective: a strict pair over
`H`, with decoder memory `S'` generating `H`.

**What is used, and calibration.**
- Only three facts: the decoder reads inside `H` after one translation; a left translation by an element
  of `H` fixes the set `G \ H`, so a constant filling off `H` is `H`-invariant; and the identity
  `sigma tau = id` holds for every input, including frozen ones.
- The Garden of Eden theorem for the decoder is never used. That is why the free case goes through,
  although a surjective automaton over `F_2` need not be pre-injective.
- **Group structure.** Step 0 uses that right multiplication by a group element is a bijection of the
  index set commuting with the left action, and Step 1 uses the decomposition of the index set into
  left cosets of a subgroup of the index set. Neither exists on the vertex set of the end-fixing tree
  (`end-fixing-tree-symmetries-carry-strict-automata`), whose index set is not a group, so the
  statement has no analogue there to misfire on.
- **Known cases reproduced.** `H` amenable gives `amenable-decoder-memory-forces-surjectivity`.
  `S <= N` normal and surjunctive gives `normal-surjunctive-decoder-memory-forces-surjectivity`, since
  then `S^-1 S <= N` and subgroups of surjunctive groups are surjunctive
  (`surjunctivity-passes-to-subgroups`). `H = G` sofic gives `sofic-groups-are-surjunctive` for pairs.
