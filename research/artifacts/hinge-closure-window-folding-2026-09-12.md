# Garden-of-Eden windows fold modulo hinge closures, and transposed hinges are commutators

Lane `gk-n-defect`, 2026-09-12. Handwritten proofs; nothing was run. Supports
`garden-of-eden-windows-fold-modulo-every-hinge-closure` and
`transposed-hinges-are-conjugated-commutators`, and re-aims
`defect-window-automaton-over-leavitt-units` at the reverse hinge.

**Why now.** `bijective-designs-force-every-finite-presentation` shows that forcing a
presentation costs nothing but gives nothing: all of strictness lives in the reverse
hinges. This note ties the Garden-of-Eden window to those hinges, and computes the hinge
that transposition leaves behind.

## 0. Conventions and inputs

A design is `D = (A, S, M, nu, mu)`. A realization over a group `H` sends the addresses
into `H`, with identity addresses to `1`. Suppressing the realization map,

```text
tau_H(x)(g) = mu((x(g m))_(m in M)),        sigma_H(y)(g) = nu((y(g s))_(s in S)).
```

So `sigma tau` reads cells `(s,m)` at products `s m`, and `tau sigma` reads cells `(m,s)` at
products `m s`.

* **Tables.** `T_f(H)` is the partition of `S x M` by equality of `s m`, with marked class
  `s m = 1`. `T_r(H)` is the partition of `M x S` by equality of `m s`, with marked class
  `m s = 1`. A quotient `H -> H/N` coarsens both tables.
* **Input (T)**, from `strict-automata-live-on-canonical-table-groups`: `sigma_H tau_H = id`
  iff `T_f(H)` lies in the up-set `𝓕_D` of forward-sufficient partitions. When it does,
  `tau_H` is surjective iff `T_r(H)` lies in the up-set `𝓡_D` of reverse-sufficient
  partitions.
* **Hinge words.** For a partition `P` of `M x S`, put

  ```text
  W_P(H) = { (m' s')^(-1) (m s) : (m,s) ~_P (m',s') }  ∪  { m s : (m,s) in the marked class of P },
  ```

  and let `N_P(H)` be its normal closure. Then `T_r(H/N)` dominates `P` iff
  `N ⊇ N_P(H)`. If `P'` is coarser than `P`, then `W_P ⊆ W_(P')`, so the minimal elements
  of `𝓡_D` have the smallest closures.
* **(Q) Periodic lift.** For `N ⊴ H` with quotient map `q`, realize `D` over `H/N` along
  `q`. For every `z in A^(H/N)`,

  ```text
  tau_H(z o q) = tau_(H/N)(z) o q,
  ```

  because `tau_H(z o q)(g) = mu((z(q(g) q(m)))_m) = tau_(H/N)(z)(q(g))`.

## 1. Windows fold modulo every hinge closure

**Theorem 1.1.** Let `T_f(H) in 𝓕_D`, and let `p in A^Omega`, `Omega ⊂ H` finite, be a
Garden of Eden for `tau_H`. Then for every `P in 𝓡_D` there are `w, w' in Omega` with
`p(w) != p(w')` and `w^(-1) w' in N_P(H)`.

*Proof.* Put `N = N_P(H)` and `Q = H/N`. `T_f(Q)` coarsens `T_f(H)`, so it lies in `𝓕_D`.
`T_r(Q)` dominates `P`, so it lies in `𝓡_D`. By (T), `tau_Q` is surjective. Suppose `q`
separated every pair `w, w'` of `Omega` with `p(w) != p(w')`. Then `z(q(w)) = p(w)` defines
a partial configuration on `q(Omega)`; extend it arbitrarily to `z in A^Q`, and choose
`x_Q` with `tau_Q(x_Q) = z`. By (Q), `tau_H(x_Q o q) = z o q`, which restricts to `p` on
`Omega`. That contradicts the Garden of Eden. So `q` merges some `p`-distinguished pair,
and `q(w) = q(w')` means `w^(-1) w' in N`. QED

**Remark 1.2 (which quotients fold).** The proof uses only that this one design is
surjective over `H/N`. Those normal subgroups are exactly the ones containing `N_P(H)` for
some minimal `P in 𝓡_D`. Indeed, if `tau_(H/N)` is surjective, then `T_r(H/N)` lies in
`𝓡_D` by (T), so it dominates a minimal `P`, and `N ⊇ N_P(H)`.

A homomorphism `psi` from `H` into a surjunctive group `K` gives such a quotient. The
realization over `K` along `psi` has a coarser forward table, so it is injective, hence
surjective, so `T_r(K)` dominates a minimal `P` and `ker psi ⊇ N_P(H)`. So Theorem 1.1
refines Corollary 2 of `strict-pairs-transfer-to-table-realizations`, which folds under
homomorphisms into surjunctive groups: the folding already happens modulo a subgroup read
off from the design's own reverse table.

**Corollary 1.3 (two-cell windows).** If `Omega = {1, d}`, then `p(1) != p(d)` and

```text
d  in  ⋂_(P minimal in 𝓡_D) N_P(H)   ⊆   Rad_surj(H)   ⊆   Rad_sof(H),
```

where `Rad_surj(H)` is the intersection of the kernels of all homomorphisms from `H` into
surjunctive groups.

*Proof.* `𝓡_D` is nonempty. Over the trivial group `sigma tau = id` makes `tau` a
bijection of `A`, so `tau sigma = id` there too, and the coarsest partition is reverse
sufficient. A two-cell window has only one pair, so Theorem 1.1 gives both conclusions for
each minimal `P`. By Remark 1.2 every kernel into a surjunctive group contains some
`N_P(H)`, which gives the first containment. The sofic radical is the intersection of the
kernels of homomorphisms into sofic groups (`sofic-radical-localizes-garden-of-eden-windows`),
and sofic groups are surjunctive (`sofic-groups-are-surjunctive`), which gives the
second. QED

**Corollary 1.4 (monolithic descent).** With `Omega = {1, d}` as above, there is `K ⊴ H`
with `d notin K` such that:

1. the realization over `H/K` is injective and has `p` as a Garden of Eden on `{1, dK}`;
2. every nontrivial normal subgroup of `H/K` contains `dK`.

So `H/K` is a monolithic group, finitely generated when `H` is, whose monolith is the
normal closure of `dK`, and it carries a strict automaton with a two-cell window on that
monolith.

*Proof.* The union of a chain of normal subgroups avoiding `d` is a normal subgroup
avoiding `d`, so by Zorn's lemma some `K` is maximal among them. Part 2 is maximality.
For part 1, `T_f(H/K)` coarsens `T_f(H)`, so `sigma tau = id` over `H/K`. If `p` appeared
at `(K, dK)` in the image over `H/K`, then (Q) would put it at `(1, d)` in the image over
`H`. QED

**Scope.** Over a simple host every nontrivial `N_P(H)` is all of `H`, so Theorem 1.1 and
Corollary 1.3 say nothing beyond strictness there. They bite on the canonical table group
of a design, where the only relators are forced coincidences. For the Leavitt unit group
itself nothing new follows. Corollary 1.4 is weaker than
`gottschalk-reduces-to-fg-simple-kazhdan-groups` as a reduction of hosts. What it adds is
that the window difference normally generates the monolith of the descended host.

## 2. Transposed hinges

**Lemma 2.1.** In any group, if `s m = s' m' =: c`, then

```text
(m' s')^(-1) (m s)  =  s'^(-1) [m'^(-1) m, c] s',         [a,b] = a b a^(-1) b^(-1).
```

*Proof.* Expand the right side as `s'^(-1) m'^(-1) m c m^(-1) m' c^(-1) s'`. From
`c = s' m'` we get `c^(-1) s' = m'^(-1)`, and from `c = s m` we get `c m^(-1) = s`. So the
right side is `s'^(-1) m'^(-1) m s = (m' s')^(-1)(m s)`. QED

So the reverse identification `(m,s) ~ (m',s')` that transposes a forward identification
`(s,m) ~ (s',m')` holds **exactly when the left memory difference `m'^(-1) m` commutes with
the common product `c = s m`.**

**Corollary 2.2.**

1. *Commutator subgroup.* Every transposed hinge lies in `[H,H]`. No abelian quotient ever
   detects a failed transpose, so the abelianization filter
   `two-cell-window-differences-die-in-host-abelianization` never sees one. For
   identifications in the marked class, `c = 1` and the transpose always holds.
2. *Rooted identifications.* If `s' = 1` is the root decoder address, then `c = m'` and
   the hinge is `[m'^(-1) m, m'] = [m'^(-1), m]`, the commutator of two memory letters.
   Shift–shear identifications `(h_r, v_r) ~ (1_S, u_r)` are rooted, and their transposed
   hinges are `[u_r^(-1), v_r]`.
3. *Commuting tables.* If every forward identification of `E` has a left difference
   commuting with its common product in `U_E`, then `T_r(U_E)` contains the transpose of
   `E`. That forces surjectivity only in the cases already recorded by
   `boolean-core-is-uniform-single-demand-network-coding` (one relay or one column). It
   is not claimed in general.

**Example 2.3 (the defect is a transposed hinge).** In the nine-leaf configuration put

```text
m' = u c^(-1) u^(-1),     m = l,     s = m' m^(-1) = u c^(-1) u^(-1) l^(-1).
```

The rooted identification `(s, m) ~ (1, m')` holds, because `s l = u c^(-1) u^(-1)`. By
Corollary 2.2(2), its transposed hinge is

```text
[m'^(-1), m] = [u c u^(-1), l] = d,
```

the defect of `defect-window-automaton-over-leavitt-units`.

## 3. The re-aimed defect-window target

Put the three sections together.

* Forcing is free but bijective (`bijective-designs-force-every-finite-presentation`), and a
  bijective gadget never changes strictness. So a rule pair for the claim must force its
  core through its own irreversible part.
* By Corollary 1.3, the window difference `d` must lie in the hinge closure of every
  minimal reverse partition of the pair's table group. The reverse hinges have to
  normally generate the defect. Inside its own tables, the design must do to `d` what
  soficity does.
* By Example 2.3, `d` is the hinge of one transposed rooted identification.

**The most direct shape.** A rule pair whose forward sufficiency needs the rooted
identification `(u c^(-1) u^(-1) l^(-1), l) ~ (1, u c^(-1) u^(-1))`, and whose every minimal
reverse-sufficient partition identifies the transposed cells
`(l, u c^(-1) u^(-1) l^(-1)) ~ (u c^(-1) u^(-1), 1)`.

Such a pair is strict over every realization whose forward table dominates its forward
partition and in which `d != 1`, the Leavitt unit group included. There, no minimal
reverse partition is dominated, so by (T) the encoder is injective and not surjective. The
hinge-closure condition of Corollary 1.3 then holds automatically. The pair would refute
Gottschalk even if its Garden of Eden sat on a window other than `{1, d}`.

**Where it dies.** At the rules. No rule pair is known whose reverse sufficiency needs the
transpose of an identification that its forward sufficiency needs.

* When `S = {1}` or `M = {1}`, the transpose always suffices
  (`boolean-core-is-uniform-single-demand-network-coding`).
* A strict pair needs a nonamenable decoder memory group and a nonsofic encoder memory
  group (`amenable-decoder-memory-forces-surjectivity`). So it needs at least three
  addresses on each side.
* Shift–shear pairs need only rooted identifications with trivial transposed hinges,
  because their inverse is built from inverse translations.
* The rooted identification is a tree edge of the difference graph, so it holds over the
  free group on the memory letters. By `free-memory-injectivity-forces-universal-bijectivity`,
  a strict encoder is not injective over that free group, nor over any surjunctive cover
  of its memory group. So the pair's forward sufficiency must also need cycle relators,
  and its injectivity must use relations that fail in every surjunctive cover. The
  nesting relator of `nested-rigid-defects-force-nonsurjunctivity` is the candidate. The
  configuration relators that make `d` invisible are not enough on their own.

This section is a design target, not a result.
