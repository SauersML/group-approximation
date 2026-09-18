---
rg: 2
id: fp-rf-groups-embed-in-hnn-recursive-annular-germ-groups
kind: claim
title: Every finitely presented residually finite group is a passenger in a finitely presented HNN-recursive annular germ group over V, driven by an ascending machine and pinned by single-depth relations
requires:
  - fp-annular-germ-groups-are-hnn-recursive
  - bishop-schesler-branch-groups-are-annular-hosts-over-v
  - dynamically-v-separated-groups-satisfy-boone-higman
distinct_from:
  dynamically-v-separated-groups-satisfy-boone-higman: that needs the input itself inside an fp group with an ascending endomorphism whose V-orbit separates it; here only a driving machine M is ascending, and the input's depth data is pinned by single-depth relations to M's data without being a word in it.
  fp-rf-boone-higman-via-fp-self-similar-overgroups: that asks for self-similar (virtual-endomorphism) overgroups on a regular tree; this allows a non-ascending transport, defined on the machine part only.
---

**OPEN** (target; the design and the reduction are lane work, not reviewed).

**Why this shape.** By `bishop-schesler-branch-groups-are-annular-hosts-over-v`, every
`EFRF^+` group `G` sits in the germ group at one rational point of an annular host over `V`,
with depth data `r_n: G → Q_{n+2} ↪ V` read off a computable residual chain. By
`fp-annular-germ-groups-are-hnn-recursive`, any finitely presented such host has germ group
`⟨L, s | s^{-1} ℓ s = θ(ℓ), ℓ ∈ L_1⟩`. Its two extreme cases are already dead:
- free zoom (`L_1 = 1`);
- depth-disjoint storage (`H ≀ Z`), `depth-disjoint-spinal-hosts-have-wreath-germ-groups`.

The ascending case `L_1 = L` needs the input itself to be dynamically V-separated in an fp group.

**Conjecture (passenger form).** For every finitely presented residually finite group `G` (these are `EFRF^+`) there are:
1. **(driver)** a finitely presented group `M`, an injective endomorphism `μ: M → M` and
   `ρ: M → V`. These give the machine germs `m̂`, acting at depth `n` by `ρ(μ^n(m))`.
2. **(passenger)** a residual chain of `G`, depth data `r_n: G → V` through `G/N_n`, and
   finitely many words `R_1, …, R_k` in `G`, `M` and one extra letter. Then:
   - `r_n(G)` together with `ρμ^n(M)` satisfies every `R_j` at every depth `n ≥ n_0`;
   - `r_n` is the **only** such family at each depth (local rigidity).
3. **(gluing)** `L := ⟨M̂, Ĝ⟩` is presented by the relations of `M`, of `G` and the `R_j`, and
   the Belk–Hyde–Matucci SingFix groups of `⟨V, M̂, Ĝ⟩` are finitely presented.

The germ group is then the non-ascending HNN extension `⟨L, s⟩` with `L_1 = M̂` and `θ = μ`.
By gates 1–3 it is finitely presented, and Theorem 2.1 would make the full host finitely
presented. So
`G ∈ B_A`, by `fp-clopen-transitive-full-cantor-groups-have-type-a-actions`.

**What it would give.** Boone–Higman for all finitely presented residually finite groups, and so for BBMZ 5.3(2), (3), (7)
and (12) together: closed mapping class groups, `Out(F_n)`, fp metabelian and fp residually
finite groups.

**Calibrations.**
- `M = G`, `μ` ascending with dynamic separation: this recovers
  `dynamically-v-separated-groups-satisfy-boone-higman` (passenger = driver).
- `M` trivial: this is the depth-disjoint or free-zoom storage, which is dead. Pinning cannot
  hold, because deep data can be perturbed.

**The gap (precise).** Gate 1 is easy: `V` itself with a cone-contraction endomorphism.
Gate 2 is the crux. The driver's depth data `ρμ^n(M)` all lie in the fixed group `ρ(M)`. So
the passenger's depth-`n` action through the growing finite groups `G/N_n` must be pinned by
finitely many single-depth equations relative to a fixed group. The chain's growth must
therefore be carried by *where* `μ^n` sends the machine inside `ρ(M)`: its support pattern, or
its conjugacy data. It cannot be carried by new group elements. A candidate is a reversible
machine `R ∈ V` with `μ = conj(R)` on part of `M`. The chain `(Q_n)` is computed by the machine
run and read by the passenger through commutation and conjugation equations with trivial
centralizers. Uniqueness then comes from centralizers of the machine data in `V` being trivial.
Not attempted beyond this design.

## Lesson for general BH

The Bishop–Schesler reduction concentrates BBMZ 5.3(2), (3), (7) and (12) into one
one-point question. Can a *finitely presented ascending driver* pin, by single-depth
equations, an input's residual chain written one finite quotient per depth? This is the
one-point, V-germ incarnation of the master route's "compiler". The driver is the machine;
the passenger pinning is the rigidity.

## Attempts

**Attempt 1 (bh-major-branch-c, 09-18): the pinning step (gate 2), with the calibrations F₂, SL₃(Z) and surface groups.** Two structural constraints are landed; no driver has been constructed.

- `pinned-annular-passengers-are-class-functions-of-the-driver`. Pinned depth data are fixed by every automorphism of V that fixes the driver datum. So the pinned quotient `G/N_n` depends only on the `Aut(V)`-class of `ρ∘μ^n`, and growth needs an infinite `μ*`-orbit in `Hom(M,V)/Aut(V)`. Four driver families are dead:
  - `Aut(V)`-induced drivers, including the "`μ = conj(R)`, `R ∈ V`" candidate above when it acts on all of `M`;
  - cone-copy drivers;
  - faithful diagonal (block-doubling) drivers;
  - more generally, any faithful driver that confines the passenger inside `ρμ^n(M)`. Such a driver collapses to the ascending case.
- `pinned-passengers-collapse-when-the-shifted-system-is-solvable`. If the pinning system with shifted parameters `μ̂(m̂)` has any solution in the base `L`, the passenger is a driver germ. So a genuine non-ascending passenger needs "a unique solution in `V` at each depth" together with "no solution in `L`".

**Calibrations.**
- **F₂.** F₂ ≤ V, so constant data realize it ascendingly. It says nothing about pinning growing finite quotients.
- **SL₃(Z) and other Kazhdan inputs.** Their V-images are finite, since V is Haagerup (Farley). By bh-free-22's remark, they are never their own telescopes. They could still be passengers in a larger telescope `M̂` (`Ĝ ≤ M̂` with `μ̂(G) ⊄ G`), and that is not excluded here. So SL₃(Z) is a genuine test of this framework, even though it satisfies BH by linearity.
- **Closed surface groups.** Not attempted.

**What remains for gate 2.** A driver `(M, μ, ρ)` must satisfy all four of these:
- `ρ∘μ^n` are pairwise non-`Aut(V)`-conjugate;
- `ρ` is non-faithful with varying kernels, or `Γ_n = ρμ^n(M)` has small double centralizers;
- a finite system pins `r_n(G)` uniquely at each depth;
- the shifted systems are unsolvable in `L`.

No natural driver meets these. The next test is a non-faithful driver from a reversible counter machine acting on the annulus, with `ρμ^n` reading the machine's configuration at time `n`.
