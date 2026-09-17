---
rg: 2
id: one-rest-donor-covering-count-proof
kind: route
title: The donor map is onto the active input sites, and a conserved active count would make the automaton surjective
target: one-rest-donor-covering-strict-automata-raise-the-count
requires:
  - finite-injective-positive-charge-automata-are-surjective
---

**Import, verbatim** (`finite-injective-positive-charge-automata-are-surjective`): "Let G be any group and A a finite
alphabet with distinguished symbol 0. Let w:A->R satisfy w(0)=0, w(a)>0 for every a!=0. Let tau:A^G->A^G be a
cellular automaton fixing the all-zero configuration. A configuration is finite if it equals 0 outside a finite set.
Suppose: 1. For every finite x, sum_g w(tau(x)(g))=sum_g w(x(g)). 2. Tau is injective on the set of finite
configurations. Then tau is bijective on the finite configurations of each prescribed total charge and is surjective
on A^G."

**Item 1.** `d` is defined only where `μ(u) ∈ B`, and then `u(d(u)) ∈ B`, by (D1) at the identity site. `0^M` has no
active entry, so `μ(0^M) = 0`, and `τ(0^G) = 0^G`. If `ℓ` is `0` off a finite set `S`, then `τ(ℓ)(g) ≠ 0` forces
`gM ∩ S ≠ ∅`, i.e. `g ∈ S M^(-1)`, a finite set.

**Item 2.** By (D1), `g ↦ D_ℓ(g)` maps the active sites of `τ(ℓ)` into those of `ℓ`. By (D2) it is onto. So
`|τ(ℓ)| >= |ℓ|`.

**Item 3.** Suppose `|τ(ℓ)| = |ℓ|` for every finite `ℓ`. Take `w(0) = 0` and `w(b) = 1` for `b ∈ B`. Then condition 1
of the import holds, `τ` fixes `0^G` by item 1, and `τ` is injective, in particular on finite configurations. The
import makes `τ` surjective. So a non-surjective `τ` raises the count on some finite configuration, and by item 2 it
never lowers it.
