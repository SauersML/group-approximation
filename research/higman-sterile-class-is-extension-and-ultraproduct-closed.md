---
rg: 2
id: higman-sterile-class-is-extension-and-ultraproduct-closed
kind: claim
title: The groups receiving only trivial maps from Higman's group form a class closed under subgroups, extensions, directed unions, direct products, algebraic ultraproducts, local embeddings, wreath and free products; it contains every LEF, linear, periodic, subexponential-growth and BS(1,2)-free group, hence every Juschenko--Monod and periodic Nekrashevych simple group, so the Helfgott--Juschenko question and (HMF5) live exactly at the quotient step
distinct_from:
  nontrivial-higman-quotients-are-not-locally-elementary-amenable: that uses the class D of groups whose nontrivial f.g. subgroups have nontrivial finite quotients, closed under Chou's operations; this uses the strictly larger Higman-sterile class S, which also contains f.g. infinite simple groups (periodic, subexponential-growth, BS(1,2)-free or low-distortion ones), and is closed under direct products, algebraic ultraproducts, local embeddings and free products as well. That claim says it is silent on f.g. infinite simple amenable groups; this one reaches the Juschenko--Monod, LRF-full-group and periodic Nekrashevych families.
  hmf5-forces-higman-to-have-no-amenable-quotient: that proves (HMF5) implies (NAQ) and says a proof must exclude Juschenko--Monod quotients; this proves those are already excluded unconditionally, reformulates (NAQ) as "every amenable group is Higman-sterile" and (HMF5) as "every matrix-corona unitary group is Higman-sterile", and locates both at the one operation S lacks, taking a quotient.
  full-mf-radical-groups-form-an-extension-colimit-class: that is the class Rad_MF(G)=G, closed under quotients, extensions and colimits (the class of Hig itself, conjecturally); this is its orthogonal, the class of targets receiving no nontrivial map from Hig, closed under subgroups, extensions, products, ultraproducts and local embeddings but not under quotients.
  nontrivial-higman-quotients-keep-all-four-bs-subgroups: that is a structural fact about each nontrivial quotient; this uses it (with the tower-distortion bound) as the base case of a closure theorem about targets.
artifacts:
  - research/higman-sterile-class-is-extension-and-ultraproduct-closed-proof.md
---

**ESTABLISHED (swarm-0917 w14, agent-verified, no referee)** by route
`higman-sterile-class-is-extension-and-ultraproduct-closed-proof`. The proof is
elementary modulo standard imports: Malcev's theorem (f.g. linear groups are
residually finite), the Kurosh-type fact that the kernel of `G*H -> G x H` is
free, Grigorchuk--Medynets (via
`residually-finite-minimal-actions-have-lef-full-groups`), and the standard facts
about hyperbolic and CAT(0) groups already imported at statement level by
`nontrivial-higman-quotients-have-tower-distorted-generators`. No novelty is
claimed for the individual closure steps. The point is the combined class and
what it removes from the Higman lane.

**Setting.** `Hig = H4 = <a,b,c,d | b^a=b^2, c^b=c^2, d^c=d^2, a^d=a^2>`, with
`x^y = y^-1 x y`. A group `G` is **Higman-sterile** if every homomorphism
`Hig -> G` is trivial. Write `S` for the class of Higman-sterile groups.

**Theorem.**

1. **Closure.** `S` is closed under
   - (a) subgroups;
   - (b) extensions: if `N` is normal in `G` and `N, G/N` lie in `S`, so does `G`;
   - (c) directed unions;
   - (d) arbitrary direct products, hence residually-`S` groups lie in `S`;
   - (e) algebraic ultraproducts `prod_omega G_i` over any ultrafilter, when
     `omega`-almost every `G_i` lies in `S`;
   - (f) local embeddability: a group locally embeddable into `S` lies in `S`;
   - (g) restricted permutational wreath products `L wr_X K` with `L, K` in `S`;
   - (h) free products `G * H` with `G, H` in `S`.
2. **Non-closure.** `S` is not closed under quotients (`F_4 ->> Hig`), nor under
   amalgamated free products over free subgroups. Hig is built from `BS(1,2)`,
   which lies in `S`, by two rounds of amalgamation (Higman's standard
   decomposition), and Hig is not in `S`.
3. **Base members.** `S` contains:
   - finite groups, and more generally every group in the class `D` (every
     residually finite and every elementary amenable group);
   - every group with no subgroup isomorphic to `BS(1,2)`. This covers periodic
     groups, groups of locally subexponential growth (nilpotent, intermediate
     growth), hyperbolic groups and CAT(0) groups;
   - every group with an element-order or distortion obstruction. If each
     f.g. subgroup has infinite cyclic subgroups whose distortion is bounded by an
     iterated exponential of fixed height, the group lies in `S`;
   - every linear group, over any field.
4. **Consequences.** `S` contains, among others:
   - every LEF group, every group locally embeddable into elementary amenable
     groups, every residually linear group, every algebraic ultraproduct of
     finite or linear groups, and `prod_n U(k_n)`;
   - every topological full group `[[T]]` of a Cantor minimal system and its
     derived subgroup `[[T]]'` (the Juschenko--Monod simple amenable groups);
   - `[[alpha]]` for LRF actions, and every f.g. subgroup of
     `GL_m(LC(X,F_q) x| Gamma)` covered by `lrf-cantor-actions-give-lef-full-and-elementary-groups`;
   - Nekrashevych's f.g. infinite simple periodic groups of intermediate growth
     (Ann. of Math. 187, 2018), and every group of intermediate growth.
5. **(NAQ) and (HMF5) as sterility statements.**
   - (NAQ) (Hig has no nontrivial amenable quotient) holds iff every amenable
     group is Higman-sterile.
   - (HMF5) holds iff for every dimension sequence `(k_n)` the corona unitary
     group `U_(k) = prod_n U(k_n) / N_(k)` lies in `S`, where
     `N_(k) = {(u_n) : ||u_n - 1|| -> 0}`. Here `prod U(k_n)` and `N_(k)` both lie
     in `S`, by (3) and (1d, 1a). So (HMF5) asks whether one specific quotient of
     an `S`-group by a normal `S`-subgroup stays in `S`. That is exactly the
     operation under which (2) shows `S` is not closed.
   - Likewise Hig has a nontrivial sofic quotient iff some metric ultraproduct
     `prod_omega (Sym(n_i), d_Hamming)` is not in `S`. Each such group is a
     quotient of the algebraic product `prod Sym(n_i)`, which lies in `S`.
6. **Residual (NAQ).** Suppose `Hig` has a nontrivial amenable quotient. Then it
   has a quotient `Q` that is f.g., infinite, simple and amenable, and `Q` lies
   outside `S`. So `Q` is not locally embeddable into any group of `S_0`, where
   `S_0` is the closure of the base members in (3) under the operations (1a)-(1h).
   Moreover `Q` has four embedded copies of `BS(1,2)` and tower-distorted
   generators. In particular `Q` is neither a subgroup of a Juschenko--Monod group
   nor of any group in (4). This corrects the obligation stated in
   `hmf5-forces-higman-to-have-no-amenable-quotient`: a proof of (HMF5) need not
   exclude Juschenko--Monod quotients, since none exist. It must exclude f.g.
   simple amenable groups outside `S_0`.

## Class kill

**Class.** Approaches that refute (NAQ) or (HMF5), or build a nontrivial
sofic, amenable or MF quotient of Hig, by producing a nontrivial map
`Hig -> G`, where `G` is assembled from the following:
* building blocks: finite, abelian, linear, periodic, subexponential-growth,
  hyperbolic, CAT(0) or `BS(1,2)`-free groups, and topological full groups of
  minimal or LRF Cantor actions;
* operations: subgroups, extensions, directed unions, direct products,
  algebraic ultraproducts, local embeddings, wreath products or free products.

This covers:
* the direct "find an amenable simple quotient among known simple amenable
  groups" search, since Juschenko--Monod, LRF and periodic Nekrashevych groups
  all lie in the class;
* residual or local-approximation schemes over these targets.

**Invariant.** Membership of the target in `S`.

**Step where every member dies.** The pullback along the operation tree. Each
closure step (1a)-(1h) pulls a nontrivial map `Hig -> G` back to a nontrivial
map into one of the pieces:
* the normal subgroup or the quotient of an extension;
* a single factor of a product;
* `omega`-almost every factor of an ultraproduct (the four relators hold on an
  `omega`-large set);
* the finite piece of a local embedding;
* the Cartesian free subgroup of a free product.

At a leaf the map dies:
* on a finite, residually finite or `D`-group, by Higman's theorem;
* on a periodic, subexponential or `BS(1,2)`-free leaf, by
  `nontrivial-higman-quotients-keep-all-four-bs-subgroups`;
* on a low-distortion leaf, by
  `nontrivial-higman-quotients-have-tower-distorted-generators`;
* on a linear leaf, by Malcev.

**Where it stops.** Every surviving approach must, at some step, pass to a
quotient by an infinite normal subgroup that does not preserve `S`. This
includes a metric ultraproduct (sofic or hyperlinear), a norm corona `U_(k)`
(MF), or a quotient of a group in `S`, as in (5). Equivalently, a nontrivial
amenable Higman quotient is an amenable group of a kind the repository has no
example of: f.g., simple, not locally embeddable into `S_0`.

**Still open.** Whether every f.g. amenable simple group lies in `S`, which is
equivalent to (NAQ). Whether Nekrashevych's non-torsion fragmentation groups,
or other amenable simple groups not covered in (4), lie in `S_0`. (HMF5) itself.

DERIVATION
higman-sterile-class-is-extension-and-ultraproduct-closed-proof
