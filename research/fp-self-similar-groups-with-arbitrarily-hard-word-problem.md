---
rg: 2
id: fp-self-similar-groups-with-arbitrarily-hard-word-problem
kind: claim
title: For every recursive time bound some finitely presented self-similar group has a harder word problem
distinct_from:
  fp-simple-groups-with-arbitrarily-complex-word-problem: that is the root asking for finitely presented SIMPLE groups beyond every recursive bound; this asks the same for finitely presented self-similar groups, and it implies that root through Zaremsky's embedding.
  every-fp-rf-group-embeds-in-fp-self-similar-group: that asks for a self-similar overgroup of EVERY finitely presented residually finite group; this asks only for one hard self-similar group per recursive bound, a much weaker existence statement that the embedding claim implies.
  kms-arbitrarily-hard-fp-rf-groups: that realizes arbitrarily hard word problems by finitely presented residually finite solvable groups with no tree action required; this requires the hard group itself to be finitely presented and self-similar.
---

**OPEN.** For every recursive `T: N -> N` there are `d >= 2` and a finitely
presented self-similar group `G <= Aut(T_d)` whose word problem has no
algorithm running in time `C*T(C*l) + C*l + C` for any constant `C`.

**Why it matters.**
- By `arbitrarily-complex-fp-simple-via-hard-self-similar-groups` it implies
  `fp-simple-groups-with-arbitrarily-complex-word-problem`, unconditionally.
  That would remove the only complexity-based counterexample route to
  `boone-higman-conjecture`: a counterexample from word-problem complexity alone
  needs a recursive bound shared by all finitely presented simple groups.
- By `rover-nekrashevych-word-problem-reduces-to-self-similar-group` it is
  also *necessary* for the Rover--Nekrashevych branch of that root. That
  construction never makes a simple host harder than its self-similar input,
  beyond exponential rescaling.

## Necessary conditions

- **Infinitely many states.** Automaton groups and contracting self-similar
  groups consist of rational homeomorphisms. Their word problems share one
  exponential bound (`rational-homeomorphism-subgroups-have-exponential-wp`), so
  the wall `complexity-bounded-host-classes-are-not-universal` excludes them as
  a family. A hard example must have a generator with infinitely many distinct
  sections, as condition (N2) of `every-fp-rf-group-embeds-in-fp-self-similar-group`
  already says for the stronger claim.
- **Residual finiteness.** Every self-similar group is residually finite and
  residually `W_d` (condition (N1) of the same node). Hard finitely presented
  residually finite groups exist (`kms-arbitrarily-hard-fp-rf-groups`), so this
  is a screen on `d`, not an obstruction.

## Attempts

1. **Through the embedding claim.** The route
   `hard-self-similar-groups-from-fp-rf-embedding` derives this claim from
   `every-fp-rf-group-embeds-in-fp-self-similar-group`, applied to the
   Kharlampovich--Myasnikov--Sapir groups. It is open because that embedding
   claim is open, and it asks for far more than one hard example per bound.
2. **Self-similar affine groups over rings.** Zaremsky's Example 4.7 in
   arXiv:2405.09722 (imported through `fp-self-similar-groups-embed-in-fp-simple-groups`)
   covers `R^n x| GL_n(R)` over suitable rings. It lands inside linear groups
   over fields, whose word problems are classically low complexity
   (Lipton--Zalcstein for characteristic 0, Simon for positive characteristic;
   not imported here). So it cannot supply hard examples.
   *Dead as a source.*
3. **Direct virtual-endomorphism construction.** Not yet attempted. A group
   with a finite-index subgroup `H` and a homomorphism `phi: H -> G` of trivial
   core acts faithfully and self-similarly on the `[G:H]`-regular tree
   (Nekrashevych--Sidki). The task is a family of finitely presented groups
   with hard word problems carrying such `phi`, with `phi` non-contracting
   (by the first necessary condition). This session did not check the
   solvable KMS groups for virtual endomorphisms of trivial core.
   - *Partial kill (lane sw-010, 2026-09-17).*
     `virtually-endomorphic-self-similar-actions-have-finite-image` rules out
     every `phi` that agrees, on a finite-index subgroup, with an endomorphism of
     a finite-index normal subgroup. That covers generator substitutions,
     Frobenius-type scalings of the KMS groups and expanding integer-matrix
     affine maps; all of them give finite image. A candidate `phi` must be a
     genuine "division" map that extends to no such endomorphism, such as a
     Cartier-type digit contraction.
   - *Cartier test on the KMS groups (bh-free-25, 2026-09-18; lane computation, not
     reviewed).* Source: KMS arXiv:1204.6506v5 §4.1, read in the TeX
     (`gq/src/kms/KMS-322.tex`). There `T = ⟨⟨x_u⟩⟩` is abelian of exponent `p`
     (Lemma lT), `H_2` (the `a`-letters) is abelian, and in module notation the G8
     operator is `f*a_i = f·P_i` with `P_i = −1 + a_i − a_i^{-1} + (a_i')^{-1}`. An
     `Add` command `i → Add(n); j` reads `x_{q_iA_0} = x_{q_jA_0}·P_n`.
     - **Test map.** Take `H` generated by `T`, the normal closure of the `A`-letters,
       and the `p`-th powers of the `a`-letters; this has index `p^{|L_2|}`. Let
       `φ(a^p) = a` on those powers, fix the `x_u` and `A` generators, and act on
       `T` by the Cartier projection `C` that keeps the monomials whose `a`-exponents
       are all divisible by `p`. This is the lamplighter's self-similar map, which
       satisfies `C(ρ^{(p)} g) = ρ·C(g)`.
     - **It fails.** `C` sends the `Add` relation to `x_{q_iA_0} = x_{q_jA_0}·C(P_n)`,
       with `C(P_n) = −1`, since only the constant term of `P_n` has all exponents
       divisible by `p`. For `p = 2` this reads `x_{q_iA_0} = x_{q_jA_0}`. By KMS
       Theorem tmm(b), with all `a`-exponents zero, that equality holds in `G(M)` only
       if `q_iA_0 = q_jA_0` in `S(M)`. The `Add` command makes these differ by
       `a_n`, so the equality fails and `φ` is not a homomorphism.
     - **Design constraint.** A Cartier-type `φ` must move the configuration
       generators, `x_u ↦ x_{σ(u)}`. `C` divides counter values by `p`
       (`a^{pk} ↦ a^k`), so this asks for a Minsky-type machine whose relation module
       is carried into itself by "divide every counter by `p`". Call it a
       *`p`-adically self-similar* machine: its configuration relation must commute
       with that halving. Whether such machines can still have arbitrarily hard
       halting sets, compatibly with KMS's residual-finiteness proof (which needs
       sym-universal halting), is the open construction problem this reduces to.
       Nothing here is claimed as an obstruction.
     - *Follow-up (bh-free-25): binomial encodings are dead.* Suppose the command
       relations are binomials `x_q·a^n = x_{q'}·a^{n'}` in a free module over the
       commutative group ring of the counter letters. Suppose also that a
       Cartier-type `φ` acts as `C_0` (keep exponents divisible by `p`, divide them by
       `p`) together with a state relabeling `σ`, and that `φ` carries the relation
       submodule `R` into itself. Multiplying a relation by `a^m`, with `m ≡ −n`
       (mod `p`), shows `n ≡ n'` (mod `p`). Otherwise one side of the image survives
       alone and a configuration generator lies in `R`. `C_0` then turns the step
       `n' − n` into `(n' − n)/p`, which must again be a step of `R`, hence again
       divisible by `p`. By induction every step is divisible by every power of `p`,
       so it is zero. A working design therefore cannot store counters as exponents
       with monomial transitions. It must use genuinely polynomial operators, as KMS's
       `P_i` are, or odometer-style counters whose carries are the sections.

4. **Finite-state candidates are capped at PSPACE; scope of the Cartier kill**
   (bh-free-02, 2026-09-18).
   - *The cap.* By `automaton-tail-full-groups-have-conp-relative-word-problem`
     (item 2), every automaton group has word problem in `PSPACE`. So do its
     Rover--Nekrashevych and product 2-graph hosts. A finite-state witness can
     therefore serve this claim only for bounds `T` below `PSPACE`. The claim needs
     infinitely many states, as the first necessary condition says.
   - *The intermediate target.* A finitely presented automaton group with `NP`- or
     `PSPACE`-hard word problem is still open. It would give finitely presented
     simple groups beyond Birget's coNP. Wächter--Weiß's PSPACE-complete automaton
     group (STACS 2020; cited, not read) is not known to be finitely presented.
   - *Scope of the partial kill above.* It assumes `φ = σ ∘ C_0`, which kills every
     monomial `x_q a^n` with `p ∤ n`. A general semilinear `φ`, with `φ(a^p) = a`,
     is determined by arbitrary images of the `x_q a^r`, `0 <= r < p`, because the
     free module is free over `F_p[a^{±p}]` on these. The kill does not cover
     `φ` that send `x_q a^r`, `r != 0`, to nonzero elements. That is how the
     sections of lamplighter-type self-similar actions look. So "no monomial
     transitions" is proved only for `σ ∘ C_0`. General semilinear `φ` are untested.
