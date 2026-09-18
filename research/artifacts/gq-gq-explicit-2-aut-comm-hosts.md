# Automorphism-type and commensurator hosts for GL_n(Q) (gq-explicit-2, 2026-09-17)

Lane `gq-explicit-2`: second attack on Problem 2.7
(`gl-n-q-explicit-natural-fp-overgroup`), family "automorphism groups and abstract
commensurators". That is the row the 2.7 host table listed as untested. All proofs are
lane proofs, not independently reviewed.

## 1. Results landed

| Node | Status | Content |
|---|---|---|
| `fg-automorphism-hosts-contain-no-divisible-subgroup` | ESTABLISHED (lane) | `Aut(Γ)` for finitely generated residually finite `Γ` is residually finite (Baumslag's argument). Finitely generated subgroups of `Aut_K(X)`, for `X` separated of finite type over any field, are residually finite (the Bass--Lubotzky argument, reproved). So none contains `(Q,+)`. |
| `fg-cremona-subgroups-have-arithmetic-linear-part` | ESTABLISHED (lane) | In a finitely generated `Γ <= Bir(P^m_Q)`, `Γ ∩ PGL_{m+1}(Q) ⊆ PGL_{m+1}(Z[1/N])`, by good reduction of birational maps modulo primes. So no linearizable copy of `(Q,+)`, and no standard copy of `GL_n(Q)`, lies in a finitely generated Cremona subgroup. |
| `comm-of-z-n-times-torsion-group-splits` | ESTABLISHED (lane) | `Comm(Z^n x B) = GL_n(Q) x Comm(B)` for torsion `B` with trivial FC-centre. So `Z^n x (Grigorchuk group)` has commensurator `GL_n(Q) x V(Grig)`, which is not finitely generated. |

## 2. Status of the family

**Dead, under every embedding:**
- automorphism groups of finitely generated residually finite groups, including
  `Aut(F_k)`, `Aut(π_1 Σ_g)`, `Aut(RAAG)`, and `Aut` of finitely generated linear or
  polycyclic groups;
- finitely generated groups of automorphisms of varieties, including polynomial
  automorphisms and tame groups.

**Dead for the natural (linearizable) copy:** Cremona groups over `Q`. A non-linearizable
copy of `(Q,+)` in a finitely generated Cremona subgroup would make that subgroup not
residually finite. Whether finitely generated Cremona subgroups are residually finite is
reported as an open question of Cantat (the wording was not found at a readable
primary source during this pass). So a Cremona host is at least as hard as answering
that question negatively. See also `kazhdan-subgroups-of-cremona-groups-are-residually-finite`.

**Not finitely generated, so no host:**
- `Comm(Z^n) = GL_n(Q)`;
- `Comm(Z^n x B)` as above;
- `Comm(SL_n(Z)) = PGL_n(Q) x| Z/2`, `n >= 3` (Margulis; context from
  `gq-gq-k2-q-uniformity.md`);
- `com(F)`: "We show com (F) is not finitely generated" (Burillo--Cleary--Röver,
  arXiv:0711.0919v4, abstract).

  One remark on `com(F)`. BCR describe it by PL homeomorphisms of `R` whose germs at
  `±∞` should commensurate `x -> x+1`. That description was not read at the source (the
  PDFs did not extract). If it holds, every finitely generated subgroup of `com(F)` omits
  `Aff(Q)`. The argument:
  - the germ map at `±∞` lands in `Comm_inf x Comm_inf`, and
    `commensurating-end-germ-groups-omit-aff-q` handles each factor;
  - a nontrivial normal subgroup of `Aff(Q)` contains `Q` (Attempt 1 of the 2.7 root),
    so `Aff(Q)` embeds in one factor;
  - the compactly supported kernel has no `(Q,+)`, by the root-counting argument of that
    Attempt.

**Open sub-questions** (sparks, not pursued):
- **S1.** Is `(Q,+)` a subgroup of `Aut(V)`? By Bleak--Cameron--Maissel--Navas--Olukoya,
  `Aut(V_n)` consists of homeomorphisms given by bi-synchronizing transducers (context,
  not read). `V` has no `(Q,+)` and no `Z[1/2]` (Higman). So a copy would meet `V` in a
  cyclic group or trivially, and map to `Out(V)` with kernel of rank at most 1.
- **S2.** Can a finitely generated branch or self-replicating group `Δ` have a finitely
  generated `Comm(Δ)` containing `GL_n(Q)`? For branch `Δ` the commensurator acts by
  almost-automorphisms of the tree. `PGL_2(Q) <= PGL_2(Q_p) <= Aut(T_{p+1})`, so
  almost-automorphism groups do contain `PGL_2(Q)`. The obstacle is finite generation:
  the natural local groups are `PGL_2(Z_(p))`, and the piece lemmas kill those.
- **S3.** `Aut(nV)` and `Aut(SV_G)` are the normalizers of these simple groups in the
  homeomorphism groups of their Cantor spaces (Rubin). They are hosts only if the
  simple groups nearly are.

## 3. A remark on FW for SL_n(Q)

`gq-gq-critic.md` §2 asks what property FW of `SL_n(Q)` (`n >= 3`) would give. It fails,
for a reason that has nothing to do with `SL_n`.
- **Every countable, non-finitely-generated group lacks FA, hence FW** (Serre, *Trees*,
  I.6.1, Theorem 15: a countable group with FA is finitely generated). The union
  `G = ⋃_m G_m` of a strictly increasing chain of subgroups acts without fixed point on
  the coset tree with vertex set `⊔_m G/G_m`.
- **For `G = SL_n(Q) = ⋃ SL_n(Z[1/m!])`** the vertex stabilizers are conjugates of
  `SL_n(Z[1/m!])`, which are residually finite. So even `(Q,+) <= SL_n(Q)` fixes no
  vertex. It is a union of elliptic cyclic groups and fixes a unique end.
- **Consequence.** No fixed-point property of the whole of `SL_n(Q)`, `GL_n(Q)` or
  `Aff(Q)` on trees or cube complexes is available. Arguments must use finitely
  generated subgroups (for example `SL_3(Z)`, which has (T)) together with the
  divisibility of `(Q,+)`.

## 4. Relation to other lanes

- Complements `gq-explicit-fp` (host classes), `gq-bt-kojima` and `gq-nv-obstruct`
  (`nV`), and the ring lanes (`E_N`, Leavitt).
- Not a duplicate of the piecewise lemmas (critic D1). Those use the finite generation
  of a piece group; here the tools are finite quotients of automorphism groups,
  reduction of birational maps, and intrinsic subsets of commensurators.
