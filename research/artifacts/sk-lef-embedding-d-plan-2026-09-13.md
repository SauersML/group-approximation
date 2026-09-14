# sk-lef-embedding-d plan: is the note's Z-family universal for LEF groups?

Lane sk-lef-embedding-d, 2026-09-13. Main retargeted this lane after sk-universal-embedding-b (22e2749154, unreviewed)
reported that f.g. LEF groups are exactly the subgroups of infinite f.g. simple Kazhdan LEF groups, using a lamplighter
host.

**Target.** Is every f.g. LEF group a subgroup of some `G_X = EL_3(LC(X,F_2) ⋊ Z)` with `X` an infinite minimal
Z-subshift? A yes makes the note's own family universal. A no needs an invariant of subgroups of `G_X`.

**Why it matters.** Subgroups of `G_X` already include free groups, `SL_3(F_2[t^{±1}])`, every finite group,
`[[σ]]'` and the `G_Y`. A universality theorem would give the note a one-line striking corollary. An obstruction would
show that the Z-family is special.

**Planned increments.**
1. Reduction (to establish). Every f.g. LEF group embeds in some `G_Y` iff every f.g. LEF group embeds in
   `GL_m(LC(X,F_2)⋊Z)` for some infinite minimal `X` and some `m`. The proof uses the Ore overgroup
   (`rf-groups-lie-in-derived-subgroups-of-rf-groups`, part 2), the Whitehead lemma `diag([a,b],1,1) ∈ E_3`, and the
   tower identity `M_m(R_X) ≅ R_(X^(m))` (`tower-subshift-elementary-group-is-el-3k-of-base`, PASS).
2. Necessary conditions (to establish). A f.g. subgroup of `GL_m(R_X)` acts faithfully on `⊕_Z F_2^m` with bounded
   propagation. Every subquotient module then has linear orbit-span growth. For finitely presented `Γ`, the periodic
   models become GENUINE representations `Γ -> GL_(mN)(F_2)`, injective on large balls, whose generators are cyclically
   band-limited with a uniform width.
3. Test object: `SL_3(Z)` (finitely presented, Kazhdan, CSP). Does it embed in some `G_X`? By 2, this is a question
   about band-limited F_2-representations of congruence quotients.
4. Open claim with Attempts: permutation encodings of expanders (bandwidth dies), dimension expanders (a conditional
   obstruction), and encodings via `F_2[t^{±1}]`-linear overgroups.

**Not duplicated.** sk-universal-embedding-b owns the lamplighter host. sk-lef-embedding-c owns the topologically free
subshift start. This lane is about the Z-family only.
