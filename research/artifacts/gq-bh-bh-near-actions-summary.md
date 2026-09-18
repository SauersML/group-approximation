# bh-near-actions: summary of the 09-18 pass

All nodes below are lane proofs, and none claims priority. Referee reviews exist only where noted.

## Near actions
- `lamplighters-in-v-show-near-action-neatness-is-no-bh-obstruction`: Cornulier's neatness theorem gives no
  Boone--Higman obstruction on inputs.

## Stein groups and interval exchanges (Juschenko--Monod type)
- **Obstruction.** `stein-derived-groups-need-computable-modules`: if `D(V(Γ,Λ,ℓ))` has solvable word problem
  on its f.g. subgroups, then `ℓ^{-1}Γ` consists of computable reals. For noncomputable `λ`, `D(V_λ)` is a
  2-generated simple group with unsolvable word problem.
- **Type (A).** `stein-v-groups-act-with-type-a-on-breakpoints`: finitely presented Stein V-groups act with
  type (A) on breakpoints. With Cleary's `F_∞`, all subgroups of quadratic-slope Stein V-groups satisfy
  Boone--Higman, including norm +1 slopes.
- **Contracting RSGs.** `pisot-stein-groups-are-contracting-rsgs`: for units `β` with (F), in any degree,
  `V(Z[β],⟨β⟩,ℓ)` is a contracting RSG on the β-shift. The key step is a uniform slope-defect bound from a
  conjugate-growth length lemma. **Referee-c: PASS with fixes (d1081f87a).**
- **Finite presentation.** `pisot-unit-slope-stein-groups-are-finitely-presented`: that same group is
  finitely presented, and `D(V)` is a finite-index finitely presented simple group. This is a positive answer
  to Tanner's question (2312.07375) for these slopes.
- **Corollaries:**
  - `pisot-interval-exchange-groups-satisfy-boone-higman`: IET groups over `Q(β)` of any rank up to
    `deg β`, minimal IET full groups, and Sturmian Juschenko--Monod groups with cubic angles (tribonacci,
    plastic, d-bonacci);
  - `quadratic-interval-exchange-full-groups-satisfy-boone-higman`: all real quadratic fields, via type (A);
  - `norm-minus-one-sturmian-jm-groups-satisfy-boone-higman`;
  - `pisot-box-exchange-groups-satisfy-boone-higman`.
- **Open:**
  - `transcendental-slope-thompson-groups-satisfy-boone-higman`: computable transcendental slopes, a
    Boone--Higman test case;
  - `every-real-number-field-lies-in-an-f-unit-field`: a number-theoretic reduction. A yes would give all
    algebraic IET groups.

## Priority and credit
- The quadratic Sturmian IET case was first done by bh-free-03 (`quadratic-rotation-iet-groups-...`) via
  substitutions.
- The golden `IE ⊂ V_τ` remark is Tanner's.
- bh-free-03's artifact §6 proposed the β-adic coding and identified the level-defect bound as the gap; that
  gap is closed here.

## Sources read at source
Cornulier 1901.05065; Tanner 2312.07375; Matui 2412.05492; BNR 2006.02401 and 1806.00108;
Grigorchuk--Medynets 1508.04454; BBMZ 2309.06224 (bh-free-03's copy); Frougny's survey; Akiyama, "Pisot numbers
and greedy algorithm". Not obtained: Cleary 1995/2000, Frougny--Solomyak 1992.
