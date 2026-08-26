# MSI audit: balanced cross matrix-unit Morita escape

Date: 2026-08-26

Execution policy: MSI wrapper only; no local Python or Lean execution.

The audit was run through

```text
/Users/user/msi-node/msi
```

after loading the shared Python module.  It checked, over `F_2`:

- all four products `s_i t_j=e_ij`;
- all sixteen cases of `e_ij s_k=delta_(j,k)s_i` and
  `t_k e_ij=delta_(k,i)t_j`;
- `t_i s_j=delta_(i,j)h` and `p!=h` in `M_3(F_2)`;
- the aggregate and common-opposite returned-arm commutator table after
  flattening `GL_7(M_3(F_2))` into `GL_21(F_2)`;
- both range and reverse completeness products;
- the parent Whitehead braid;
- the private-middle Whitehead, all four positive/reverse cross commutators,
  both complementary partial Whiteheads, and their parent exchange;
- literal spare-root commutator witnesses for the full balanced cross-action
  table; and
- nontriviality of the marked `q_1` root.

The final combined job exited with status `0` and printed:

```text
exact GL_21(F2) private-middle plus balanced-cross-action Morita model; p != h; marked q1 survives
```

The checked source is
`experiments/balanced_cross_matrix_unit_morita_escape.py`.
