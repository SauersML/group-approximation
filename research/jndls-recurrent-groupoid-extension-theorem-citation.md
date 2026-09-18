---
rg: 2
id: jndls-recurrent-groupoid-extension-theorem-citation
kind: route
title: Import §3.1 and Theorem 3.1 of Juschenko–Nekrashevych–de la Salle, arXiv:1305.2637v2
target: jndls-recurrent-groupoid-extension-theorem
requires: []
---

Imports the passages quoted in the claim from K. Juschenko, V. Nekrashevych and M. de la Salle,
arXiv:1305.2637v2 (24 May 2013). swarm-0917-w13-w13-f-last1 extracted the text from the arXiv PDF
with `pypdf` on 2026-09-18 and checked it line by line against the quotations. Only the definitions
and the statement are imported. The downstream theorem `thompson-f-recurrent-germ-criteria-return-f-as-an-input`
uses only the definitions of germ, isotropy group and topological full group, and the four
hypotheses of Theorem 3.1, not its conclusion.
