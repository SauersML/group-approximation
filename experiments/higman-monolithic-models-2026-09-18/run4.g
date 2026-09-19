Read("mono3.g"); Read("perm.g");
for e in [3,4,5] do
  Read(Concatenation("p",String(e),".g")); P := F;
  Print("e=",e,"\n");
  r := MonoPc(P, e, 6);
  m := Minimum(List(r, x->x[1]));
  for x in Filtered(r, x->x[1]=m) do PermInfo(P, e, x); od;
od;
QUIT;
