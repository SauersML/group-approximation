# faithful irreducible degrees of small monolithic quotients (lower bound 2^(e-2) from the eigenvalue orbit)
Read("mono3.g");
for e in [3,4] do
  Read(Concatenation("p",String(e),".g")); P := F;
  Print("e=",e,"\n");
  r := MonoPc(P, e, 8);
  m := Minimum(List(r, x->x[1]));
  x := First(r, y->y[1]=m);
  Q := Image(NaturalHomomorphismByNormalSubgroupNC(P, x[3]));
  irr := Irr(CharacterTable(Q));
  Print("   |Q|=2^",m," faithful irreducible degrees ", Set(List(Filtered(irr, chi->Size(KernelOfCharacter(chi))=1), chi->chi[1])), " all degrees ", Collected(List(irr, chi->chi[1])), "\n");
od;
QUIT;
