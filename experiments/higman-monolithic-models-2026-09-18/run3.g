Read("mono3.g"); R := rec();
for e in [3,4,5] do
  Read(Concatenation("p",String(e),".g")); P := F;
  Print("e=",e," |P|=2^",Log(Size(P),2),"\n");
  R.(e) := MonoPc(P, e, 10);
od;
QUIT;
