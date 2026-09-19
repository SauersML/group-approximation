R := rec();
Read("mono2.g");
for e in [3,4,5] do
  Read(Concatenation("p",String(e),".g")); P := F;
  Print("e=",e," |P|=2^",Log(Size(P),2),"\n");
  R.(e) := MonoPc(P, e, 8);
od;
QUIT;
