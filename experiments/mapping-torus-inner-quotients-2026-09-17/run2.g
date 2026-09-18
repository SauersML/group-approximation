Read("inner2.g");
for q in [5,7,8,9,11,13] do search(Concatenation("PSL2_",String(q)), Image(IsomorphismPermGroup(PSL(2,q))), "fig8", 4); od;
for q in [5,7] do search(Concatenation("PSL2_",String(q)), Image(IsomorphismPermGroup(PSL(2,q))), "id", 3); od;
Print("DONE\n"); QUIT;
