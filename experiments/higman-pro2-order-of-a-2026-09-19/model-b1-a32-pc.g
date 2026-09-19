# monolithic 2-quotient model m8 of order 2^14
MQ:=function()
local g1,g2,g3,g4,g5,g6,g7,g8,g9,g10,g11,g12,g13,g14,r,f,g,rws,x;
f:=FreeGroup(IsSyllableWordsFamily,14);
g:=GeneratorsOfGroup(f);
g1:=g[1];
g2:=g[2];
g3:=g[3];
g4:=g[4];
g5:=g[5];
g6:=g[6];
g7:=g[7];
g8:=g[8];
g9:=g[9];
g10:=g[10];
g11:=g[11];
g12:=g[12];
g13:=g[13];
g14:=g[14];
rws:=SingleCollector(f,[ 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2 ]);
r:=[
[1,g5*g8*g11*g14],
[3,g6],
[5,g8],
[6,g9],
[7,g14],
[8,g11],
[10,g14],
[11,g14],
];
for x in r do SetPower(rws,x[1],x[2]);od;
r:=[
[2,1,g4],
[3,1,g5],
[4,1,g7],
[6,1,g11],
[7,1,g10],
[9,1,g14],
[10,1,g12],
[12,1,g13],
[3,2,g6],
[5,2,g7*g12*g14],
[6,2,g9],
[7,2,g14],
[8,2,g12],
[13,2,g14],
[4,3,g7*g10*g11*g14],
[5,3,g8],
[7,3,g12*g14],
[8,3,g11],
[10,3,g12*g14],
[11,3,g14],
[5,4,g10*g13*g14],
[6,4,g14],
[7,4,g14],
[8,4,g13*g14],
[10,4,g14],
[12,4,g14],
[6,5,g14],
[7,5,g12*g14],
[10,5,g13],
[10,7,g14],
];
for x in r do SetCommutator(rws,x[1],x[2],x[3]);od;
return GroupByRwsNC(rws);
end;
MQ:=MQ();
Print("#I A group of order ",Size(MQ)," has been defined.\n");
Print("#I It is called MQ\n");

MEXP := [ [ 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ], 
  [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ], 
  [ 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ], 
  [ 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ] ];
