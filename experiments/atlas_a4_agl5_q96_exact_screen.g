# Exact AGL(5,2) screen for extending the fixed affine Q96 triangle through
# F'=S3xS3, J=S4, and the double-attached C144 vertex.

field := GF(2);;

AffineMatrix := function(rows,translation)
  local value,row,column;
  value:=NullMat(6,6,field);
  for row in [1..5] do
    for column in [1..5] do
      if QuoInt(rows[row],2^(column-1)) mod 2=1 then
        value[row][column]:=One(field);
      fi;
    od;
    if QuoInt(translation,2^(row-1)) mod 2=1 then
      value[row][6]:=One(field);
    fi;
  od;
  value[6][6]:=One(field);
  return value;
end;;

identityRows:=[1,2,4,8,16];;
ambientGenerators:=[];;
for row in [1..5] do
  Add(ambientGenerators,AffineMatrix(identityRows,2^(row-1)));
  for column in [1..5] do
    if row<>column then
      rows:=ShallowCopy(identityRows);;
      rows[row]:=rows[row]+2^(column-1);
      Add(ambientGenerators,AffineMatrix(rows,0));
    fi;
  od;
od;
ambient:=Group(ambientGenerators);;
if Size(ambient)<>319979520 then Error("ambient is not AGL(5,2)"); fi;

# Fixed affine Q96 certificate, in generator order t,c,u.
t:=AffineMatrix([2,3,8,12,16],0);;
c:=AffineMatrix([1,2,4,8,18],8);;
u:=AffineMatrix([1,2,4,8,21],24);;
if Size(Group([c,u,t]))<>96 then Error("fixed Q96 calibration failed"); fi;

rCandidates:=Filtered(Elements(Centralizer(ambient,c)),r->
  Order(r)=3 and u*r*u=r^-1);;
zCandidates:=Filtered(Elements(Centralizer(ambient,u)),z->
  Order(z)=3 and c*z*c=z^-1);;

normalizerT:=Normalizer(ambient,Group([t]));;
sCandidates:=[];;
for s in Elements(normalizerT) do
  if Order(s)=2 and s*t*s=t^-1 then
    q:=t*c*s*c*t^-1*c*s*t*c;
    if IsOne(q) and Size(Group([t,s,c]))=24 then
      Add(sCandidates,s);
    fi;
  fi;
od;

Print("ambient_order=",Size(ambient),
      " r_candidates=",Length(rCandidates),
      " z_candidates=",Length(zCandidates),
      " s_candidates=",Length(sCandidates),"\n");

survivors:=0;;
for r in rCandidates do
  for z in zCandidates do
    if r*z=z*r and Size(Group([r,z,c,u]))=36 then
      for s in sCandidates do
        b:=s*t;
        if IsOne((r^-1*b)^3) and IsOne((z*b)^3)
           and Size(Group([r,z,b]))=144 then
          survivors:=survivors+1;
          Print("SURVIVOR r=",r," z=",z," s=",s,
                " ambient_image_order=",Size(Group([r,z,c,u,t,s])),"\n");
        fi;
      od;
    fi;
  od;
od;
Print("survivors=",survivors,"\n");
QUIT;
