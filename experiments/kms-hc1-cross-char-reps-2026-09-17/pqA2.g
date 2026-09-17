run:=function(p, maxc)
  local F,a,b,c,cm,rels,G,epi,Q,r,s,cl;
  F:=FreeGroup("a","b","c");; a:=F.1;; b:=F.2;; c:=F.3;;
  cm:=function(x,y) return x^-1*y^-1*x*y; end;;
  rels:=[a^p,b^p,c^p,cm(cm(a,b),a),cm(cm(a,b),b),cm(cm(b,c),b),cm(cm(b,c),c),cm(cm(a,c),a),cm(cm(a,c),c)];;
  G:=F/rels;;
  r:=cm(G.2,G.1);; s:=cm(G.2,G.3);;
  for cl in [1..maxc] do
    epi:=EpimorphismPGroup(G,p,cl);; Q:=Image(epi);;
    Print("A2 p=",p," class<=",cl," |Q|=p^",LogInt(Size(Q),p)," ord[r,s]=",Order(Image(epi,cm(r,s)))," ord w=",Order(Image(epi,(r*s)^p)),"\n");
  od;
end;;
run(3,7);
run(5,10);
QUIT;
