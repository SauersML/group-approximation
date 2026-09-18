run:=function(p, maxc)
  local F,a,b,c,cm,rels,G,epi,Q,w,cl,img;
  F:=FreeGroup("a","b","c");; a:=F.1;; b:=F.2;; c:=F.3;;
  cm:=function(x,y) return x^-1*y^-1*x*y; end;;
  rels:=[a^p,b^p,c^p,cm(cm(a,b),a),cm(cm(a,b),b),cm(cm(b,c),b),cm(cm(b,c),c),cm(cm(a,c),a),cm(cm(cm(a,c),c),a),cm(cm(cm(a,c),c),c)];;
  G:=F/rels;;
  w:=(cm(G.2,G.1)*cm(G.2,G.3))^p;;
  for cl in [1..maxc] do
    epi:=EpimorphismPGroup(G,p,cl);;
    Q:=Image(epi);;
    img:=Image(epi,w);;
    Print("p=",p," class<=",cl," |Q|=p^",LogInt(Size(Q),p)," nilclass=",NilpotencyClassOfGroup(Q)," w order ",Order(img),"\n");
    if Order(img)>1 then return; fi;
  od;
end;;
run(3,12);
run(5,12);
QUIT;
