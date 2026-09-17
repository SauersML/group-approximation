# Deep p-quotients of Gamma^A2_p: test whether the degree-3p central class of the Serre Lie algebra
# (the HC_1 cocycle t^{p-1}dt, nontrivial exactly because p | p) is realised by the group and detects w_p.
run:=function(p, cl)
  local F,a,b,c,cm,rels,G,epi,Q,r,s,w,pc,k,t0;
  F:=FreeGroup("a","b","c");; a:=F.1;; b:=F.2;; c:=F.3;;
  cm:=function(x,y) return x^-1*y^-1*x*y; end;;
  rels:=[a^p,b^p,c^p,cm(cm(a,b),a),cm(cm(a,b),b),cm(cm(b,c),b),cm(cm(b,c),c),cm(cm(a,c),a),cm(cm(a,c),c)];;
  G:=F/rels;;
  r:=cm(G.2,G.1);; s:=cm(G.2,G.3);;
  t0:=Runtime();;
  epi:=EpimorphismPGroup(G,p,cl);; Q:=Image(epi);;
  pc:=PCentralSeries(Q,p);;
  Print("A2 p=",p," class<=",cl," |Q|=p^",LogInt(Size(Q),p)," time=",Runtime()-t0,"ms\n");
  Print("  increments: ",List([1..Length(pc)-1],i->LogInt(Index(pc[i],pc[i+1]),p)),"\n");
  w:=Image(epi,(r*s)^p);;
  Print("  ord w=",Order(w)," depth of w in p-central series: ",First([1..Length(pc)],i->not w in pc[i]),"\n");
end;;
run(5,15);
run(5,16);
QUIT;
