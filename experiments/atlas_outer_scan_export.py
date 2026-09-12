"""Emit a GAP program scanning the outer automorphism coset of A8."""

import itertools

import numpy as np

import atlas_two_chart_search as atlas


def gap_perm(g):
    vectors = [np.array(bits, dtype=np.uint8)
               for bits in itertools.product((0, 1), repeat=4) if any(bits)]
    index = {tuple(v.tolist()): i + 1 for i, v in enumerate(vectors)}
    images = []
    for v in vectors:
        image = (g @ v) & 1
        images.append(index[tuple(image.tolist())])
    return "PermList([%s])" % ",".join(map(str, images))


def gap_string(value):
    return '"' + value.replace("\\", "\\\\").replace('"', '\\"') + '"'


def main():
    names, words = atlas.relation_family()
    atlas.validate_relation_words(names, words)
    generators = [word[0][1] for _, word in atlas.factor_generators()[:6]]
    print("G:=Group([%s]);; A:=AlternatingGroup(8);;" %
          ",".join(gap_perm(g) for g in generators))
    print("iso:=IsomorphismGroups(G,A);; outer:=(1,2);;")
    print("names:=[%s];;" % ",".join(gap_string(name) for name in names))
    encoded_words = []
    for word in words:
        tokens = []
        for factor, g in word:
            tokens.append("[%d,Image(iso,%s)]" % (factor, gap_perm(g)))
        encoded_words.append("[%s]" % ",".join(tokens))
    print("rels:=[%s];;" % ",".join(encoded_words))
    print(r"""
EvalWord:=function(w,h)
  local value,token,image;
  value:=One(A);
  for token in w do
    image:=token[2];
    if token[1]=2 then image:=(image^outer)^h; fi;
    value:=value*image;
  od;
  return value;
end;;
hist:=List([0..Length(rels)],i->0);; best:=-1;; winners:=[];;
for h in Elements(A) do
  count:=Number(rels,r->EvalWord(r,h)=One(A));
  hist[count+1]:=hist[count+1]+1;
  if count>best then best:=count; winners:=[h];
  elif count=best then Add(winners,h); fi;
od;
Print("alignments ",Size(A)," relations ",Length(rels),
      " best_exact ",best," best_count ",Length(winners),"\n");
Print("histogram ",Filtered([0..Length(rels)],i->hist[i+1]<>0),"\n");
Print("histogram_counts ",Filtered(hist,x->x<>0),"\n");
for h in winners{[1..Minimum(Length(winners),8)]} do
  failed:=Filtered([1..Length(rels)],i->EvalWord(rels[i],h)<>One(A));
  Print("winner ",h," failed ",List(failed,i->names[i]),"\n");
od;
QUIT;
""")


if __name__ == "__main__":
    main()
