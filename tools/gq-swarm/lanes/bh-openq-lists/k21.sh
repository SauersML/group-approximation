cd /projects/standard/hsiehph/sauer354/openq-lists/ksrc
tr '\n' ' ' < 21tkt.tex | LC_ALL=C sed 's/  */ /g; s/\\bmp /\n/g' | LC_ALL=C grep -E '^\\textbf\{(\\zv )?21\.[0-9]+' | LC_ALL=C grep -i -E 'simple|thompson|boone|higman|finitely presented|word problem|embed|residually finite' | cut -c1-420
