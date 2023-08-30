#!/usr/bin/bash

sed -i 's/(/BIGTIMELPAREN/g' $1
sed -i 's/)/BIGTIMERPAREN/g' $1
comby -timeout 5 -in-place -rule 'where match :[stuff] { | ":[_~AgdaUnsolvedMeta]" -> true | ":[_]" -> false  }, rewrite :[stuff] {"%" -> ""}' -matcher .tex '\begin{code}:[stuff]\end{code}' '\begin{code}:[stuff]\end{code}' $1
comby -timeout 5 -in-place -matcher .tex '\AgdaUnsolvedConstraint{:[one]}' ':[one]' $1
for N in 1 2 3 4 5 6 7 8 9 10; do
  comby -timeout 5 -in-place -matcher .tex '\AgdaUnsolvedMeta{:[one]}\AgdaSpace{}' '\AgdaUnsolvedMeta{:[one]\AgdaSpace{}}' $1
  # comby -timeout 5 -in-place -matcher .tex '\AgdaUnsolvedMeta{:[one]}\>[:[num]]' '\AgdaUnsolvedMeta{:[one]\>[:[num]]}' $1
  comby -timeout 5 -in-place -matcher .tex '\AgdaUnsolvedMeta{:[one]}\AgdaUnsolvedMeta{:[two]}' '\AgdaUnsolvedMeta{:[one]:[two]}' $1
done
sed -i 's/BIGTIMELPAREN/(/g' $1
sed -i 's/BIGTIMERPAREN/)/g' $1

