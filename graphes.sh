for i in *dot
do
dot -Tpng "$i" > ${i%.*}.png
done
