
print(" TEST 1");

pp:=(x[1]^(2)-2)*(x[1]^(2)-3); 
qq := z^2 - 2;
R := PolynomialRing([z, x[1]]);

res := Trager_base(pp, x[1], qq, z, R):
Display(res, R);

##   [( z- x[1]) * (z -x[1]),    (x[1]^(2)-2) ]
##   [ z^2 - 2, (x[1]^(2)-3) ]



## Add verification

