var x1;
var x2;
var x3;

subject to

cons1: x1*x2^2 + x1*x3^2 - 1.1*x1 + 1 = 0;
cons2: x2*x1^2 + x2*x3^2 - 1.1*x2 + 1 = 0;
cons3: x3*x1^2 + x3*x2^2 - 1.1*x3 + 1 = 0;

#solve;
#display x1, x2, x3;

# TITLE : A neural network modeled by an adaptive Lotka-Volterra system, n=3

# ROOT COUNTS :

# total degree : 27

# generalized Bezout bound : 21
# set structure:
#   {x1} {x2 x3} {x2 x3}
#   {x2} {x1 x3} {x1 x3}
#   {x3} {x1 x2} {x1 x2}

# mixed volume : 21

# REFERENCES :

# Karin Gatermann:
# "Symbolic solution of polynomial equation systems with symmetry",
# Proceedings of ISSAC-90, pp 112-119, ACM New York, 1990.

# V. W. Noonburg:
# "A neural network modeled by an adaptive Lotka-Volterra system",
# SIAM J. Appl. Math., Vol. 49, No. 6, 1779-1792, 1989.

# Jan Verschelde and Ann Haegemans:
# `The GBQ-Algorithm for constructing start systems of homotopies for polynomial
# systems, SIAM J. Numer. Anal., Vol. 30, No. 2, pp 583-594, 1993.

# NOTE :

# The coefficients have been chosen so that full permutation symmetry
# was obtained.  The parameter c = 1.1.

# The orbits of solutions :  3 4 1
#   3*(a,a,a) 4*(a,a,b) and 1*(a,b,c) 

# THE GENERATING SOLUTIONS :

# 8 3
# ===========================================================
# solution 1 :
# t :  1.00000000000000E+00   0.00000000000000E+00
# m : 1
# the solution for t :
#  x1 :  5.09959548065397E-01   4.79766841277292E-01
#  x2 :  5.09959548065397E-01   4.79766841277292E-01
#  x3 :  5.09959548065397E-01   4.79766841277292E-01
# == err :  5.911E-16 = rco :  2.745E-01 = res :  2.493E-16 ==
# solution 2 :
# t :  1.00000000000000E+00   0.00000000000000E+00
# m : 1
# the solution for t :
#  x1 :  1.35560902253960E+00  -1.28703758201580E-17
#  x2 : -6.77804511269800E-01  -5.27500584353303E-01
#  x3 : -6.77804511269800E-01   5.27500584353303E-01
# == err :  7.955E-16 = rco :  2.529E-01 = res :  4.003E-16 ==
# solution 3 :
# t :  1.00000000000000E+00   0.00000000000000E+00
# m : 1
# the solution for t :
#  x1 : -4.44383120980212E-01  -3.01427302521399E-61
#  x2 : -1.29427788609688E+00   1.65298843318187E-61
#  x3 : -1.29427788609688E+00   1.65298843318187E-61
# == err :  2.849E-15 = rco :  2.583E-01 = res :  3.886E-16 ==
# solution 4 :
# t :  1.00000000000000E+00   0.00000000000000E+00
# m : 1
# the solution for t :
#  x1 :  8.98653694263692E-01   3.48820047576431E-01
#  x2 : -1.65123467890611E-01   7.61734168646636E-01
#  x3 :  8.98653694263692E-01   3.48820047576431E-01
# == err :  3.699E-16 = rco :  2.949E-01 = res :  1.665E-16 ==
# solution 5 :
# t :  1.00000000000000E+00   0.00000000000000E+00
# m : 1
# the solution for t :
#  x1 :  5.09959548065397E-01  -4.79766841277292E-01
#  x2 :  5.09959548065397E-01  -4.79766841277292E-01
#  x3 :  5.09959548065397E-01  -4.79766841277292E-01
# == err :  5.242E-16 = rco :  2.745E-01 = res :  5.662E-17 ==
# solution 6 :
# t :  1.00000000000000E+00   0.00000000000000E+00
# m : 1
# the solution for t :
#  x1 : -5.03029502430507E-01  -2.11770212163837E-55
#  x2 : -5.03029502430507E-01   1.95759134039956E-54
#  x3 :  1.68372096585234E+00  -1.95759134039956E-54
# == err :  1.716E-15 = rco :  3.764E-01 = res :  3.331E-16 ==
# solution 7 :
# t :  1.00000000000000E+00   0.00000000000000E+00
# m : 1
# the solution for t :
#  x1 : -1.65123467890611E-01  -7.61734168646636E-01
#  x2 :  8.98653694263692E-01  -3.48820047576431E-01
#  x3 :  8.98653694263692E-01  -3.48820047576431E-01
# == err :  3.702E-16 = rco :  2.761E-01 = res :  2.791E-16 ==
# solution 8 :
# t :  1.00000000000000E+00   0.00000000000000E+00
# m : 1
# the solution for t :
#  x1 : -1.01991909613079E+00  -9.49556774575980E-66
#  x2 : -1.01991909613079E+00  -7.59645419660784E-65
#  x3 : -1.01991909613079E+00  -4.74778387287990E-65
# == err :  3.234E-15 = rco :  2.070E-01 = res :  6.661E-16 ==
# <\PRE>
# <\HTML>
