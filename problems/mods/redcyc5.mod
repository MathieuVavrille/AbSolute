var y1;
var y2;
var y3;
var y4;

subject to

cons1:  1 + y1 + y2 + y3 + y4 = 0;
cons2:  y1 + y1*y2 + y2*y3 + y3*y4 + y4 = 0;
cons3:  y1*y2 + y1*y2*y3 + y2*y3*y4 + y3*y4 + y4*y1 = 0;
cons4:  y1*y2*y3 + y1*y2*y3*y4 + y2*y3*y4 + y3*y4*y1 + y4*y1*y2 = 0;

#solve;
#display y1, y2, y3, y4;

#  z0**5*y1*y2*y3*y4  - 1;

# TITLE : reduced cyclic 5-roots problem

# ROOT COUNTS :

# total degree : 4! = 24
# multi-homogeneous Bezout bound : 24
# generalized Bezout bound : 20
#  based on
#   { y1 y2 y3 y4 }
#   { y1 y3 }{ y2 y4 }
#   { y1 }{ y2 }{ y3 }{ y4 }
#   { y1 }{ y2 }{ y3 }{ y4 }

# mixed volume : 14

# REFERENCES :

# See Ioannis Z. Emiris:
# `Sparse Elimination and Application in Kinematics'
# PhD Thesis, Computer Science, University of California at Berkeley, 1994,
# page 25.

# yi = zi/z0
# This reduced the dimension of the problem by 1 and the mixed volume
# drops with 5.

# For the original problem,
# see G\"oran Bj\"orck and Ralf Fr\"oberg:
# `A faster way to count the solutions of inhomogeneous systems
#  of algebraic equations, with applications to cyclic n-roots',
# in J. Symbolic Computation (1991) 12, pp 329--336.

# THE SYMMETRY GROUP :

# y1 y2 y3 y4
# y4 y3 y2 y1

# THE GENERATING SOLUTIONS :

# 7 4
# ===========================================================
# solution 1 :
# t :  1.00000000000000E+00   0.00000000000000E+00
# m : 2
# the solution for t :
#  y1 :  1.00000000000000E+00   6.36727435230003E-73
#  y2 : -3.81966011250105E-01   2.47616224811668E-73
#  y3 : -2.61803398874990E+00  -5.65979942426670E-73
#  y4 :  1.00000000000000E+00  -1.06121239205001E-73
# == err :  4.785E-15 = rco :  7.860E-02 = res :  2.145E-72 ==
# solution 2 :
# t :  1.00000000000000E+00   0.00000000000000E+00
# m : 2
# the solution for t :
#  y1 :  3.09016994374947E-01  -9.51056516295154E-01
#  y2 : -8.09016994374947E-01  -5.87785252292473E-01
#  y3 : -8.09016994374948E-01   5.87785252292473E-01
#  y4 :  3.09016994374947E-01   9.51056516295154E-01
# == err :  7.337E-16 = rco :  1.617E-01 = res :  2.483E-16 ==
# solution 3 :
# t :  1.00000000000000E+00   0.00000000000000E+00
# m : 2
# the solution for t :
#  y1 :  1.00000000000000E+00   3.70920615068742E-68
#  y2 :  1.00000000000000E+00   4.82196799589365E-67
#  y3 : -2.61803398874989E+00   1.48368246027497E-67
#  y4 : -3.81966011250105E-01  -1.03857772219248E-66
# == err :  4.655E-15 = rco :  4.742E-02 = res :  4.441E-16 ==
# solution 4 :
# t :  1.00000000000000E+00   0.00000000000000E+00
# m : 2
# the solution for t :
#  y1 : -3.81966011250105E-01   2.84867032372794E-65
#  y2 : -3.81966011250105E-01   5.19288861096239E-66
#  y3 : -3.81966011250105E-01   0.00000000000000E+00
#  y4 :  1.45898033750316E-01  -3.32344871101593E-65
# == err :  4.869E-16 = rco :  3.777E-02 = res :  5.551E-17 ==
# solution 5 :
# t :  1.00000000000000E+00   0.00000000000000E+00
# m : 2
# the solution for t :
#  y1 :  1.00000000000000E+00   7.07474928033337E-73
#  y2 :  1.00000000000000E+00  -4.52783953941336E-72
#  y3 : -3.81966011250105E-01  -3.53737464016669E-73
#  y4 : -2.61803398874989E+00   3.96185959698669E-72
# == err :  4.655E-15 = rco :  4.136E-02 = res :  4.441E-16 ==
# solution 6 :
# t :  1.00000000000000E+00   0.00000000000000E+00
# m : 2
# the solution for t :
#  y1 :  6.85410196624969E+00  -2.65993991496909E-75
#  y2 : -2.61803398874989E+00   3.45446742203778E-76
#  y3 : -2.61803398874990E+00   7.94527507068689E-76
#  y4 : -2.61803398874990E+00   1.41633164303549E-75
# == err :  5.029E-15 = rco :  1.653E-02 = res :  1.066E-14 ==
# solution 7 :
# t :  1.00000000000000E+00   0.00000000000000E+00
# m : 2
# the solution for t :
#  y1 : -8.09016994374947E-01   5.87785252292473E-01
#  y2 :  3.09016994374947E-01  -9.51056516295154E-01
#  y3 :  3.09016994374947E-01   9.51056516295154E-01
#  y4 : -8.09016994374947E-01  -5.87785252292473E-01
# == err :  7.252E-16 = rco :  1.925E-01 = res :  5.551E-16 ==
