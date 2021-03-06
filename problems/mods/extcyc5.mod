var a;
var b;
var c;
var d;
var e;
var i;

subject to

cons1:  a + b + c + d + e - 1 = 0;
cons2:  a*b + b*c + c*d + d*e + e*a - 0.30901699437495 - 0.95105651629515*i = 0;
cons3:  a*b*c + b*c*d + c*d*e + d*e*a + e*a*b + 0.80901699437495 + 0.58778525229247*i = 0;
cons4:  a*b*c*d + b*c*d*e + c*d*e*a + d*e*a*b + e*a*b*c 
               - 0.30901699437495 - 0.95105651629515*i = 0;
cons5:  a*b*c*d*e - 1 = 0;

#solve;
#display a, b, c, d, e, i;

# TITLE : extended cyclic 5-roots problem, to exploit the symmetry

# ROOT COUNTS :

# total degree : 120
# 5-homogeneous Bezout number : 120
#   with partition : {a }{b }{c }{d }{e }
# generalized Bezout number : 106
#   based on the set structure :
#      {a b c d e }
#      {a c e }{b d e }
#      {a d }{b d e }{c e }
#      {a e }{b e }{c e }{d e }
#      {a }{b }{c }{d }{e }
# mixed volume : 70 = 14*5 = 7*10

# REFERENCES :

# Jan Verschelde and Karin Gatermann:
# `Symmetric Newton Polytopes for Solving Sparse Polynomial Systems',
# Adv. Appl. Math., 16(1): 95-127, 1995.

# G\"oran Bj\"orck and Ralf Fr\"oberg:
# `A faster way to count the solutions of inhomogeneous systems
#  of algebraic equations, with applications to cyclic n-roots',
# J. Symbolic Computation (1991) 12, pp 329--336.

# NOTE : EXPLOITATION OF SYMMETRY AND CHOICE OF CONSTANTS :

# By extending the equations of the original system with a
# random complex constant, we add a fixed point to the symmetry.

# The two generating elements of the symmetry group are

#   b c d e a
#   e d c b a

# which are respectively the cyclic permutation and the reading
# backwards operation.

# The fifth root of unity w :
#    w   =  0.30901699437495 + 0.95105651629515i
#    w^2 = -0.80901699437495 + 0.58778525229247i
#    w^3 = -0.80901699437495 - 0.58778525229247i
#    w^4 =  0.30901699437495 - 0.95105651629515i
#    w^5 =  1.0
# Note however that :
#     1 + w + w^2 + w^3 + w^4 = -1.110223024625157e-16 + 3.330669073875470e-16i.

# When (w,w^2,w^3,w^4,1) is the vector of the right hand sides, then
# (w,w,w,w,w) is a solution of all subsystems of a certain type.
# Therefore, (1,w,w^3,w,1) seems to be a better choice.

# THE GENERATING SOLUTIONS :

# 7 5
# ===========================================================
# solution 1 :
# t :  1.00000000000000E+00   0.00000000000000E+00
# m : 10
# the solution for t :
#  a :  3.51566035447901E-02  -8.27261453800970E-01
#  b :  1.01623041236047E+00  -1.24241632490855E+00
#  c : -9.20411830092637E-02   2.16579860363359E+00
#  d : -2.10069650118794E-01   4.96678926154659E-01
#  e :  2.50723817222800E-01  -5.92799751078729E-01
# == err :  3.507E-15 = rco :  7.423E-02 = res :  4.003E-16 ==
# solution 2 :
# t :  1.00000000000000E+00   0.00000000000000E+00
# m : 10
# the solution for t :
#  a :  1.16341787215603E+00   3.24099681249188E-01
#  b :  1.54792244147177E+00  -1.33407662151979E-01
#  c : -1.84748735988833E+00   1.59225658169080E-01
#  d : -4.44386084044522E-01  -1.23795062494183E-01
#  e :  5.80533130305057E-01  -2.26122614772107E-01
# == err :  4.843E-15 = rco :  7.975E-02 = res :  4.475E-16 ==
# solution 3 :
# t :  1.00000000000000E+00   0.00000000000000E+00
# m : 10
# the solution for t :
#  a :  4.10014793736554E-01   7.50751897540148E-01
#  b :  1.60100166102993E-01   7.35198384573590E-01
#  c : -4.08340693440269E-01  -2.85192410929864E+00
#  d : -6.11528218468393E-02  -2.80820794433095E-01
#  e :  8.99378555447562E-01   1.64679462161799E+00
# == err :  5.729E-15 = rco :  3.872E-02 = res :  8.006E-16 ==
# solution 4 :
# t :  1.00000000000000E+00   0.00000000000000E+00
# m : 10
# the solution for t :
#  a : -8.09016994374948E-01   5.87785252292474E-01
#  b : -5.37688913226986E-01   8.43143304897086E-01
#  c :  3.11581670732691E+00  -1.47039386691358E+00
#  d :  1.98921146442162E-01  -2.11361625033512E-01
#  e : -9.68031946167142E-01   2.50826934757527E-01
# == err :  5.436E-15 = rco :  4.732E-02 = res :  9.930E-16 ==
# solution 5 :
# t :  1.00000000000000E+00   0.00000000000000E+00
# m : 10
# the solution for t :
#  a : -8.02615012782033E-01  -8.49949264705670E-01
#  b : -3.65901573839422E-01  -3.87480633537469E-01
#  c :  3.00459112225004E+00   1.75469990030919E+00
#  d :  3.11577150774741E-01   1.52965719796006E-01
#  e : -1.14765168640332E+00  -6.70235721862056E-01
# == err :  3.466E-15 = rco :  4.368E-02 = res :  8.473E-16 ==
# solution 6 :
# t :  1.00000000000000E+00   0.00000000000000E+00
# m : 10
# the solution for t :
#  a :  8.91931221365206E-01  -4.52171091904345E-01
#  b : -4.86191902445739E-01  -5.68082696200543E-01
#  c :  6.97615506804102E-01   1.14101698421537E+00
#  d :  7.05662168651377E-01  -7.08548448402957E-01
#  e : -8.09016994374947E-01   5.87785252292474E-01
# == err :  2.209E-15 = rco :  1.096E-01 = res :  7.109E-16 ==
# solution 7 :
# t :  1.00000000000000E+00   0.00000000000000E+00
# m : 10
# the solution for t :
#  a : -8.09016994374947E-01   5.87785252292475E-01
#  b : -3.64715822016015E-01  -9.31118880257073E-01
#  c :  2.05677941924575E-02  -6.95027127677804E-01
#  d :  1.38032173080495E+00   4.03763838735321E-01
#  e :  7.72843291393555E-01   6.34596916907081E-01
# == err :  9.805E-16 = rco :  2.227E-01 = res :  5.579E-16 ==
