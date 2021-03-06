var C1;
var C2;
var g1;
var g2;
var s1;
var s2;

subject to

cons1:  s1^2+g1^2 - 1 = 0;
cons2:  s2^2+g2^2 - 1 = 0;
cons3:  C1*g1^3+C2*g2^3 - 1.2 = 0;
cons4:  C1*s1^3+C2*s2^3 - 1.2 = 0;
cons5:  C1*g1^2*s1+C2*g2^2*s2 - 0.7 = 0;
cons6:  C1*g1*s1^2+C2*g2*s2^2 - 0.7 = 0;

#solve;
#display C1, C2, g1, g2, s1, s2;

# TITLE : neurofysiology, posted by Sjirk Boon

# ROOT COUNTS :

# total degree : 1024
# 3-homogeneous Bezout number : 344
#   with partition : {s1 s2 }{g1 g2 }{C1 C2 }
# generalized Bezout number : 216
#   based on the set structure :
#      {s1 g1 }{s1 g1 }
#      {s2 g2 }{s2 g2 }
#      {g1 g2 }{g1 g2 }{g1 g2 }{C1 C2 }
#      {s1 s2 }{s1 s2 }{s1 s2 }{C1 C2 }
#      {s1 s2 }{g1 g2 }{g1 g2 }{C1 C2 }
#      {s1 s2 }{s1 s2 }{g1 g2 }{C1 C2 }
# mixed volume : 20

# NOTE :

# There are only 8 finite solutions for general values of
# the constant terms.
# It can be proved that it is equivalent to a quadrature formula
# problem, so that there is only one solution upon symmetry.

# REFERENCES :

# The system has been posted to the newsgroup
# sci.math.num-analysis by Sjirk Boon.

# P. Van Hentenryck, D. McAllester and D. Kapur:
# `Solving Polynomial Systems Using a Branch and Prune Approach'
# SIAM J. Numerical Analysis, Vol. 34, No. 2, pp 797-827, 1997.

# SYMMETRY GROUP :

#  g2 s2 g1 s1 C2 C1
#  g1 s1 g2 s2 C1 C2
#  s2 g2 s1 g1 C2 C1
#  s1 g1 s2 g2 C1 C2

#  -s1 s2 -g1 g2 -C1 C2
#  s1 -s2 g1 -g2 C1 -C2

# THE GENERATING SOLUTIONS :

# 1 6
# ===========================================================
# solution 1 :
# t :  1.00000000000000E+00   0.00000000000000E+00
# m : 8
# the solution for t :
#  s1 : -4.02451939639181E-01  -6.67657107123736E-67
#  g1 : -9.15441115681758E-01   3.52374584315305E-67
#  s2 :  9.15441115681758E-01   4.26558707329054E-67
#  g2 :  4.02451939639181E-01  -7.41841230137484E-67
#  C1 : -1.44169513021472E+00  -1.24258406048029E-66
#  C2 :  1.44169513021472E+00  -1.07566978369935E-66
# == err :  3.255E-15 = rco :  1.566E-02 = res :  2.220E-16 ==
