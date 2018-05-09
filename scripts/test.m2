R = QQ[x,y,z];
use frac R;
n = (x*x -1)/(x + 1);
<< toExternalString (numerator(n)) << "\n"
<< toExternalString (denominator(n)) << "\n"