#include "formalism.h"
#include "limits.h"

/*@
    requires n > 0;
    requires \valid(&P[0..n-1]);
    requires isPermutation(\at(P, Pre), n);
    ensures isPermutation(\at(P, Post), n) ;

    behavior maxPerm:
        assumes isMaxPerm{Pre}(P, n);
        ensures \result == false;
        ensures unchangedTab{Pre,Post}(P, P, 0, n)  ;

    behavior notMaxPerm:
        assumes !isMaxPerm{Pre}(P, n);
        ensures \result == true;
        ensures isStrictlyBiggerPerm{Pre,Post}(P, P, n) ;

    assigns P[0..n-1];

    complete behaviors;
    disjoint behaviors maxPerm,notMaxPerm;

*/
bool NextPermutation(int *P, unsigned int n);