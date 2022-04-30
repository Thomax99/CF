#include "tsp.h"

int tsp(unsigned int n, int *P)
{
    initPerm(P, n);
    int val = value(P, n);
    //@ assert \forall int* t; \separated(t+(0..n-1),P+(0..n-1)) ==>  isPermutation(t,n) ==> isBiggerPerm{Here,Here}(t,P,n) ==> unchangedTab{Here,Here}(t,P,0,n);
    /*@

        loop invariant \forall int* t; \separated(t+(0..n-1),P+(0..n-1)) ==> unchangedTab{Pre,Here}(t,t,0,n);
        loop invariant \forall int* t; \separated(t+(0..n-1),P+(0..n-1)) ==> isBiggerPerm{Pre,Pre}(t,P,n) ==> isBiggerPerm{Pre,Here}(t,P,n);
        loop invariant \forall int* t; \separated(t+(0..n-1),P+(0..n-1)) ==> isPermutation(t,n) ==> isBiggerPerm{Pre,Here}(t,P,n) ==> value(t,n) >= val;
        loop invariant isPermutation(P, n);
        loop invariant isBiggerPerm{Pre, Here}(P, P, n) ;
        loop invariant \forall int* t; \separated(t+(0..n-1),P+(0..n-1)) ==> isPermutation(t,n) ==> isMaxPerm{Here}(t,n) ==> isBiggerPerm{Here, Here}(P, t, n) ;
        loop invariant \forall int* t; \separated(t+(0..n-1),P+(0..n-1)) ==> isPermutation(t,n) ==> isMinPerm{Here}(t,n) ==> isBiggerPerm{Here, Here}(t, P, n) ;
        loop assigns val, P[0..n];
    */
    while (!(isMaxPerm(P, n)))
    {
    L:
        NextPermutation(P, n);

        //@ assert isBiggerPerm{Here,L}(P,P,n)

        //@ assert \forall int* t; \separated(t+(0..n-1),P+(0..n-1)) ==> unchangedTab{L,Here}(t,t,0,n);
        //@ assert \forall int* t; \separated(t+(0..n-1),P+(0..n-1)) ==> isBiggerPerm{Here,L}(t,P,n) ==> isBiggerPerm{L,L}(t,P,n);
        //@ assert \forall int* t; \separated(t+(0..n-1),P+(0..n-1)) ==> isPermutation(t,n) ==> isBiggerPerm{Here,L}(t,P,n) ==> value(t,n) >= val;
        if (val > value(P, n))
            val = value(P, n);
    }
    return val;
}