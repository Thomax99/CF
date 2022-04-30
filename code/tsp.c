#include "tsp.h"

int tsp(unsigned int n, int *P)
{
    initPerm(P, n);
    int val = value(P, n);
    //@ assert isPermutation(P, n) ;
    //@ assert \forall integer i; 0 <= i < n ==> 0 <= P[i] < n ;
    //@ assert \forall integer i,j; 0 <= i < j < n ==> P[i] != P[j];
    //@ assert \forall int* t; \separated(t+(0..n-1),P+(0..n-1)) ==>  isPermutation(t,n) ==> isBiggerPerm{Here,Here}(t,P,n) ==> unchangedTab{Here,Here}(t,P,0,n);
    /*@

        loop invariant \forall int* t; \separated(t+(0..n-1),P+(0..n-1)) ==> unchangedTab{Here,Here}(t,t,0,n);
        loop invariant \forall int* t; \separated(t+(0..n-1),P+(0..n-1)) ==> isBiggerPerm{Here,Here}(t,P,n) ==> isBiggerPerm{Here,Here}(t,P,n);
        loop invariant \forall int* t; \separated(t+(0..n-1),P+(0..n-1)) ==> isPermutation(t,n) ==> isBiggerPerm{Here,Here}(t,P,n) ==> value(t,n) >= val;
        loop invariant isPermutation(P, n);
        loop invariant \forall int* t; \separated(t+(0..n-1),P+(0..n-1)) ==> isPermutation(t,n) ==> isMaxPerm{Here}(t,n) ==> isBiggerPerm{Here, Here}(P, t, n) ;
        loop invariant \forall int* t; \separated(t+(0..n-1),P+(0..n-1)) ==> isPermutation(t,n) ==> isMinPerm{Here}(t,n) ==> isBiggerPerm{Here, Here}(t, P, n) ;
        loop assigns val, P[0..n];
    */
    while (!(isMaxPerm(P, n)))
    {
    L:
        //@ assert isPermutation(P, n);
        NextPermutation(P, n);
        //@ assert isPermutation(P, n);

        //@ assert \forall int* t; \separated(t+(0..n-1),P+(0..n-1)) ==> unchangedTab{L,Here}(t,t,0,n);
        //@ assert !isMaxPerm{L}(P, n) ==> isStrictlyBiggerPerm{L,Here}(P,P,n) ;
        //@ assert isMaxPerm{L}(P, n) ==> unchangedTab{L,Here}(P,P,0,n) ;
        //@ assert isBiggerPerm{L,Here}(P,P,n) ;
        //@ assert \forall int* t; \separated(t+(0..n-1),P+(0..n-1)) ==> isBiggerPerm{L,Here}(t,P,n) ==> isBiggerPerm{L,L}(t,P,n);
        //@ assert \forall int* t; \separated(t+(0..n-1),P+(0..n-1)) ==> isPermutation(t,n) ==> isBiggerPerm{Here,L}(t,P,n) ==> value(t,n) >= val;
        if (val > value(P, n))
            val = value(P, n);
    }
    return val;
}