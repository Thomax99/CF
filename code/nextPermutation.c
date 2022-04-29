#include "nextPermutation.h"
#include "reverse.h"
#include "swap-xor.h"


bool NextPermutation(int *P, unsigned int n)
{
    unsigned int i = n - 1, j;

    /* étape 1: cherche i le plus grand tq P[i]<P[i+1] */
    j = n - 1;
    /*@
        loop invariant \forall integer i ; j<=i<n-1 ==> P[i] > P[i+1] ;
        loop invariant n > j >= 0;
        loop assigns j;
        loop variant j;
    */
    while (j > 0 && P[j - 1] >= P[j])
    {
        j--;
    }
    //@ assert j == 0 || P[j-1] < P[j];
    /* on a trouvé un i tq P[i]<P[i+1] */
    if (j == 0)
    {
        return false; /* le plus grand i tq P[i]<[i+1] n'existe pas */
    }
    //@ assert P[j-1] < P[j];
    //@ assert j < n;
    i = j - 1;
    //@ assert i < n-1;
    //@ assert P[i] < P[i+1];

    /* étape 2: cherche j le plus grand tq P[i]<P[j] */
    /*@
        loop invariant i < j <= n ;
        loop invariant \forall integer k ; i<k<j ==> P[i] < P[k] ;
        loop assigns j;
        loop variant n-j;
    */
    while ((j < n) && (P[i] < P[j]))
        j++;
    //@ assert i < n-1;
    //@ assert j == n || P[i] >= P[j] ;
    j-- ;
    //@ assert i != j || P[i] >= P[j+1];
    //@ assert i != j ;
    //@ assert isPermutation(P,n);
    swap(P + i, P + j);
    //@ assert \forall integer k; 0 <= k < n ==> 0 <= P[k] < n ;
    //@ assert \forall integer k,l; 0 <= k < l < n ==> P[k] != P[l];
    //@ assert \forall integer k; 0 <= k < n ==> 0 <= P[k] < n && \forall integer k,l; 0 <= k < l < n ==> P[k] != P[l];
    //@ assert isPermutation(P,n);
    reverse(P, i + 1, n - 1, n);
    //@ assert unchangedTab{Pre,Here}(P,P,0,i);
    //@ assert \forall integer k; k ==j ==> P[i] == \at(P[k], Pre) ;
    //@ assert \forall integer k; i+1<=k<n && k != j ==> P[n-1-k+i+1] == \at(P[k], Pre);
    //@ assert \forall integer k; 0 <= k < n ==> 0 <= P[k] < n ;
    //@ assert \forall integer k,l; 0 <= k < l < n ==> P[k] != P[l];
    //@ assert isPermutation(P,n);
    //@ assert P[i] > \at(P[\at(i,Here)],Pre);
    return true;
}