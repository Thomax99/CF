#include "permutations.h"

void initPerm(int *P, unsigned int n)
{   
    int i=n;
    /*@
        loop invariant 0 <= i <=n;
        loop invariant \forall integer k; 0<=k<n-i ==> P[k]==k;
        
        loop assigns P[0..n-1],i;
        loop variant i;
    */
    while(i>0){
        P[n-i] = n-i;
        i--;
    }
    return;
}

bool isMaxPerm(int *P, unsigned int n)
{   
    if (n==0){
        return true;
    }
    int i=1;
    /*@
        loop invariant 0 < i <=n;
        loop invariant \forall integer k; 0<k<i ==> P[k]<P[k-1];       
        loop assigns i;
        loop variant n-i;
    */
    while(i<n){
        if(P[i]>= P[i-1]){
            return false;
        }
        i++;
    }
    return true;
}