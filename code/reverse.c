#include "reverse.h"

/*@ decreases j;
*/
void reverse(int *t, unsigned int i, unsigned int j, unsigned int n) {
    if (i < j) {
        int aux = t[i];
        t[i] = t[j];
        t[j] = aux;
        i++ ;
        j-- ;
        if (i<j)
            reverse(t, i, j, n) ;
    }
}

void reverseP(int *t, unsigned int i, unsigned int j, unsigned int n)
{
    /*@ loop invariant 0<=\at(i, Pre)<=i<=j+1<=\at(j, Pre)+1<=n;
        loop invariant \forall integer k; i<=k<=j ==> t[k] == \at(t[k], Pre) ;
        loop invariant i == \at(j, Pre) -j  + \at(i, Pre) ;
        loop invariant \forall integer k; (\at(i, Pre)<=k<i) ==> t[k] == \at(t[j- k + i], Pre);
        loop invariant \forall integer k; j<k<=\at(j, Pre) ==> t[k] == \at(t[j- k + i], Pre);
        loop assigns i,j,t[\at(i,Pre)..\at(j,Pre)] ;
        loop variant j-i+1;
    */
    while (i < j)
    {
        int aux = t[i];
        t[i] = t[j];
        t[j] = aux;
        i++;
        j--;
    }
}