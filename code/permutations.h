#include "formalism.h"
#include "limits.h"

/*@
    requires n< INT_MAX;
    requires \valid (P+(0..n));
    terminates \true;
    ensures isPermutation(P,n);
    ensures isMinPerm(P,n);
*/
void initPerm(int *P, unsigned int n);

/*@
    requires n< INT_MAX;
    requires \valid (P+(0..n));
    terminates \true;
    ensures isMaxPerm(P,n) ==> \result == true;
    ensures !isMaxPerm(P,n) ==> \result == false;
*/
bool isMaxPerm(int *P, unsigned int n);