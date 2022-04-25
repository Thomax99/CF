/*@ requires i <= j;
    requires 0<=i<n;
    requires -1<=j<n;
    requires \valid (&t[i..j]) ;

    terminates \true;
    ensures \forall integer k; i <= k <= j ==> t[k] == \old(t[j-k+i]);
    assigns t[i..j];
*/
void reverse(int *t, unsigned int i, unsigned int j, unsigned int n);