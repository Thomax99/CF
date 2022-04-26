/*@ requires \separated(a, b);
    requires \valid (a) ;
    requires \valid(b) ;
    terminates \true;
    ensures *a == \old(*b);
    ensures *b == \old(*a);
    assigns *a, *b;
*/
void swap(int *a, int *b);