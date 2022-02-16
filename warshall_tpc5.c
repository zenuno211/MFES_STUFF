#define MAXVERTICES 10
typedef int Graph[MAXVERTICES][MAXVERTICES];

/*@ requires n>0 &&
@       \valid(A+(0..(n*n-1))) &&
@       \valid(R+(0..(n*n-1))) &&
@       \separated(A+(0..n*n-1), R+(0..n*n-1)) ;
@ assigns R[0..n-1][0..n-1];
@*/

void WarshallTC (Graph A, Graph R, int n) {
    int i, j, k;
    /*@ loop invariant 0 <= i <= n &&
    @       (\forall integer a, b; 0 <= a < i && 0 <= b < n ==> R[a][b] == A[a][b]);
    @ loop assigns i, j, R[0..n-1][0..n-1];
    @ loop variant n - i;
    */
    for (i=0 ; i<n ; i++)
        /*@ loop invariant 0 <= j <= n &&
        @   (\forall integer b; 0 <= b < j ==> R[i][b] == A[i][b]);
        @ loop assigns j, R[i][0..n-1];
        @ loop variant n - j;
        */
        for (j=0 ; j<n ; j++)
            R[i][j] = A[i][j];

    
    /*@ loop invariant 0 <= k <= n &&
    @       (\forall integer a, b, c;
    @           0 <= a < k && 0 <= b < n && 0 <= c < n ==>
    @               R[b][a] && R[a][c] ==> R[b][c] == 1);
    @ loop assigns k, i, j, R[0..n-1][0..n-1];
    @ loop variant n - k;
    */
    for (k=0 ; k<n; k++)
        /*@ loop invariant 0 <= i <= n &&
        @       (\forall integer a, b, c;
        @           0 <= a < k && 0 <= b < i && 0 <= c < n ==>
        @               R[b][a] && R[a][c] ==> R[b][c] == 1);
        @ loop assigns i, j, R[0..n-1][0..n-1];
        @ loop variant n - i ;
        @*/
        for (i=0 ; i<n ; i++)
            /*@ loop invariant 0 <= j <= n &&
            @       (\forall integer a, b, c;
            @           0 <= a < k && 0 <= b < i && 0 <= c < j ==>
            @               R[b][a] && R[a][c] ==> R[b][c] == 1);
            @ loop assigns j, R[i][0..n-1];
            @ loop variant n - j ;
            @*/
            for (j=0 ; j<n ; j++)
                if (R[i][k] && R[k][j])
                    R[i][j] = 1;
}