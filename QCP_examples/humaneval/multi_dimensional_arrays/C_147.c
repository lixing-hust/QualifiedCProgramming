/*
You are given a positive integer n. You have to create an integer vector a of length n.
    For each i (1 ≤ i ≤ n), the value of a{i} = i * i - i + 1.
    Return the number of triples (a{i}, a{j}, a{k}) of a where i < j < k, 
&& a[i] + a[j] + a[k] is a multiple of 3.

Example :
    Input: n = 5
    Output: 1
    Explanation: 
    a = {1, 3, 7, 13, 21}
    The only valid triple is (1, 7, 13).
*/
#include<stdio.h>
int get_matrix_triples(int n){
    int a[1005];
    int sum[1005][3];
    int sum2[1005][3];

    for (int i = 0; i <= n; ++i) {
        for (int j = 0; j < 3; ++j) {
            sum[i][j] = 0;
            sum2[i][j] = 0;
        }
    }

    for (int i=1;i<=n;i++)
    {
        a[i] = (i*i-i+1)%3;
        for (int j = 0; j < 3; ++j) sum[i][j] = sum[i-1][j];
        sum[i][a[i]] += 1;
    }

    for (int times=1;times<3;times++)
    {
        for (int i=1;i<=n;i++)
        {
            for (int j = 0; j < 3; ++j) sum2[i][j] = sum2[i-1][j];
            for (int j=0;j<=2;j++)
                sum2[i][(a[i]+j)%3] += sum[i-1][j];
        }
        for (int i = 0; i <= n; ++i)
            for (int j = 0; j < 3; ++j)
                sum[i][j] = sum2[i][j];
        for (int i = 0; i <= n; ++i)
            for (int j = 0; j < 3; ++j)
                sum2[i][j] = 0;
    }

    return sum[n][0];
}

