/*
You are given a non-empty vector of positive integers. Return the greatest integer that is greater than 
zero, && has a frequency greater than || equal to the value of the integer itself. 
The frequency of an integer is the number of times it appears in the vector.
If no such a value exist, return -1.
Examples:
    search({4, 1, 2, 2, 3, 1}) == 2
    search({1, 2, 2, 3, 3, 3, 4, 4, 4}) == 3
    search({5, 5, 4, 4, 4}) == -1
*/
#include<stdio.h>
#include<stdlib.h>
#include<stdbool.h>
int search(int* lst, int lst_size){
    int* vals;
    int* cnts;
    int freq_size = 0;
    int max=-1;

    vals = (int*)malloc((size_t)lst_size * sizeof(int));
    cnts = (int*)malloc((size_t)lst_size * sizeof(int));
    if (vals == NULL || cnts == NULL) {
        free(vals);
        free(cnts);
        return -1;
    }

    for (int i=0;i<lst_size;i++)
    {
        bool has=false;
        for (int j=0;j<freq_size;j++)
            if (lst[i]==vals[j])
            {
                cnts[j]+=1;
                has=true;
                if (cnts[j]>=vals[j] && vals[j]>max) max=vals[j];
            }
        if (!has)
        {
            vals[freq_size]=lst[i];
            cnts[freq_size]=1;
            freq_size += 1;
            if (max==-1 && lst[i]==1) max=1;
        }
    }
    free(vals);
    free(cnts);
    return max;
}

