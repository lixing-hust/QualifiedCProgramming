/*
I think we all remember that feeling when the result of some long-awaited
event is finally known. The feelings && thoughts you have at that moment are
definitely worth noting down && comparing.
Your task is to determine if a person correctly guessed the results of a number of matches.
You are given two vectors of scores && guesses of equal length, where each index shows a match. 
Return a vector of the same length denoting how far off each guess was. If they have guessed correctly,
the value is 0, && if !, the value is the absolute difference between the guess && the score.


example:

compare({1,2,3,4,5,1},{1,2,3,4,2,-2}) -> {0,0,0,0,3,3}
compare({0,5,0,0,0,4},{4,1,1,0,0,-2}) -> {4,4,1,0,0,6}
*/
#include<stdio.h>
#include<math.h>
#include<stdlib.h>

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray compare(const int* game, int game_size, const int* guess, int guess_size){
    IntArray out;
    int n = game_size < guess_size ? game_size : guess_size;
    out.size = n;
    out.data = (int*)malloc((size_t)n * sizeof(int));
    if (out.data == NULL) {
        out.size = 0;
        return out;
    }
    for (int i=0;i<n;i++)
        out.data[i] = abs(game[i]-guess[i]);
    return out;
}

