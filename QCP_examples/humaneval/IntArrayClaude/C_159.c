/*
You"re a hungry rabbit, && you already have eaten a certain number of carrots,
but now you need to eat more carrots to complete the day's meals.
you should return a vector of { total number of eaten carrots after your meals,
                                the number of carrots left after your meals }
if there are ! enough remaining carrots, you will eat all remaining carrots, but will still be hungry.

Example:
* eat(5, 6, 10) -> {11, 4}
* eat(4, 8, 9) -> {12, 1}
* eat(1, 10, 10) -> {11, 0}
* eat(2, 11, 5) -> {7, 0}

Variables:
@number : integer
    the number of carrots that you have eaten.
@need : integer
    the number of carrots that you need to eat.
@remaining : integer
    the number of remaining carrots thet exist in stock

Constrain:
* 0 <= number <= 1000
* 0 <= need <= 1000
* 0 <= remaining <= 1000

Have fun :)
*/
#include<stdio.h>
#include<stdlib.h>

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray eat(int number,int need,int remaining){
    IntArray out;
    out.data = (int*)malloc(2 * sizeof(int));
    out.size = 2;
    if (out.data == NULL) {
        out.size = 0;
        return out;
    }
    if (need>remaining) {
        out.data[0] = number + remaining;
        out.data[1] = 0;
        return out;
    }
    out.data[0] = number + need;
    out.data[1] = remaining - need;
    return out;
}

