/*
Input to this function is a string represented multiple groups for nested parentheses separated by spaces.
For each of the group, output the deepest level of nesting of parentheses.
E.g. (()()) has maximum two levels of nesting while ((())) has three.

>>> parse_nested_parens("(()()) ((())) () ((())()())")
{2, 3, 1, 3}
*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray parse_nested_parens(const char* paren_string){
    IntArray all_levels;
    int cap = 8;
    int level=0,max_level=0;
    all_levels.size = 0;
    all_levels.data = (int*)malloc((size_t)cap * sizeof(int));
    if (all_levels.data == NULL) return all_levels;
    for (int i=0;paren_string[i]!='\0';i++)
    {
        char chr=paren_string[i];
        if (chr=='(')
        {
            level+=1;
            if (level>max_level) max_level=level;
        }
        if (chr==')')
        {
            level-=1;
            if (level==0){
                if (all_levels.size == cap) {
                    int new_cap = cap * 2;
                    int* tmp = (int*)realloc(all_levels.data, (size_t)new_cap * sizeof(int));
                    if (tmp == NULL) return all_levels;
                    all_levels.data = tmp;
                    cap = new_cap;
                }
                all_levels.data[all_levels.size++] = max_level;
                max_level=0;
            }
        }
    }
    return all_levels;
}

