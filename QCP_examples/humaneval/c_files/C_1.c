/*
Input to this function is a string containing multiple groups of nested parentheses. Your goal is to
separate those group into separate strings && return the vector of those.
Separate groups are balanced (each open brace is properly closed) && ! nested within each other
Ignore any spaces in the input string.
>>> separate_paren_groups("( ) (( )) (( )( ))")
{"()", "(())", "(()())"}
*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>

typedef struct {
    char** data;
    int size;
} StringArray;

StringArray separate_paren_groups(const char* paren_string){
    StringArray out;
    char* current;
    int level;
    int cur_len;
    int cur_cap;
    int out_cap;
    size_t i;

    out.data = NULL;
    out.size = 0;
    current = NULL;
    level = 0;
    cur_len = 0;
    cur_cap = 0;
    out_cap = 0;

    for (i = 0; paren_string[i] != '\0'; i++) {
        char chr = paren_string[i];
        if (chr != '(' && chr != ')') {
            continue;
        }

        if (cur_len + 2 > cur_cap) {
            int new_cap = cur_cap == 0 ? 16 : cur_cap * 2;
            char* tmp = (char*)realloc(current, (size_t)new_cap);
            if (tmp == NULL) {
                free(current);
                return out;
            }
            current = tmp;
            cur_cap = new_cap;
        }

        current[cur_len++] = chr;
        current[cur_len] = '\0';

        if (chr == '(') {
            level += 1;
        } else {
            level -= 1;
            if (level == 0) {
                if (out.size == out_cap) {
                    int new_cap = out_cap == 0 ? 4 : out_cap * 2;
                    char** tmp = (char**)realloc(out.data, (size_t)new_cap * sizeof(char*));
                    if (tmp == NULL) {
                        free(current);
                        return out;
                    }
                    out.data = tmp;
                    out_cap = new_cap;
                }
                out.data[out.size] = (char*)malloc((size_t)cur_len + 1);
                if (out.data[out.size] == NULL) {
                    free(current);
                    return out;
                }
                memcpy(out.data[out.size], current, (size_t)cur_len + 1);
                out.size += 1;
                cur_len = 0;
                if (current != NULL) {
                    current[0] = '\0';
                }
            }
        }
    }

    free(current);
    return out;
}

