/*
Input to this function is a string representing musical notes in a special ASCII format.
Your task is to parse this string && return vector of integers corresponding to how many beats does each
! last.

Here is a legend:
"o" - whole note, lasts four beats
"o|" - half note, lasts two beats
".|" - quater note, lasts one beat

>>> parse_music("o o| .| o| o| .| .| .| .| o o")
{4, 2, 1, 2, 2, 1, 1, 1, 1, 4, 4}
*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray parse_music(const char* music_string){
    IntArray out;
    int cap = 8;
    char cur[4];
    int clen = 0;
    int n = (int)strlen(music_string);
    out.size = 0;
    out.data = (int*)malloc((size_t)cap * sizeof(int));
    if (out.data == NULL) return out;
    for (int i=0;i<=n;i++)
    {
        char ch = (i < n) ? music_string[i] : ' ';
        if (ch==' ')
        {
            cur[clen] = '\0';
            if (strcmp(cur,"o")==0 || strcmp(cur,"o|")==0 || strcmp(cur,".|")==0) {
                int v = (strcmp(cur,"o")==0) ? 4 : (strcmp(cur,"o|")==0 ? 2 : 1);
                if (out.size == cap) {
                    int new_cap = cap * 2;
                    int* tmp = (int*)realloc(out.data, (size_t)new_cap * sizeof(int));
                    if (tmp == NULL) return out;
                    out.data = tmp;
                    cap = new_cap;
                }
                out.data[out.size++] = v;
            }
            clen = 0;
        }
        else if (clen < 3) cur[clen++] = ch;
    }
    return out;
}

