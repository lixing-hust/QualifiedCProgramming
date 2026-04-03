#include<stdio.h>
#include<stdlib.h>
#include<string.h>
char* encode_cyclic(const char* s){ 
    // returns encoded string by cycling groups of three characters.  
    // split string to groups. Each of length 3.
    size_t l=strlen(s);
    char* output = (char*)malloc(l + 1);
    if (output == NULL) return NULL;
    for (size_t i=0;i*3<l;i++) {
        size_t b = i * 3;
        size_t rem = l - b;
        if (rem >= 3) {
            output[b] = s[b + 1];
            output[b + 1] = s[b + 2];
            output[b + 2] = s[b];
        } else {
            for (size_t k = 0; k < rem; k++) output[b + k] = s[b + k];
        }
    }
    output[l] = '\0';
    return output;
}


char* decode_cyclic(const char* s){ 
    /*
    takes as input string encoded with encode_cyclic function. Returns decoded string. 
    */
    size_t l=strlen(s);
    char* output = (char*)malloc(l + 1);
    if (output == NULL) return NULL;
    for (size_t i=0;i*3<l;i++) {
        size_t b = i * 3;
        size_t rem = l - b;
        if (rem >= 3) {
            output[b] = s[b + 2];
            output[b + 1] = s[b];
            output[b + 2] = s[b + 1];
        } else {
            for (size_t k = 0; k < rem; k++) output[b + k] = s[b + k];
        }
    }
    output[l] = '\0';
    return output;


}

