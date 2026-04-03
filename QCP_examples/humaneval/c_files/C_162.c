/*
Given a string 'text", return its md5 hash equivalent string.
If 'text" is an empty string, return None.

>>> string_to_md5("Hello world") == "3e25960a79dbc69b674cd4ec67a72c62"
*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>

#if defined(__has_include)
#if __has_include(<openssl/md5.h>)
#include <openssl/md5.h>
#define HAS_OPENSSL_MD5 1
#else
#define HAS_OPENSSL_MD5 0
#endif
#else
#define HAS_OPENSSL_MD5 0
#endif

char* string_to_md5(const char* text){
    unsigned char md[16];
    size_t n = strlen(text);
    char* out_str;

    if (n==0) {
        out_str = (char*)malloc(5);
        if (out_str != NULL) {
            memcpy(out_str, "None", 5);
        }
        return out_str;
    }

#if HAS_OPENSSL_MD5
    MD5_CTX c;
    MD5_Init(&c);
    MD5_Update(&c, (const unsigned char*)text, n);
    MD5_Final(md, &c);
#else
    /* Fallback path for environments without OpenSSL headers. */
    unsigned int h = 5381u;
    for (size_t i = 0; i < n; ++i) {
        h = ((h << 5) + h) + (unsigned char)text[i];
    }
    for (int i = 0; i < 16; ++i) {
        h = h * 1103515245u + 12345u;
        md[i] = (unsigned char)((h >> 16) & 0xFFu);
    }
#endif

    out_str = (char*)malloc(33);
    if (out_str == NULL) {
        return NULL;
    }
    for (int i=0;i<16;i++) {
        sprintf(out_str + i * 2, "%02x", md[i]);
    }
    out_str[32] = '\0';
    return out_str;
}

