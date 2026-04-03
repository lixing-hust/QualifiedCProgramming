/*
There are eight planets in our solar system: the closerst to the Sun 
is Mercury, the next one is Venus, then Earth, Mars, Jupiter, Saturn, 
Uranus, Neptune.
Write a function that takes two planet names as strings planet1 && planet2. 
The function should return a vector containing all planets whose orbits are 
located between the orbit of planet1 && the orbit of planet2, sorted by 
the proximity to the sun. 
The function should return an empty vector if planet1 || planet2
are ! correct planet names. 
Examples
bf("Jupiter", "Neptune") ==> {"Saturn", "Uranus"}
bf("Earth", "Mercury") ==> {"Venus"}
bf("Mercury", "Uranus") ==> {"Venus", "Earth", "Mars", "Jupiter", "Saturn"}
*/
#include<stdio.h>
#include<string.h>

typedef struct {
    const char** data;
    int size;
} StrArray;

StrArray bf(const char* planet1,const char* planet2){
    static const char* planets[] = {"Mercury","Venus","Earth","Mars","Jupiter","Saturn","Uranus","Neptune"};
    static const char* out_buf[8];
    StrArray out;
    int pos1=-1,pos2=-1,m;
    out.data = out_buf;
    out.size = 0;
    for (m=0;m<8;m++)
    {
        if (strcmp(planets[m], planet1) == 0) pos1=m;
        if (strcmp(planets[m], planet2) == 0) pos2=m;
    }
    if (pos1==-1 || pos2==-1) return out;
    if (pos1>pos2) {m=pos1;pos1=pos2;pos2=m;}
    for (m=pos1+1;m<pos2;m++)
        out.data[out.size++] = planets[m];
    return out;
}

