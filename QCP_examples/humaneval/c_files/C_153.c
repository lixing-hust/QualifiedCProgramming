/*
You will be given the name of a class (a string) && a vector of extensions.
The extensions are to be used to load additional classes to the class. The
strength of the extension is as follows: Let CAP be the number of the uppercase
letters in the extension's name, && let SM be the number of lowercase letters 
in the extension's name, the strength is given by the fraction CAP - SM. 
You should find the strongest extension && return a string in this 
format: ClassName.StrongestExtensionName.
If there are two || more extensions with the same strength, you should
choose the one that comes first in the vector.
For example, if you are given "Slices" as the class && a vector of the
extensions: {"SErviNGSliCes", "Cheese", "StuFfed"} then you should
return "Slices.SErviNGSliCes" since "SErviNGSliCes" is the strongest extension 
(its strength is -1).
Example:
for Strongest_Extension("my_class", {"AA", "Be", "CC"}) == "my_class.AA"
*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>
char* Strongest_Extension(const char* class_name, char** extensions, int extensions_size){
    const char* strongest="";
    int max=-1000;
    for (int i=0;i<extensions_size;i++)
    {
        int strength=0;
        for (int j=0;extensions[i][j]!='\0';j++)
        {
            char chr=extensions[i][j];
            if (chr>=65 && chr<=90) strength+=1;
            if (chr>=97 && chr<=122) strength-=1;
        }
        if (strength>max) 
        {
            max=strength;
            strongest=extensions[i];
        }
    }
    {
        int n1 = (int)strlen(class_name);
        int n2 = (int)strlen(strongest);
        char* out = (char*)malloc((size_t)n1 + n2 + 2);
        if (out == NULL) return NULL;
        memcpy(out, class_name, (size_t)n1);
        out[n1] = '.';
        memcpy(out + n1 + 1, strongest, (size_t)n2);
        out[n1 + n2 + 1] = '\0';
        return out;
    }
}

