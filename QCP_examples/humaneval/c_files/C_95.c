/*
Given a map, return true if all keys are strings in lower 
case || all keys are strings in upper case, else return false.
The function should return false is the given map is empty.
Examples:
check_map_case({{"a","apple"}, {"b","banana"}}) should return true.
check_map_case({{"a","apple"}, {"A","banana"}, {"B","banana"}}) should return false.
check_map_case({{"a","apple"}, {"8","banana"}, {"a","apple"}}) should return false.
check_map_case({{"Name","John"}, {"Age","36"}, {"City","Houston"}}) should return false.
check_map_case({{"STATE","NC"}, {"ZIP","12345"} }) should return true.
*/
#include<stdio.h>
#include<string.h>
#include<stdbool.h>
bool check_dict_case(const char** keys, int dict_size){
    int islower=0,isupper=0;
    if (dict_size==0) return false;
    for (int k=0;k<dict_size;k++)
    {
        const char* key=keys[k];
    
        for (int i=0;key[i]!='\0';i++)
        {
            if (key[i]<65 || (key[i]>90 && key[i]<97) || key[i]>122) return false;
            if (key[i]>=65 && key[i]<=90) isupper=1;
            if (key[i]>=97 && key[i]<=122) islower=1;
            if (isupper+islower==2) return false;
        }

    }
    return true;
}

