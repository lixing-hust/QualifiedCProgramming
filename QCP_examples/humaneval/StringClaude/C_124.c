/*
You have to write a function which validates a given date string &&
returns true if the date is valid otherwise false.
The date is valid if all of the following rules are satisfied:
1. The date string is ! empty.
2. The number of days is ! less than 1 || higher than 31 days for months 1,3,5,7,8,10,12. And the number of days is ! less than 1 || higher than 30 days for months 4,6,9,11. And, the number of days is ! less than 1 || higher than 29 for the month 2.
3. The months should ! be less than 1 || higher than 12.
4. The date should be in the format: mm-dd-yyyy

for example: 
valid_date("03-11-2000") => true

valid_date("15-01-2012") => false

valid_date("04-0-2040") => false

valid_date("06-04-2020") => true

valid_date("06/04/2020") => false
*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>
#include<stdbool.h>
bool valid_date(const char* date){
    int mm,dd,yy,i;
    if (strlen(date)!=10) return false;
    for (int i=0;i<10;i++)
        if (i==2 || i==5)
        {
            if (date[i]!='-') return false;
        }
        else
            if (date[i]<48 || date[i]>57) return false;

    mm = (date[0]-'0')*10 + (date[1]-'0');
    dd = (date[3]-'0')*10 + (date[4]-'0');
    yy = (date[6]-'0')*1000 + (date[7]-'0')*100 + (date[8]-'0')*10 + (date[9]-'0');
    if (mm<1 || mm>12) return false;
    if (dd<1 || dd>31) return false;
    if (dd==31 && (mm==4 || mm==6 || mm==9 || mm==11 || mm==2)) return false;
    if (dd==30 && mm==2) return false;
    return true;

}

