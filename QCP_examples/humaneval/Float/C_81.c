/*
It is the last week of the semester && the teacher has to give the grades
to students. The teacher has been making her own algorithm for grading.
The only problem is, she has lost the code she used for grading.
She has given you a vector of GPAs for some students && you have to write 
a function that can output a vector of letter grades using the following table:
         GPA       |    Letter grade
          4.0                A+
        > 3.7                A 
        > 3.3                A- 
        > 3.0                B+
        > 2.7                B 
        > 2.3                B-
        > 2.0                C+
        > 1.7                C
        > 1.3                C-
        > 1.0                D+ 
        > 0.7                D 
        > 0.0                D-
          0.0                E


Example:
grade_equation({4.0, 3, 1.7, 2, 3.5}) ==> {"A+", "B", "C-", "C", "A-"}
*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>

typedef struct {
  const char** data;
  int size;
} StrArray;

StrArray numerical_letter_grade(const float* grades, int grades_size){
  StrArray out;
  out.size = grades_size;
  out.data = (const char**)malloc((size_t)grades_size * sizeof(const char*));
  if (out.data == NULL) {
    out.size = 0;
    return out;
  }
    for (int i=0;i<grades_size;i++)
    {
    if (grades[i]>=3.9999) out.data[i] = "A+";
    else if (grades[i]>3.7001) out.data[i] = "A";
    else if (grades[i]>3.3001) out.data[i] = "A-";
    else if (grades[i]>3.0001) out.data[i] = "B+";
    else if (grades[i]>2.7001) out.data[i] = "B";
    else if (grades[i]>2.3001) out.data[i] = "B-";
    else if (grades[i]>2.0001) out.data[i] = "C+";
    else if (grades[i]>1.7001) out.data[i] = "C";
    else if (grades[i]>1.3001) out.data[i] = "C-";
    else if (grades[i]>1.0001) out.data[i] = "D+";
    else if (grades[i]>0.7001) out.data[i] = "D";
    else if (grades[i]>0.0001) out.data[i] = "D-";
    else out.data[i] = "E";
    }
    return out;
}

