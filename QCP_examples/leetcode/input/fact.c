
int fact(int n){
   for(int i = n-1; i > 0; i--){
       n *= i;
   }
   return n;
}