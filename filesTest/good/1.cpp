int main () {
  int ret =0;
  ret = printInt(fact(7)) ;
  ret = printInt(factr(7)) ;
  ret = printString("testS");
  return fact(7) ;
}

// iteracyjnie
int fact (int n) {
  int i=0 ;
  int r=0;
  i = 1 ;
  r = 1 ;
  while (i < n+1) {
    r = r * i ;
    i = 1+i ;
  }
  return r ;
}

// rekurencyjnie
int factr (int n) {
  if (n < 2){
    return 1 ;
  }
  else{
    return (n * factr(n-1)) ;
  }
}