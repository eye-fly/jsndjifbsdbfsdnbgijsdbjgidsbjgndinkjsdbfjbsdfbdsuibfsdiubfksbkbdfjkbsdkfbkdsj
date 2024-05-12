
int glob =0;

int main () {
  int ret =0;
  glob = 2;
  ret = printInt(glob) ;
  int glob =3;
  ret = printInt(glob) ;

  ret = f();
  return ret;
}


// rekurencyjnie
int f () {
  return printInt(glob) ;
}
