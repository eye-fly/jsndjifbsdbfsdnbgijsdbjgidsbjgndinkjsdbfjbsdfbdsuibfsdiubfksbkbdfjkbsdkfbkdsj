int main () {
    return test(101, "example"+" string", false || true);
}

int tst = 1;

int test (int n, string str, boolean bl) {

    n = printInt(n);
    n=printString(str);
    if(bl){
        n=printString("false");
    } else{
        n=printString("true");
    }
}
