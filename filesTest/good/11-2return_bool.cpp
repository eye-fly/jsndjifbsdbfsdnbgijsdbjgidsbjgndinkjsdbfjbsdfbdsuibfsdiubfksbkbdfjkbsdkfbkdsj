int main(){
    int n=0;
    if(tst () ){
        n=printString("true");
    } else{
        n=printString("false");
    }
}

boolean tst(){
    return true && false;
}