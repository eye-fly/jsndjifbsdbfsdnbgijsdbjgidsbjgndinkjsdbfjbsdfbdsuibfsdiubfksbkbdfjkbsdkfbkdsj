int main(){
    int n=0;
    boolean bl = true; 
    if( !(bl|| (false && true)) ){
        n=printString("true");
    } else{
        n=printString("false");
    }
}
