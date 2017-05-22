// sea_inc  tbd1.c ;;  example9 is feasible
// sea_inc --single tbd1.c ;;  example9 is infeasible

int getInt(int n){
    return 0;
}

int example9(int index, int ints_size, int chars_size, int bytes_size, int booleans_size) {
    int max = 0;
    if (booleans_size > 0 && index < 63)
        max = 64;
    else if (bytes_size > 0 && index < 56)
        max = 57;
    else if (chars_size > 0 && index < 48)
        max = 49;
    else if (ints_size > 0 && index < 32)
        max = 33;

    if (max != 0) {
        int rand = getInt(9);
        max = max - index;
        //at this point, max must be 1 because
        //if max!=0, then one of the cases above
        //was taken s.t. max is always set to index+1
        // hence the line above always sets index to 1
        if (max > rand)
            max = rand;
        else if (max != 1)
            max = getInt(max); // unreachable
        index+=max;
    }
    return index;
}
