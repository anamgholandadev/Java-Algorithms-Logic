package com.thealgorithms.bitmanipulation;

/**
 * Is number power of 2
 * @author Bama Charan Chhandogi (https://github.com/BamaCharanChhandogi)
 */

public class IsPowerTwo {

    //@ requires Integer.MIN_VALUE < number && number <= Integer.MAX_VALUE;
    //@ ensures \result == (number > 0 && ((number - 1) | number) == (2 * number - 1));
    public static boolean isPowerTwo(int number) {
        if (number <= 0) {
            return false;
        }
        int ans = number & (number - 1);
        return ans == 0;
    }
}
