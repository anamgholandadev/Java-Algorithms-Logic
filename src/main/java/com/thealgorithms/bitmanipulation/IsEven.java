package com.thealgorithms.bitmanipulation;

/**
 * Checks whether a number is even
 * @author Bama Charan Chhandogi (https://github.com/BamaCharanChhandogi)
 */

public class IsEven {
    //@ requires Integer.MIN_VALUE <= number && number <= Integer.MAX_VALUE;
    //@ ensures \result == ((number % 2) == 0);
    public static boolean isEven(int number) {
        return (number & 1) == 0;
    }
}
