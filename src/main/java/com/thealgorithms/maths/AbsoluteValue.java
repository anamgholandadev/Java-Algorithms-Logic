package com.thealgorithms.maths;

public class AbsoluteValue {

    /**
     * Returns the absolute value of a number.
     *
     * @param number The number to be transformed
     * @return The absolute value of the {@code number}
     */
    //@ requires Integer.MIN_VALUE < number && number < Integer.MAX_VALUE;
    //@ ensures (\result == number) || (\result == -number);
    public static int getAbsValue(int number) {
        return number < 0 ? -number : number;
    }
}
