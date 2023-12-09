package com.thealgorithms.maths;


public class Average {

    /**
     * find average value of an int array
     *
     * @param numbers the array contains element and the sum does not excess long
     *                value limit
     * @return average value
     */

    //@ requires numbers != null && numbers.length < Integer.MAX_VALUE;
    //@ signals (IllegalArgumentException e) numbers == null || numbers.length == 0;
    //@ ensures \result >= 0 && \result <= Integer.MAX_VALUE;
    public static int average(int[] numbers) {
        if (numbers == null || numbers.length == 0) {
            throw new IllegalArgumentException("Numbers array cannot be empty or null");
        }
        long sum = 0;
        for (int number : numbers) {
            sum += number;
        }
        return (int) (sum / numbers.length);
    }
}
