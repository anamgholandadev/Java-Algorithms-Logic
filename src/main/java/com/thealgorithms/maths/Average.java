package com.thealgorithms.maths;


public class Average {
 /**
     * Calculate average of a list of numbers
     *
     * @param numbers array to store numbers
     * @return mean of given numbers
     */
    public static double average(double[] numbers) {
        if (numbers == null || numbers.length == 0) {
            throw new IllegalArgumentException("Numbers array cannot be empty or null");
        }
        double sum = 0;
        for (double number : numbers) {
            sum += number;
        }
        return sum / numbers.length;
    }

    /**
     * find average value of an int array
     *
     * @param numbers the array contains element and the sum does not excess long
     *                value limit
     * @return average value
     */
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
    public static int average1(int[] numbers) {
        if (numbers == null || numbers.length == 0) {
            throw new IllegalArgumentException("Numbers array cannot be empty or null");
        }
        long sum = 0;
        int i;

        for (i = 0; i < numbers.length; i++) {
            sum = sum + numbers[i]; 
        }
        int result = (int) (sum / numbers.length);
        return result;
    }
}
