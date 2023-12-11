package com.thealgorithms.maths;

public final class FindMin {
    private FindMin() {
    }

    /**
     * @brief finds the minimum value stored in the input array
     *
     * @param array the input array
     * @exception IllegalArgumentException input array is empty
     * @return the mimum value stored in the input array
     */
    
    //@   public normal_behavior
    //@     requires 0 < array.length <= Integer.MAX_VALUE;
    //@     ensures \forall int k; 0 <= k < array.length; \result <= array[k];
    //@ also
    //@   public exceptional_behavior
    //@     requires array.length == 0;
    //@     signals_only IllegalArgumentException;
    public static int findMin(final int[] array) {
        if (array.length == 0) {
            throw new IllegalArgumentException("Array must be non-empty.");
        }
        int min = array[0];
        //@ assert min == array[0];

        //@ maintaining 1 <= i <= array.length;
        //@ loop_writes min;
        //@ maintaining \forall int k; 0 <= k < i; min <= array[k];
        for (int i = 1; i < array.length; i++) {
            if (array[i] < min) {
                min = array[i];
            }
        }
        return min;
    }
}
