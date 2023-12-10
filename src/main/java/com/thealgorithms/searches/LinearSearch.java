package com.thealgorithms.searches;

// import com.thealgorithms.devutils.searches.SearchAlgorithm;
// import java.util.Random;
// import java.util.stream.Stream;

import com.thealgorithms.devutils.searches.SearchAlgorithm;

/**
 * Linear search is the easiest search algorithm It works with sorted and
 * unsorted arrays (an binary search works only with sorted array) This
 * algorithm just compares all elements of an array to find a value
 *
 * <p>
 * Worst-case performance O(n) Best-case performance O(1) Average performance
 * O(n) Worst-case space complexity
 *
 * @author Varun Upadhyay (https://github.com/varunu28)
 * @author Podshivalov Nikita (https://github.com/nikitap492)
 * @see BinarySearch
 * @see SearchAlgorithm
 */
public class LinearSearch implements SearchAlgorithm {

    /**
     * Generic Linear search method
     *
     * @param array List to be searched
     * @param value Key being searched for
     * @return Location of the key
     */
    
    // specification inherited;
    @Override
    public <T extends Comparable<T>> int find(/*@ non_null @*/ T /*@ non_null @*/[] array, /*@ non_null @*/ T value) {

        //@ loop_writes \nothing;
        //@ maintaining 0 <= i <= array.length;
        //@ maintaining (\forall int k; 0 <= k < i; array[k].compareTo(value) != 0);
        //@ decreases array.length - i;
        for (int i = 0; i < array.length; i++) {
            //@ assert \typeof(value) <: \typeof(array[i]);
            if (array[i].compareTo(value) == 0) {
                //@ assert array[i].compareTo(value) == 0;
                return i;
            }
        }
        return -1;
    }
}