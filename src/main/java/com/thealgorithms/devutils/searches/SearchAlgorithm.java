package com.thealgorithms.devutils.searches;

/**
 * The common interface of most searching algorithms
 *
 * @author Podshivalov Nikita (https://github.com/nikitap492)
 */
public interface SearchAlgorithm {
    /**
     * @param key is an element which should be found
     * @param array is an array where the element should be found
     * @param <T> Comparable type
     * @return first found index of the element
     */
    // outra linha de raciocínio para a especificação
    // @ requires array.length <= Integer.MAX_VALUE;
    // @ requires (\forall int x; 0 <= x < array.length; \typeof(value) <: \typeof(array[x]));
    // @ requires !(\forall int x; 0 <= x < array.length; array[x].compareTo(value) != 0);
    // @ ensures \result >= 0 && array[\result].compareTo(value) == 0;
    // @ also
    // @ requires array.length <= Integer.MAX_VALUE;
    // @ requires (\forall int x; 0 <= x < array.length; \typeof(value) <: \typeof(array[x]));
    // @ requires (\forall int x; 0 <=x < array.length; array[x].compareTo(value) != 0);
    // @ ensures \result == -1;

    //@ requires array.length <= Integer.MAX_VALUE;
    //@ requires (\forall int x; 0 <= x < array.length; \typeof(key) <: \typeof(array[x]));
    //@ ensures (!(\forall int x; 0 <= x < array.length; array[x].compareTo(key) != 0)) ==> array[\result].compareTo(key) == 0;
    //@ ensures (\forall int x; 0 <=x < array.length; array[x].compareTo(key) != 0) ==> \result == -1;
    //@ pure
    <T extends Comparable<T>> int find(T[] array, T key);
}
