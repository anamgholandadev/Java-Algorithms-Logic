package com.thealgorithms.strings;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

/**
 * Vowel Count is a system whereby character strings are placed in order based
 * on the position of the characters in the conventional ordering of an
 * alphabet. Wikipedia: https://en.wikipedia.org/wiki/Alphabetical_order
 */
public class CheckVowels {

    //@ public invariant VOWELS != null;
    // @ public invariant (\forall char c; VOWELS.contains(c) <==> (c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'));
    //@ spec_public
    private static final Set<Character> VOWELS = new HashSet<>(Arrays.asList('a', 'e', 'i', 'o', 'u'));

    /**
     * Check if a string is has vowels or not
     *
     * @param input a string
     * @return {@code true} if given string has vowels, otherwise {@code false}
     */
    //@ requires input.length() < Integer.MAX_VALUE - 1;
    //@ requires input != null;
    //@ ensures (!(\forall int x; 0 <= x < input.length(); !VOWELS.contains(Character.toLowerCase(input.charAt(x))) ) <==> \result);
    //@ also
    //@ requires input == null;
    //@ ensures \result == false;
    public static boolean hasVowels(String input) {
        if (input == null) {
            return false;
        }
        input = input.toLowerCase();

        //@ maintaining 0 <= i <= input.length();
        //@ loop_writes \nothing;
        //@ maintaining (\forall int k; 0 <= k < i; !(VOWELS.contains(input.charAt(k))) );
        //@ decreases input.length() - i;
        for (int i = 0; i < input.length(); i++) {
            if (VOWELS.contains(input.charAt(i))) {
                return true;
            }
        }
        return false;
    }
}