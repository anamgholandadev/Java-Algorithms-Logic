package com.thealgorithms.strings;

public class CharactersSame {
    /**
     * check if all the characters of a string are same
     *
     * @param s the string to check
     * @return {@code true} if all characters of a string are same, otherwise
     * {@code false}
     */
    
    //@ requires s.length() <= Integer.MAX_VALUE;
    //@ ensures ((\forall int x; 0 <= x < s.length(); s.charAt(x) == s.charAt(0) ) <==> \result);
    public static boolean isAllCharactersSame(String s) {

        //@ maintaining (1 <= i <= s.length()) || (i==1 && s.length() == 0);
        //@ maintaining (\forall int k; 0 <= k < i; s.charAt(k) == s.charAt(0));
        //@ decreases length - i;
        for (int i = 1, length = s.length(); i < length; ++i) {
            if (s.charAt(i) != s.charAt(0)) {
                return false;
            }
        }
        return true;
    }
}
